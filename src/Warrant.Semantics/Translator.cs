using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>The entry point of translation (docs/m4/05).</summary>
public static class Translator
{
    /// <summary>
    /// Translates units into kernel declarations and theorem statements, without admitting anything (KTD22): the engine
    /// admits the declarations in order into a fork of <paramref name="bundle"/>, and each theorem through
    /// <see cref="TheoremShell.WithProof"/>.
    /// </summary>
    /// <param name="units">The units; every unit a unit depends on must be among them.</param>
    /// <param name="bundle">The checked semantics bundle, read only: for reducibility heights and name collisions.</param>
    /// <param name="displayNames">C# display names by unit key; the key is shown where one is missing.</param>
    /// <returns>The translation, units in dependency order.</returns>
    /// <exception cref="TranslationException">A unit cannot be translated, or two names collide.</exception>
    public static Translation Translate(IEnumerable<VirUnit> units, KernelEnvironment bundle, IReadOnlyDictionary<string, string>? displayNames = null)
    {
        ArgumentNullException.ThrowIfNull(units);
        ArgumentNullException.ThrowIfNull(bundle);
        var ordered = DependencyOrder(units.ToList());
        var types = new TypeTable(ordered);
        // M6 KTD11: the one effect inference decides which units translate into ClrM.
        var callees = new CalleeEffects(
            Effects.Analyze(ordered),
            ordered.Where(Effects.HasRequires).Select(u => u.Key).ToHashSet(StringComparer.Ordinal),
            ordered.ToDictionary(u => u.Key, StringComparer.Ordinal));
        var run = new Run(bundle);
        var result = new List<TranslatedUnit>();
        foreach (var unit in ordered)
        {
            try
            {
                result.Add(run.Unit(unit, types, callees, displayNames?.GetValueOrDefault(unit.Key) ?? LeanNames.FallbackDisplay(unit.Key)));
            }
            catch (TranslationException ex) when (ex.Key is null)
            {
                throw new TranslationException(unit.Key, ex.Message);
            }
        }
        return new Translation(result, run.DisplayNames);
    }

    /// <summary>
    /// Whether a unit is a recursive method, which translates to a well-founded definition (M5a KTD14): a function whose
    /// block body starts with <c>Spec.Decreases</c>.
    /// </summary>
    /// <param name="unit">The unit.</param>
    /// <returns>Whether it is recursive.</returns>
    public static bool IsRecursive(VirUnit unit)
    {
        ArgumentNullException.ThrowIfNull(unit);
        return BodyTranslator.IsRecursive(unit);
    }

    /// <summary>Every unit after the units it depends on, ties broken by key (ordinal), so the order is deterministic.</summary>
    private static List<VirUnit> DependencyOrder(List<VirUnit> units)
    {
        var byKey = new Dictionary<string, VirUnit>(StringComparer.Ordinal);
        foreach (var unit in units)
        {
            if (!byKey.TryAdd(unit.Key, unit))
            {
                throw new TranslationException(unit.Key, "the unit is given twice.");
            }
        }
        var waiting = new Dictionary<string, int>(StringComparer.Ordinal);
        var users = new Dictionary<string, List<string>>(StringComparer.Ordinal);
        var ready = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var unit in units)
        {
            var deps = unit.Deps.Where(d => !string.Equals(d, unit.Key, StringComparison.Ordinal)).ToList();
            foreach (var dep in deps)
            {
                if (!byKey.ContainsKey(dep))
                {
                    throw new TranslationException(unit.Key, $"it depends on {dep}, which is not being translated.");
                }
                (users.TryGetValue(dep, out var list) ? list : users[dep] = []).Add(unit.Key);
            }
            waiting[unit.Key] = deps.Count;
            if (deps.Count == 0)
            {
                ready.Add(unit.Key);
            }
        }
        var order = new List<VirUnit>();
        while (ready.Count > 0)
        {
            var key = ready.Min!;
            ready.Remove(key);
            order.Add(byKey[key]);
            foreach (var user in users.GetValueOrDefault(key) ?? [])
            {
                if (--waiting[user] == 0)
                {
                    ready.Add(user);
                }
            }
        }
        if (order.Count != units.Count)
        {
            var stuck = units.Select(u => u.Key).Where(k => waiting[k] > 0).Order(StringComparer.Ordinal).First();
            throw new TranslationException(stuck, "the units depend on each other in a cycle.");
        }
        return order;
    }

    /// <summary>The state of one translation: the names generated so far, their heights and display names.</summary>
    private sealed class Run(KernelEnvironment bundle)
    {
        private readonly Dictionary<Name, ReducibilityHints> _hints = [];

        public Dictionary<Name, string> DisplayNames { get; } = [];

        public TranslatedUnit Unit(VirUnit unit, TypeTable types, CalleeEffects callees, string display)
        {
            var name = LeanNames.ForKey(unit.Key);
            bool raising = callees.Analysis.IsRaising(unit.Key);
            if (unit.Dependencies is { Count: > 0 } && (unit.Kind != VirUnitKind.Function || !raising))
            {
                // A method that calls a dependency can raise (KTD11); one that lists a dependency it never calls would drop
                // the dependency's contract unread.
                throw new TranslationException(unit.Key, "it lists dependencies, but calls none of them.");
            }
            bool recursive = BodyTranslator.IsRecursive(unit) || callees.Analysis.IsRecursive(unit.Key);
            switch (unit.Kind)
            {
                case VirUnitKind.Function when raising && recursive:
                    // Extraction rejects this (KTD11): the recursive call would sit inside a bind, out of the decrease obligations' sight.
                    throw new TranslationException(unit.Key, "a recursive method that can raise an exception is not translated (recursion with effects).");
                case VirUnitKind.Function when recursive && HasContract(unit):
                    // Extraction rejects this (KTD11): the recursive call could not use the method's own unproved triple.
                    throw new TranslationException(unit.Key, "a recursive method with Spec.Requires or Spec.Ensures is not translated (contract on a recursive method).");
                case VirUnitKind.Function when raising:
                    {
                        // M6 KTD4, KTD11: a unit that can raise is a ClrM program over an opaque world, and KTD12: it has a
                        // contract obligation.
                        var (type, value) = new BodyTranslator(types, callees) { Contracted = true }.MonadicFunction(unit);
                        var decl = TypeDeclarations.Definition(name, type, value, Regular);
                        Declare(unit.Key, name, display, decl.Value.Hints);
                        var contract = Contract(unit, name, display, types, callees, raising: true);
                        if (contract is not null)
                        {
                            // The walker's view of the same program, its sites naming their VIR nodes (M6 KTD18).
                            contract.Program = new BodyTranslator(types, callees) { Contracted = true, TagSites = true }.MonadicFunction(unit).Value;
                        }
                        return new TranslatedUnit(unit.Key, unit.Kind, name, display, [decl], null) { Contract = contract };
                    }
                case VirUnitKind.Theorem when raising:
                    // Extraction rejects this (KTD11): a theorem is a Prop, and Lean's total operations would make a / 0 == 0 provable.
                    throw new TranslationException(unit.Key, "a theorem whose statement can raise an exception is not translated.");
                case VirUnitKind.Function when BodyTranslator.IsRecursive(unit):
                    {
                        // M5a KTD14, KTD15: the decrease theorems, the Nat.fix definition, then the equation lemma.
                        var (type, value, decreases, proof) = new BodyTranslator(types, callees).Recursive(unit);
                        var decl = TypeDeclarations.Definition(name, type, value, Regular);
                        Declare(unit.Key, name, display, decl.Value.Hints);
                        foreach (var decrease in decreases)
                        {
                            Declare(unit.Key, decrease.Theorem.Name, $"{display} (decrease {decrease.Index})", null);
                        }
                        var equationName = LeanNames.EquationLemma(unit.Key);
                        var equation = new TheoremShell(equationName, new BodyTranslator(types, callees).Equation(unit, name), null, null);
                        Declare(unit.Key, equationName, $"{display} (equation)", null);
                        return new TranslatedUnit(unit.Key, unit.Kind, name, display, [decl], null, new RecursiveDefinition(decreases, equation, proof));
                    }
                case VirUnitKind.Function:
                    {
                        var (type, value) = new BodyTranslator(types, callees) { Contracted = true }.Function(unit);
                        var decl = TypeDeclarations.Definition(name, type, value, Regular);
                        Declare(unit.Key, name, display, decl.Value.Hints);
                        // M6 KTD12: a pure unit has an obligation only when it has a contract; M4's and M5a's have none.
                        return new TranslatedUnit(unit.Key, unit.Kind, name, display, [decl], null) { Contract = Contract(unit, name, display, types, callees, raising: false) };
                    }
                case VirUnitKind.Theorem:
                    {
                        var (statement, claim, wellDefinedness) = new BodyTranslator(types, callees).TheoremStatement(unit);
                        foreach (var wd in wellDefinedness)
                        {
                            Declare(unit.Key, wd.Theorem.Name, $"{display} (well-definedness {wd.Index})", null);
                        }
                        Declare(unit.Key, name, display, null);
                        return new TranslatedUnit(unit.Key, unit.Kind, name, display, [], new TheoremShell(name, statement, unit.Script, unit.Budget, claim))
                        {
                            WellDefinedness = wellDefinedness,
                        };
                    }
                case VirUnitKind.Type:
                    {
                        var decls = TypeDeclarations.Translate(unit, types, Regular);
                        foreach (var decl in decls)
                        {
                            switch (decl)
                            {
                                case InductiveDecl ind:
                                    foreach (var t in ind.Types)
                                    {
                                        Declare(unit.Key, t.Name, display, null);
                                        Declare(unit.Key, LeanNames.Recursor(unit.Key), $"{display} (recursor)", null);
                                        foreach (var c in t.Constructors)
                                        {
                                            Declare(unit.Key, c.Name, Generated(display, c.Name), null);
                                        }
                                    }
                                    break;
                                case DefinitionDecl d:
                                    Declare(unit.Key, d.Value.Name, d.Value.Name == name ? display : Generated(display, d.Value.Name), d.Value.Hints);
                                    break;
                            }
                        }
                        return new TranslatedUnit(unit.Key, unit.Kind, name, display, decls, null);
                    }
                case VirUnitKind.Contract:
                    {
                        // M6 KTD10: a contract is never verified and admits nothing; each method that calls the member
                        // states it as a hypothesis (KTD9). Its own checks are KTD25's and KTD26's.
                        var member = new BodyTranslator(types, callees).MemberObligations(unit);
                        foreach (var wd in member.WellDefinedness)
                        {
                            Declare(unit.Key, wd.Theorem.Name, $"{display} (well-definedness {wd.Index})", null);
                        }
                        foreach (var vacuity in member.Vacuity)
                        {
                            Declare(unit.Key, vacuity.Theorem.Name, $"{display} (vacuity {vacuity.Index})", null);
                        }
                        return new TranslatedUnit(unit.Key, unit.Kind, name, display, [], null) { MemberContract = member };
                    }
                default:
                    throw new TranslationException(unit.Key, $"unknown unit kind {unit.Kind}.");
            }
        }

        private static bool HasContract(VirUnit unit) =>
            unit.Body is BlockStmt block && block.Stmts.Any(s => s is RequiresStmt or EnsuresStmt);

        /// <summary>
        /// A function unit's contract obligation (M6 KTD12), with its names recorded; null for a pure unit without a
        /// contract.
        /// </summary>
        private ContractObligation? Contract(VirUnit unit, Name name, string display, TypeTable types, CalleeEffects callees, bool raising)
        {
            var contract = new BodyTranslator(types, callees).Contract(unit, name, raising);
            if (contract is null)
            {
                // A script with nothing to prove would be dropped unread (M6 KTD16).
                return unit.Script is null
                    ? null
                    : throw new TranslationException(unit.Key, "it has a [ProofFor] script, but no contract obligation to prove: it has no Spec.Requires or Spec.Ensures and cannot raise.");
            }
            foreach (var wd in contract.WellDefinedness)
            {
                Declare(unit.Key, wd.Theorem.Name, $"{display} (well-definedness {wd.Index})", null);
            }
            Declare(unit.Key, contract.Theorem.Name, $"{display} (contract)", null);
            if (contract.Spec is { } spec)
            {
                Declare(unit.Key, spec.Name, $"{display} (contract spec)", null);
            }
            return contract;
        }

        /// <summary>Lean's height rule: one more than the largest <c>regular</c> height among the definitions the value mentions.</summary>
        private ReducibilityHints Regular(Expr value)
        {
            uint max = 0;
            ExprOps.ForEach(value, (e, _) =>
            {
                if (e is ConstExpr c && Hints(c.Name) is { Kind: ReducibilityHintsKind.Regular, Height: var h } && h > max)
                {
                    max = h;
                }
                return true;
            });
            return ReducibilityHints.Regular(max + 1);
        }

        private ReducibilityHints? Hints(Name name) =>
            _hints.TryGetValue(name, out var h) ? h : bundle.Find(name) is DefinitionInfo d ? d.Hints : null;

        /// <summary>Records a generated name; any collision, with another generated name or with the bundle, is an error (KTD6).</summary>
        private void Declare(string key, Name name, string display, ReducibilityHints? hints)
        {
            if (DisplayNames.ContainsKey(name) || bundle.Find(name) is not null)
            {
                throw new TranslationException(key, $"the name {name} collides with another declaration.");
            }
            DisplayNames.Add(name, display);
            if (hints is { } h)
            {
                _hints.Add(name, h);
            }
        }

        private static string Generated(string typeDisplay, Name name) => name.StringComponent switch
        {
            "$mk" => $"new {typeDisplay}",
            "$eq" => $"{typeDisplay} ==",
            "$index" => $"{typeDisplay} (member index)",
            var member => $"{typeDisplay}.{member}",
        };
    }
}
