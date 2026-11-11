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
            ordered.Where(Effects.HasRequires).Select(u => u.Key).ToHashSet(StringComparer.Ordinal));
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
            if (unit.Dependencies is { Count: > 0 })
            {
                throw new TranslationException(unit.Key, "a unit with external dependencies is not translated until M6 U19.");
            }
            bool raising = callees.Analysis.IsRaising(unit.Key);
            switch (unit.Kind)
            {
                case VirUnitKind.Function when raising && (BodyTranslator.IsRecursive(unit) || callees.Analysis.IsRecursive(unit.Key)):
                    // Extraction rejects this (KTD11): the recursive call would sit inside a bind, out of the decrease obligations' sight.
                    throw new TranslationException(unit.Key, "a recursive method that can raise an exception is not translated (recursion with effects).");
                case VirUnitKind.Function when raising:
                    {
                        // M6 KTD4, KTD11: a unit that can raise is a ClrM program over an opaque world.
                        var (type, value) = new BodyTranslator(types, callees).MonadicFunction(unit);
                        var decl = TypeDeclarations.Definition(name, type, value, Regular);
                        Declare(unit.Key, name, display, decl.Value.Hints);
                        return new TranslatedUnit(unit.Key, unit.Kind, name, display, [decl], null);
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
                        var (type, value) = new BodyTranslator(types, callees).Function(unit);
                        var decl = TypeDeclarations.Definition(name, type, value, Regular);
                        Declare(unit.Key, name, display, decl.Value.Hints);
                        return new TranslatedUnit(unit.Key, unit.Kind, name, display, [decl], null);
                    }
                case VirUnitKind.Theorem:
                    {
                        var (statement, claim) = new BodyTranslator(types, callees).StatementAndClaim(unit);
                        Declare(unit.Key, name, display, null);
                        return new TranslatedUnit(unit.Key, unit.Kind, name, display, [], new TheoremShell(name, statement, unit.Script, unit.Budget, claim));
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
                    throw new TranslationException(unit.Key, "a contract unit is not translated until M6 U19.");
                default:
                    throw new TranslationException(unit.Key, $"unknown unit kind {unit.Kind}.");
            }
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
