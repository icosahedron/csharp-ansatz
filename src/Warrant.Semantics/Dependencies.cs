using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>
/// What a contract unit states (M6 KTD10, KTD25, KTD26): nothing to admit, since a contract class is never verified (R7),
/// but the checks that its <c>Spec</c> calls mean something. Each <c>Spec.Requires</c> and <c>Spec.Ensures</c> gets a
/// vacuity check, <c>∀ params [r], R₁ → … → False</c> over the statements up to it, the result universally bound once an
/// <c>Spec.Ensures</c> is among them: proving one shows that no result satisfies the contract, so every method calling the
/// member would hold vacuously after the call (KTD25). Each partial operation in them gets a well-definedness obligation
/// (KTD26), as a method's do. The member's contract itself is stated where it is used: as a hypothesis of the obligation of
/// each method that calls it (KTD9).
/// </summary>
public sealed class MemberContract
{
    internal MemberContract(ImmutableArray<SpecObligation> wellDefinedness, ImmutableArray<SpecObligation> vacuity)
    {
        WellDefinedness = wellDefinedness;
        Vacuity = vacuity;
    }

    /// <summary>The well-definedness obligations of the <c>Spec</c> expressions (KTD26), in source order.</summary>
    public ImmutableArray<SpecObligation> WellDefinedness { get; }

    /// <summary>One vacuity check per <c>Spec.Requires</c> and <c>Spec.Ensures</c> (KTD25), in source order.</summary>
    public ImmutableArray<SpecObligation> Vacuity { get; }
}

/// <summary>
/// External dependencies (M6 U19, KTD4, KTD9, KTD22). A method that calls a dependency member is a function of one
/// operation per (dependency, member) pair it calls, <c>op : args → ClrM σ R</c>, bound after the world and before its
/// parameters; an external call is the bound operation applied to its arguments, which may read and change the world, so
/// two calls are unrelated unless a contract relates them (KTD4). Its obligation takes, after its parameters, one
/// hypothesis per operation, the member's contract over every argument and every world (design D9):
/// <code>
/// ∀ (σ : Type) (op₁ : args → ClrM σ R₁) … params,
///   (∀ x, ⦃⌜Req₁ x⌝⦄ op₁ x ⦃post⟨fun r =&gt; ⌜Ens₁ x r⌝, allowed⟩⦄) → … →
///   ⦃⌜Requires⌝⦄ f op₁ … params ⦃post⟨fun r =&gt; ⌜Ensures r⌝, allowed⟩⦄
/// </code>
/// A <c>Task&lt;T&gt;</c> or <c>ValueTask&lt;T&gt;</c> result is a <c>ClrM σ T</c> program, and a <c>void</c>, <c>Task</c> or
/// <c>ValueTask</c> one a <c>ClrM σ Unit</c> program (KTD22); <c>await</c> of a call binds its program.
/// </summary>
internal sealed partial class BodyTranslator
{
    /// <summary>A bound operation: the dependency's index, the member's key, the operation's and its hypothesis's binders.</summary>
    private sealed record Operation(int Dependency, string Member, VirUnit Contract, Expr Op);

    /// <summary>The operations of the unit being translated, by dependency index and member key; empty when it has none.</summary>
    private readonly Dictionary<(int Dependency, string Member), Operation> _operations = [];

    /// <summary>The type a value of <paramref name="type"/> has once awaited: a task's result; any other type itself (KTD22).</summary>
    private static VirType Awaited(VirType type) => type is TaskType t ? t.Result : type;

    /// <summary>Whether a method of this return type returns no value: <c>void</c>, <c>Task</c> or <c>ValueTask</c>.</summary>
    private static bool ReturnsNothing(VirUnit unit) => unit.Returns is { } r && Awaited(r) == VirType.Unit;

    /// <summary>
    /// The unit's operations, as free variables of type <c>args → ClrM σ R</c> named <c>dependency_Member</c>, one per
    /// (dependency, member) pair in dependency order and then member key order (ordinal).
    /// </summary>
    private List<Operation> Operations(VirUnit unit, Expr sigma)
    {
        var result = new List<Operation>();
        var dependencies = unit.Dependencies ?? VirList<VirDependency>.Empty;
        for (int i = 0; i < dependencies.Count; i++)
        {
            foreach (var member in dependencies[i].Members)
            {
                var contract = ContractUnit(member);
                var args = (contract.Params ?? VirList<VirParam>.Empty).Select(p => _lctx.MkLocalDecl(_ngen, Name.From(p.Name), _types.Cic(p.Type))).ToList();
                var type = _lctx.MkPi([.. args], Monadic.Type(sigma, ReturnType(contract)));
                var op = new Operation(i, member, contract, _lctx.MkLocalDecl(_ngen, Name.From($"{dependencies[i].Name}_{MemberName(member)}"), type));
                _operations.Add((i, member), op);
                result.Add(op);
            }
        }
        return result;
    }

    /// <summary>A dependency member's contract unit, which must be among the units being translated.</summary>
    private VirUnit ContractUnit(string member) =>
        _callees?.Units.GetValueOrDefault(member) is { Kind: VirUnitKind.Contract } contract
            ? contract
            : throw new TranslationException(null, $"the contract of the dependency member {member} is not being translated.");

    /// <summary>A member's name from its key: <c>GetPayment</c> from <c>M:Payments.IPaymentStore.GetPayment(System.Int32)</c>.</summary>
    private static string MemberName(string key)
    {
        int open = key.IndexOf('(', StringComparison.Ordinal);
        var path = open < 0 ? key : key[..open];
        return path[(path.LastIndexOf('.') + 1)..];
    }

    /// <summary>The hypothesis's name for an operation: its own name with <c>_spec</c> appended.</summary>
    private Name ContractHypothesisName(Operation op) => Name.From(_lctx.Get(op.Op).UserName.ToString() + "_spec");

    /// <summary>
    /// The contract of an operation as a hypothesis (KTD9): <c>∀ args, ⦃⌜Req args⌝⦄ op args ⦃post⟨fun r =&gt; ⌜Ens args
    /// r⌝, allowed⟩⦄</c>, the member's <c>Spec.Requires</c> and <c>Spec.Ensures</c> as its contract unit states them, at every
    /// world, since the triple holds from every state. A missing one is <c>True</c>. The contract unit's own obligations
    /// are its own (<see cref="MemberContract"/>).
    /// </summary>
    private Expr Hypothesis(Operation op, Expr sigma)
    {
        var contract = op.Contract;
        var nested = new BodyTranslator(_types, _callees, _lctx, _ngen) { _quantified = true };
        var args = new List<Expr>();
        foreach (var p in contract.Params ?? VirList<VirParam>.Empty)
        {
            var x = _lctx.MkLocalDecl(_ngen, Name.From(p.Name), _types.Cic(p.Type));
            nested._params.Add(x);
            args.Add(x);
        }
        var returns = ReturnType(contract);
        var stmts = contract.Body is BlockStmt block ? block.Stmts : VirList<VirStmt>.Empty;
        var ensures = stmts.OfType<EnsuresStmt>().ToList();
        var r = _lctx.MkLocalDecl(_ngen, Name.From(ensures.Select(e => e.Name).FirstOrDefault(n => n is not null) ?? "r"), returns);
        // A translator with no world records no obligation: the contract unit states its own.
        var spec = nested._spec = new SpecState(contract, null, []);
        var pre = Triples.Conjunction([.. stmts.OfType<RequiresStmt>().Select(q => nested.Cond(q.Condition, Env.Empty).Prop)]);
        spec.Result = r;
        var post = Triples.Conjunction([.. ensures.Select(e => nested.Cond(e.Condition, e.Local is { } l ? Env.Empty.Set(l, r) : Env.Empty).Prop)]);
        var triple = Triples.Triple(sigma, returns, Expr.App(op.Op, [.. args]), Triples.Pure(sigma, pre),
            Triples.Post(sigma, returns, _lctx.MkLambda([r], Triples.Pure(sigma, post))));
        return _lctx.MkPi([.. args], triple);
    }

    /// <summary>
    /// An external call's program, <c>op args</c>, its arguments bound left to right, then <paramref name="k"/>; a site the
    /// VC walker reports at (M6 U20, KTD18): the member's precondition and an exception from it are the call's.
    /// </summary>
    private Expr External(ExternalCallExpr call, VirType type, Env env, Expr result, Next? k) =>
        BoundAll(call.Args, env, result, args =>
        {
            var op = _operations.GetValueOrDefault((call.Dependency, call.Member))
                ?? throw new TranslationException(null, $"the external call to {call.Member} names dependency {call.Dependency}, which does not list it.");
            return Emit(Site(call, Expr.App(op.Op, [.. args])), type, k);
        });

    /// <summary>
    /// <c>await e</c> (KTD22): <c>e</c>'s program bound, its value the awaited one. <c>e</c> is an
    /// external call, or a call to a verified method: that method's program, <c>g σ args</c> when it can raise and
    /// <c>pure (g args)</c> otherwise, so the VC walker sees every awaited call as a bind.
    /// </summary>
    private Expr Await(AwaitExpr a, Env env, Expr result, Next? k)
    {
        switch (a.Operand)
        {
            case ExternalCallExpr x when x.Type is TaskType:
                return External(x, a.Type, env, result, k);
            case CallExpr c when c.Type is TaskType:
                RejectCallWithDependencies(c.Target);
                return BoundAll(c.Args, env, result, args =>
                {
                    var f = Expr.Const(LeanNames.ForKey(c.Target));
                    var program = IsRaisingCallee(c.Target)
                        ? Expr.App(f, [_sigma!, .. args])
                        : Monadic.Pure(_sigma!, _types.Cic(a.Type), Expr.App(f, [.. args]));
                    return Emit(program, a.Type, k);
                });
            default:
                throw new TranslationException(null, "await of something other than a call that returns a Task or ValueTask.");
        }
    }

    /// <summary>
    /// A call to a method with dependencies, which would need operations the caller does not bind. Extraction never makes
    /// one: such a method is an instance method of a service class, and calling it is a member access on <c>this</c>.
    /// </summary>
    private void RejectCallWithDependencies(string target)
    {
        if (_callees?.Units.GetValueOrDefault(target) is { Dependencies.Count: > 0 })
        {
            throw new TranslationException(null, $"the call to {target}, which has dependencies of its own, is not translated.");
        }
    }

    /// <summary>
    /// A contract unit's own obligations (KTD25, KTD26): the vacuity check of each <c>Spec</c> call and the
    /// well-definedness of its <c>Spec</c> expressions.
    /// </summary>
    public MemberContract MemberObligations(VirUnit unit)
    {
        _quantified = true;
        var sigma = _lctx.MkLocalDecl(_ngen, Name.From("σ"), Expr.Type);
        var binders = Binders(unit);
        var returns = ReturnType(unit);
        var spec = _spec = new SpecState(unit, sigma, binders);
        var stmts = unit.Body is BlockStmt block ? block.Stmts : VirList<VirStmt>.Empty;
        var r = _lctx.MkLocalDecl(_ngen, Name.From(stmts.OfType<EnsuresStmt>().Select(e => e.Name).FirstOrDefault(n => n is not null) ?? "r"), returns);
        var vacuity = new List<SpecObligation>();
        var facts = new List<Expr>();
        bool result = false;
        foreach (var stmt in stmts)
        {
            Expr prop;
            switch (stmt)
            {
                case RequiresStmt q:
                    prop = InGuards(facts, () => Cond(q.Condition, Env.Empty)).Prop;
                    break;
                case EnsuresStmt e:
                    result = true;
                    spec.Result = r;
                    prop = InGuards(facts, () => Cond(e.Condition, e.Local is { } l ? Env.Empty.Set(l, r) : Env.Empty)).Prop;
                    spec.Result = null;
                    break;
                default:
                    throw new TranslationException(unit.Key, $"a contract holds only Spec.Requires and Spec.Ensures, not {stmt.GetType().Name}.");
            }
            facts.Add(prop);
            var hyps = facts.Select(p => _lctx.MkLocalDecl(_ngen, GuardName, p)).ToList();
            List<Expr> fvars = [.. binders, .. result ? [r] : Array.Empty<Expr>(), .. hyps];
            vacuity.Add(new SpecObligation(
                vacuity.Count + 1, SpecObligationKind.Vacuity,
                new TheoremShell(LeanNames.Vacuity(unit.Key, vacuity.Count + 1), new Condition(Closed(_lctx.MkPi(fvars, Init.PropFalse)), null), null, null),
                stmt, fvars.Count));
        }
        _spec = null;
        return new MemberContract([.. spec.WellDefinedness], [.. vacuity]);
    }
}
