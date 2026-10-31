using LeanSharp.Cic;

namespace LeanSharp.Kernel;

/// <summary>A declaration submitted to the kernel (Lean's <c>Declaration</c>).</summary>
public abstract record KernelDeclaration;

/// <summary>An axiom.</summary>
public sealed record AxiomDecl(AxiomInfo Value) : KernelDeclaration;

/// <summary>A (non-mutual) definition.</summary>
public sealed record DefinitionDecl(DefinitionInfo Value) : KernelDeclaration;

/// <summary>A theorem.</summary>
public sealed record TheoremDecl(TheoremInfo Value) : KernelDeclaration;

/// <summary>An opaque definition.</summary>
public sealed record OpaqueDecl(OpaqueInfo Value) : KernelDeclaration;

/// <summary>A block of mutually recursive definitions; only allowed for unsafe and partial definitions.</summary>
public sealed record MutualDefinitionDecl(EquatableArray<DefinitionInfo> Values) : KernelDeclaration;

/// <summary>The quotient package: <c>Quot</c>, <c>Quot.mk</c>, <c>Quot.lift</c>, <c>Quot.ind</c>.</summary>
public sealed record QuotDecl : KernelDeclaration;

/// <summary>A constructor in an <see cref="InductiveDecl"/>.</summary>
public sealed record InductiveConstructor(Name Name, Expr Type);

/// <summary>One inductive type in an <see cref="InductiveDecl"/>.</summary>
public sealed record InductiveType(Name Name, Expr Type, EquatableArray<InductiveConstructor> Constructors);

/// <summary>
/// A (possibly mutual, possibly nested) block of inductive types. The kernel derives the
/// recursors itself.
/// </summary>
public sealed record InductiveDecl(EquatableArray<Name> LevelParams, int NumParams, EquatableArray<InductiveType> Types, bool IsUnsafe) : KernelDeclaration;

/// <summary>
/// The kernel's admission rules: what may be added to an environment. A port of Lean 4's
/// <c>environment.cpp</c> (<c>add_axiom</c>, <c>add_definition</c>, …), <c>quot.cpp</c> and
/// <c>inductive.cpp</c>.
/// </summary>
public static class Kernel
{
    /// <summary>Type-checks <paramref name="declaration"/> and, if it is valid, adds it to <paramref name="env"/>.</summary>
    /// <exception cref="KernelException">The declaration is rejected; <paramref name="env"/> is unchanged.</exception>
    public static void Add(KernelEnvironment env, KernelDeclaration declaration, KernelLimits? limits = null)
    {
        ArgumentNullException.ThrowIfNull(env);
        ArgumentNullException.ThrowIfNull(declaration);
        var fork = env.Fork();
        try
        {
            switch (declaration)
            {
                case AxiomDecl a:
                    AddAxiom(fork, a.Value, limits);
                    break;
                case DefinitionDecl d:
                    AddDefinition(fork, d.Value, limits);
                    break;
                case TheoremDecl t:
                    AddTheorem(fork, t.Value, limits);
                    break;
                case OpaqueDecl o:
                    AddOpaque(fork, o.Value, limits);
                    break;
                case MutualDefinitionDecl m:
                    AddMutual(fork, m.Values, limits);
                    break;
                case QuotDecl:
                    Quotient.Add(fork);
                    break;
                case InductiveDecl i:
                    Inductive.Add(fork, i, limits);
                    break;
                default:
                    throw new ArgumentException($"Unsupported declaration {declaration.GetType().Name}.", nameof(declaration));
            }
        }
        catch (InsufficientExecutionStackException ex)
        {
            throw new KernelResourceException("kernel recursion too deep for the available stack", ex);
        }
        fork.Commit();
    }

    internal static void CheckNoFVar(Name name, Expr e)
    {
        if (e.HasFVar)
        {
            throw new KernelException($"declaration '{name}' contains free variables");
        }
    }

    internal static void CheckDuplicatedUnivParams(EquatableArray<Name> lps)
    {
        for (int i = 0; i < lps.Count; i++)
        {
            for (int j = i + 1; j < lps.Count; j++)
            {
                if (lps[i] == lps[j])
                {
                    throw new KernelException($"failed to add declaration to environment, duplicate universe level parameter: '{lps[i]}'");
                }
            }
        }
    }

    private static void CheckConstantVal(KernelEnvironment env, ConstantInfo v, TypeChecker checker)
    {
        env.CheckName(v.Name);
        CheckDuplicatedUnivParams(v.LevelParams);
        CheckNoFVar(v.Name, v.Type);
        var sort = checker.Check(v.Type, v.LevelParams);
        checker.EnsureSort(sort, v.Type);
    }

    private static void CheckValue(TypeChecker checker, ConstantInfo v, Expr value)
    {
        CheckNoFVar(v.Name, value);
        var valType = checker.Check(value, v.LevelParams);
        if (!checker.IsDefEq(valType, v.Type))
        {
            throw new KernelException($"declaration type mismatch, '{v.Name}' has type{Environment.NewLine}  {valType}{Environment.NewLine}but is expected to have type{Environment.NewLine}  {v.Type}");
        }
    }

    private static void AddAxiom(KernelEnvironment env, AxiomInfo v, KernelLimits? limits)
    {
        CheckConstantVal(env, v, new TypeChecker(env, v.IsUnsafe ? DefinitionSafety.Unsafe : DefinitionSafety.Safe, limits));
        env.AddCore(v);
    }

    private static void AddDefinition(KernelEnvironment env, DefinitionInfo v, KernelLimits? limits)
    {
        if (v.Safety == DefinitionSafety.Unsafe)
        {
            // Unsafe definitions may be recursive: check the header, add, then check the body.
            CheckConstantVal(env, v, new TypeChecker(env, DefinitionSafety.Unsafe, limits));
            env.AddCore(v);
            CheckValue(new TypeChecker(env, DefinitionSafety.Unsafe, limits), v, v.DefinitionValue);
        }
        else
        {
            var checker = new TypeChecker(env, DefinitionSafety.Safe, limits);
            CheckConstantVal(env, v, checker);
            CheckValue(checker, v, v.DefinitionValue);
            env.AddCore(v);
        }
    }

    private static void AddTheorem(KernelEnvironment env, TheoremInfo v, KernelLimits? limits)
    {
        var checker = new TypeChecker(env, DefinitionSafety.Safe, limits);
        CheckConstantVal(env, v, checker);
        if (!checker.IsProp(v.Type))
        {
            throw new KernelException($"type of theorem '{v.Name}' is not a proposition{Environment.NewLine}  {v.Type}");
        }
        CheckValue(checker, v, v.Proof);
        env.AddCore(v);
    }

    private static void AddOpaque(KernelEnvironment env, OpaqueInfo v, KernelLimits? limits)
    {
        var checker = new TypeChecker(env, DefinitionSafety.Safe, limits);
        CheckConstantVal(env, v, checker);
        CheckValue(checker, v, v.OpaqueValue);
        env.AddCore(v);
    }

    private static void AddMutual(KernelEnvironment env, EquatableArray<DefinitionInfo> vs, KernelLimits? limits)
    {
        if (vs.Count == 0)
        {
            throw new KernelException("invalid empty mutual definition");
        }
        var safety = vs[0].Safety;
        if (safety == DefinitionSafety.Safe)
        {
            throw new KernelException("invalid mutual definition, declaration is not tagged as unsafe/partial");
        }
        var lparams = vs[0].LevelParams;
        var headerChecker = new TypeChecker(env, safety, limits);
        var found = new HashSet<Name>();
        foreach (var v in vs)
        {
            if (v.Safety != safety)
            {
                throw new KernelException("invalid mutual definition, declarations must have the same safety annotation");
            }
            if (!v.LevelParams.Equals(lparams))
            {
                throw new KernelException("invalid mutual definition, declarations must have the same universe level parameters");
            }
            if (!found.Add(v.Name))
            {
                throw new KernelException($"invalid mutual definition, duplicate declaration name '{v.Name}'");
            }
            CheckConstantVal(env, v, headerChecker);
        }
        foreach (var v in vs)
        {
            env.AddCore(v);
        }
        var checker = new TypeChecker(env, safety, limits);
        foreach (var v in vs)
        {
            CheckValue(checker, v, v.DefinitionValue);
        }
    }
}

/// <summary>The built-in quotient types (Lean's <c>quot.cpp</c>).</summary>
internal static class Quotient
{
    public static void Add(KernelEnvironment env)
    {
        if (env.IsQuotInitialized)
        {
            return;
        }
        CheckEqType(env);
        env.CheckName(KernelNames.Quot);
        env.CheckName(KernelNames.QuotMk);
        env.CheckName(KernelNames.QuotLift);
        env.CheckName(KernelNames.QuotInd);
        foreach (var c in ExpectedConstants())
        {
            env.AddCore(c);
        }
        env.MarkQuotInitialized();
    }

    private static Expr Arrow(Expr a, Expr b) => Expr.Forall(Name.From("a"), a, ExprOps.LiftLooseBVars(b, 0, 1));

    /// <summary>The four quotient constants, as Lean's kernel generates them.</summary>
    public static IReadOnlyList<QuotInfo> ExpectedConstants()
    {
        var lctx = new LocalContext();
        var g = new NameGenerator(Name.From("_quot"));
        var uName = Name.From("u");
        var u = Level.Param(uName);
        var sortU = Expr.Sort(u);
        var alpha = lctx.MkLocalDecl(g, Name.From("α"), sortU, BinderInfo.Implicit);
        var r = lctx.MkLocalDecl(g, Name.From("r"), Arrow(alpha, Arrow(alpha, Expr.Prop)));
        var quot = new QuotInfo(KernelNames.Quot, EquatableArray.Create(uName), lctx.MkPi([alpha, r], sortU), QuotKind.Type);
        var quotR = Expr.App(Expr.Const(KernelNames.Quot, u), alpha, r);
        var a = lctx.MkLocalDecl(g, Name.From("a"), alpha);
        var mk = new QuotInfo(KernelNames.QuotMk, EquatableArray.Create(uName), lctx.MkPi([alpha, r, a], quotR), QuotKind.Ctor);

        // `r` is implicit from here on.
        lctx = new LocalContext();
        alpha = lctx.MkLocalDecl(g, Name.From("α"), sortU, BinderInfo.Implicit);
        r = lctx.MkLocalDecl(g, Name.From("r"), Arrow(alpha, Arrow(alpha, Expr.Prop)), BinderInfo.Implicit);
        quotR = Expr.App(Expr.Const(KernelNames.Quot, u), alpha, r);
        a = lctx.MkLocalDecl(g, Name.From("a"), alpha);
        var vName = Name.From("v");
        var v = Level.Param(vName);
        var beta = lctx.MkLocalDecl(g, Name.From("β"), Expr.Sort(v), BinderInfo.Implicit);
        var f = lctx.MkLocalDecl(g, Name.From("f"), Arrow(alpha, beta));
        var b = lctx.MkLocalDecl(g, Name.From("b"), alpha);
        var rab = Expr.App(r, a, b);
        var faEqFb = Expr.App(Expr.Const(KernelNames.Eq, v), beta, Expr.App(f, a), Expr.App(f, b));
        var sanity = lctx.MkPi([a, b], Arrow(rab, faEqFb));
        var lift = new QuotInfo(KernelNames.QuotLift, EquatableArray.Create(uName, vName),
            lctx.MkPi([alpha, r, beta, f], Arrow(sanity, Arrow(quotR, beta))), QuotKind.Lift);

        beta = lctx.MkLocalDecl(g, Name.From("β"), Arrow(quotR, Expr.Prop), BinderInfo.Implicit);
        var quotMkA = Expr.App(Expr.Const(KernelNames.QuotMk, u), alpha, r, a);
        var allQuot = lctx.MkPi(a, Expr.App(beta, quotMkA));
        var q = lctx.MkLocalDecl(g, Name.From("q"), quotR);
        var betaQ = Expr.App(beta, q);
        var ind = new QuotInfo(KernelNames.QuotInd, EquatableArray.Create(uName),
            lctx.MkPi([alpha, r, beta], Expr.Forall(Name.From("mk"), allQuot, lctx.MkPi(q, betaQ))), QuotKind.Ind);
        return [quot, mk, lift, ind];
    }

    private static void CheckEqType(KernelEnvironment env)
    {
        if (env.Find(KernelNames.Eq) is not InductiveInfo eq)
        {
            throw new KernelException("failed to initialize quot module, environment does not have 'Eq' type");
        }
        if (eq.LevelParams.Count != 1)
        {
            throw new KernelException("failed to initialize quot module, unexpected number of universe params at 'Eq' type");
        }
        if (eq.Constructors.Count != 1)
        {
            throw new KernelException("failed to initialize quot module, unexpected number of constructors for 'Eq' type");
        }
        var lctx = new LocalContext();
        var g = new NameGenerator(Name.From("_quot"));
        {
            var u = Level.Param(eq.LevelParams[0]);
            var alpha = lctx.MkLocalDecl(g, Name.From("α"), Expr.Sort(u), BinderInfo.Implicit);
            var expected = lctx.MkPi(alpha, Arrow(alpha, Arrow(alpha, Expr.Prop)));
            if (!expected.AlphaEquals(eq.Type))
            {
                throw new KernelException("failed to initialize quot module, 'Eq' has an expected type");
            }
        }
        {
            var refl = env.Get(eq.Constructors[0]);
            var u = Level.Param(refl.LevelParams[0]);
            var alpha = lctx.MkLocalDecl(g, Name.From("α"), Expr.Sort(u), BinderInfo.Implicit);
            var a = lctx.MkLocalDecl(g, Name.From("a"), alpha);
            var expected = lctx.MkPi([alpha, a], Expr.App(Expr.Const(KernelNames.Eq, u), alpha, a, a));
            if (!expected.AlphaEquals(refl.Type))
            {
                throw new KernelException("failed to initialize quot module, unexpected type for 'Eq' type constructor");
            }
        }
    }
}
