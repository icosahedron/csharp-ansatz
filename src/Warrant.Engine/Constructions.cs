using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Meta;
using LocalContext = Warrant.Kernel.LocalContext;

namespace Warrant.Engine;

/// <summary>
/// The auxiliary definitions Lean's elaborator makes for every inductive type and the kernel does not (M5a KTD8, docs/m5a/04
/// "<c>cases</c> and <c>induction</c>"): <c>T.casesOn</c>, which <c>cases</c> eliminates with, and <c>T.ctorIdx</c>, which
/// tells constructors apart. The engine generates both for every translated inductive; they are definitions the kernel
/// checks, so generating them in untrusted code adds nothing to the trusted base. The names are Lean's, which M4 KTD6
/// reserved.
/// </summary>
public static class Constructions
{
    private static readonly Name NatName = Name.From("Nat");

    /// <summary>Lean's <c>mkCasesOnName</c>: <c>T.casesOn</c>.</summary>
    public static Name CasesOnName(Name indName)
    {
        ArgumentNullException.ThrowIfNull(indName);
        return indName.Append("casesOn");
    }

    /// <summary>Lean's <c>mkCtorIdxName</c>: <c>T.ctorIdx</c>.</summary>
    public static Name CtorIdxName(Name indName)
    {
        ArgumentNullException.ThrowIfNull(indName);
        return indName.Append("ctorIdx");
    }

    /// <summary>
    /// The definitions to admit after an inductive declaration, in order: for each of its types, <c>casesOn</c> and then
    /// <c>ctorIdx</c> (which uses it), unless <see cref="MkCtorIdx"/> skips it.
    /// </summary>
    /// <param name="env">An environment in which <paramref name="declaration"/> has been admitted.</param>
    /// <param name="declaration">The inductive declaration.</param>
    /// <returns>The definitions, each to be admitted before the next is built.</returns>
    public static IEnumerable<DefinitionDecl> For(KernelEnvironment env, InductiveDecl declaration)
    {
        ArgumentNullException.ThrowIfNull(env);
        ArgumentNullException.ThrowIfNull(declaration);
        return Generate();

        IEnumerable<DefinitionDecl> Generate()
        {
            foreach (var type in declaration.Types)
            {
                yield return new DefinitionDecl(MkCasesOn(env, type.Name));
                if (MkCtorIdx(env, type.Name) is { } ctorIdx)
                {
                    yield return new DefinitionDecl(ctorIdx);
                }
            }
        }
    }

    /// <summary>
    /// Marks the generated definitions in an attribute overlay as Lean marks its own: <c>casesOn</c> is <c>@[reducible]</c>
    /// (an <c>abbrev</c>), which Meta's <c>whnfCore</c> also unfolds at every transparency as an auxiliary recursor
    /// (<see cref="MetaM.IsAuxRecursor"/> recognizes it by name); <c>ctorIdx</c> keeps the default status, as in Lean.
    /// </summary>
    /// <param name="attributes">The run's overlay (a fork of the sidecar).</param>
    /// <param name="definition">A definition <see cref="For"/> generated.</param>
    public static void Register(Sidecar attributes, DefinitionInfo definition)
    {
        ArgumentNullException.ThrowIfNull(attributes);
        ArgumentNullException.ThrowIfNull(definition);
        if (definition.Name.StringComponent == "casesOn")
        {
            attributes.SetReducibilityStatus(definition.Name, ReducibilityStatus.Reducible);
        }
    }

    /// <summary>
    /// <c>T.casesOn</c> (Lean's C++ <c>mk_cases_on</c>, the shape Init's <c>Bool.casesOn</c> and <c>Nat.casesOn</c> have):
    /// <c>T.rec</c> with the induction hypotheses dropped and the major premise before the minor premises.
    /// <code>
    /// T.casesOn.{u, us} : ∀ params {motive} indices (t : T params indices) (minor_i : ∀ fields, motive … (C_i params fields)), motive indices t
    ///   := fun params motive indices t minors => T.rec params motive (fun fields ihs => minor_i fields)… indices t
    /// </code>
    /// The universe parameters, binder names and binder annotations are the recursor's; the definition is an
    /// <c>abbrev</c>.
    /// </summary>
    /// <param name="env">The environment with <c>T</c> and <c>T.rec</c>.</param>
    /// <param name="indName">The inductive type <c>T</c>.</param>
    /// <returns>The definition.</returns>
    /// <exception cref="ArgumentException"><c>T</c> is not an inductive type, or is mutual or nested (its recursor has several motives).</exception>
    public static DefinitionInfo MkCasesOn(KernelEnvironment env, Name indName)
    {
        ArgumentNullException.ThrowIfNull(env);
        ArgumentNullException.ThrowIfNull(indName);
        if (env.Find(indName) is not InductiveInfo ind || env.Find(indName.Append("rec")) is not Cic.RecursorInfo rec)
        {
            throw new ArgumentException($"'{indName}' is not an inductive type with a recursor.", nameof(indName));
        }
        if (rec.NumMotives != 1)
        {
            throw new ArgumentException($"'{indName}' is mutual or nested; casesOn is generated only for a type whose recursor has one motive.", nameof(indName));
        }

        var lctx = new LocalContext();
        var ngen = new NameGenerator(Name.From("_warrant"));
        var type = rec.Type;
        var parameters = Open(rec.NumParams);
        var motive = Open(1)[0];
        var minors = Open(rec.NumMinors);
        var indices = Open(rec.NumIndices);
        var major = Open(1)[0];
        var conclusion = type;

        var newMinors = new List<Expr>();
        var recMinors = new List<Expr>();
        foreach (var minor in minors)
        {
            var decl = lctx.Get(minor);
            var minorType = decl.Type;
            var minorParams = new List<Expr>();
            var nonRec = new List<Expr>();
            while (minorType is ForallExpr f)
            {
                var local = lctx.MkLocalDecl(ngen, f.BinderName, f.BinderType, f.BinderInfo);
                var curr = f.BinderType;
                while (curr is ForallExpr inner)
                {
                    curr = inner.Body;
                }
                if (curr.GetAppFn() != motive)
                {
                    nonRec.Add(local);
                }
                minorParams.Add(local);
                minorType = ExprOps.Instantiate(f.Body, local);
            }
            var newMinor = lctx.MkLocalDecl(ngen, decl.UserName, lctx.MkPi(nonRec, minorType), decl.BinderInfo);
            newMinors.Add(newMinor);
            recMinors.Add(lctx.MkLambda(minorParams, ExprOps.MkApp(newMinor, [.. nonRec])));
        }

        var levels = rec.LevelParams.Select(Level.Param).ToEquatableArray();
        Expr[] binders = [.. parameters, motive, .. indices, major, .. newMinors];
        var value = ExprOps.MkApp(Expr.Const(rec.Name, levels), [.. parameters, motive, .. recMinors, .. indices, major]);
        var name = CasesOnName(indName);
        return new DefinitionInfo(
            name,
            rec.LevelParams,
            lctx.MkPi(binders, conclusion),
            lctx.MkLambda(binders, value),
            ReducibilityHints.Abbrev,
            ind.IsUnsafe ? DefinitionSafety.Unsafe : DefinitionSafety.Safe,
            [name]);

        Expr[] Open(int n)
        {
            var xs = new Expr[n];
            for (int i = 0; i < n; i++)
            {
                var f = (ForallExpr)type;
                xs[i] = lctx.MkLocalDecl(ngen, f.BinderName, f.BinderType, f.BinderInfo);
                type = ExprOps.Instantiate(f.Body, xs[i]);
            }
            return xs;
        }
    }

    /// <summary>
    /// <c>T.ctorIdx : ∀ {params} {indices}, T params indices → Nat</c>, the constructor's position (Lean's <c>mkCtorIdx</c>,
    /// Lean/Meta/Constructions/CtorIdx.lean 41): <c>0</c> for a type with one constructor, otherwise
    /// <c>T.casesOn (motive := fun indices x => Nat) x (fun fields => i)…</c>, with a <c>regular</c> height one more than the
    /// heights the value mentions. Skipped, as Lean skips it, for a type of propositions and for a type whose
    /// <c>casesOn</c> eliminates only into <c>Prop</c>.
    /// </summary>
    /// <param name="env">The environment with <c>T</c> and <c>T.casesOn</c>.</param>
    /// <param name="indName">The inductive type <c>T</c>.</param>
    /// <returns>The definition, or null when Lean would not make one.</returns>
    public static DefinitionInfo? MkCtorIdx(KernelEnvironment env, Name indName)
    {
        ArgumentNullException.ThrowIfNull(env);
        ArgumentNullException.ThrowIfNull(indName);
        if (env.Find(indName) is not InductiveInfo info)
        {
            throw new ArgumentException($"'{indName}' is not an inductive type.", nameof(indName));
        }
        if (IsPropFormerType(info.Type))
        {
            return null;
        }
        var casesOnName = CasesOnName(indName);
        var casesOn = env.Find(casesOnName) ?? throw new ArgumentException($"'{casesOnName}' must be admitted before '{CtorIdxName(indName)}'.", nameof(indName));
        if (casesOn.LevelParams.Count <= info.LevelParams.Count)
        {
            return null;
        }

        var lctx = new LocalContext();
        var ngen = new NameGenerator(Name.From("_warrant"));
        var us = info.LevelParams.Select(Level.Param).ToEquatableArray();
        var type = info.Type;
        var xs = new Expr[info.NumParams + info.NumIndices];
        for (int i = 0; i < xs.Length; i++)
        {
            // withImplicitBinderInfos: the parameters and indices are implicit.
            var f = (ForallExpr)type;
            xs[i] = lctx.MkLocalDecl(ngen, f.BinderName, f.BinderType, BinderInfo.Implicit);
            type = ExprOps.Instantiate(f.Body, xs[i]);
        }
        var parameters = xs[..info.NumParams];
        var indices = xs[info.NumParams..];
        var indType = ExprOps.MkApp(Expr.Const(indName, us), xs);
        var nat = Expr.Const(NatName);
        var x = lctx.MkLocalDecl(ngen, Name.From("x"), indType);

        Expr body;
        if (info.Constructors.Count == 1)
        {
            body = Expr.NatLit(0);
        }
        else
        {
            var motive = lctx.MkLambda([.. indices, x], nat);
            body = ExprOps.MkApp(Expr.Const(casesOnName, new[] { Level.One }.Concat(us).ToEquatableArray()), [.. parameters, motive, .. indices, x]);
            foreach (var c in info.Constructors)
            {
                var ctor = (ConstructorInfo)env.Get(c);
                var ctorType = ExprOps.InstantiateTypeLevelParams(ctor, us);
                foreach (var p in parameters)
                {
                    ctorType = ExprOps.Instantiate(((ForallExpr)ctorType).Body, p);
                }
                var fields = new Expr[ctor.NumFields];
                for (int i = 0; i < fields.Length; i++)
                {
                    var f = (ForallExpr)ctorType;
                    fields[i] = lctx.MkLocalDecl(ngen, f.BinderName, f.BinderType, f.BinderInfo);
                    ctorType = ExprOps.Instantiate(f.Body, fields[i]);
                }
                body = Expr.App(body, lctx.MkLambda(fields, Expr.NatLit(ctor.Index)));
            }
        }

        var value = lctx.MkLambda([.. xs, x], body);
        var name = CtorIdxName(indName);
        return new DefinitionInfo(
            name,
            info.LevelParams,
            lctx.MkPi(xs, Expr.Forall(Name.From("x"), indType, nat)),
            value,
            ReducibilityHints.Regular(MaxHeight(env, value) + 1),
            info.IsUnsafe ? DefinitionSafety.Unsafe : DefinitionSafety.Safe,
            [name]);
    }

    /// <summary>Lean's <c>getMaxHeight</c>: the largest <c>regular</c> height among the definitions <paramref name="e"/> mentions.</summary>
    private static uint MaxHeight(KernelEnvironment env, Expr e)
    {
        uint max = 0;
        ExprOps.ForEach(e, (sub, _) =>
        {
            if (sub is ConstExpr c && env.Find(c.Name) is DefinitionInfo { Hints: { Kind: ReducibilityHintsKind.Regular, Height: var h } } && h > max)
            {
                max = h;
            }
            return true;
        });
        return max;
    }

    /// <summary>Lean's <c>isPropFormerType</c> for an inductive's type, which is syntactically <c>∀ …, Sort u</c>.</summary>
    private static bool IsPropFormerType(Expr type)
    {
        while (type is ForallExpr f)
        {
            type = f.Body;
        }
        return type is SortExpr { Level.Kind: LevelKind.Zero };
    }
}
