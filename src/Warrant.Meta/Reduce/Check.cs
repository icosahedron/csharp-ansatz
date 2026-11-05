using Warrant.Cic;
using Warrant.Kernel;
using KernelLocalContext = Warrant.Kernel.LocalContext;

namespace Warrant.Meta;

// Type checking of Meta terms (Lean 4.35.0's Lean/Meta/Check.lean). A ground term, one without
// metavariables, is handed to Warrant's kernel in a kernel copy of the local context (KTD3); a
// term with metavariables is checked by Meta itself, as Lean's `check` does.
public sealed partial class MetaM
{
    private static readonly Name KernelCheckPrefix = Name.From("_meta_check");

    /// <summary>
    /// Kernel-check every ground value Meta assigns to a metavariable, against the metavariable's
    /// type (a debug mode, docs/m5a/02). An ill-typed assignment throws a <see cref="MetaException"/>
    /// at the assignment instead of a kernel rejection of the finished proof.
    /// </summary>
    public bool DebugCheckAssignments { get; set; }

    /// <summary>
    /// Throws if <paramref name="e"/> is not type correct at <paramref name="transparency"/>
    /// (Lean's <c>Meta.check</c>). After instantiation, a ground term is checked by the kernel.
    /// </summary>
    /// <exception cref="MetaException">It is not type correct.</exception>
    public void Check(Expr e, TransparencyMode transparency = TransparencyMode.All)
    {
        ArgumentNullException.ThrowIfNull(e);
        var e1 = this.InstantiateMVars(e);
        if (!e1.HasExprMVar && !e1.HasLevelMVar && KernelInfer(LCtx, e1, null) is not null)
        {
            return;
        }
        WithTransparency(transparency, () =>
        {
            CheckAux(e1);
            return 0;
        });
    }

    /// <summary>Whether <paramref name="e"/> is type correct (Lean's <c>isTypeCorrect</c>).</summary>
    public bool IsTypeCorrect(Expr e)
    {
        try
        {
            Check(e);
            return true;
        }
        catch (MetaException ex) when (ex is not MetaResourceException)
        {
            return false;
        }
    }

    /// <summary>
    /// Type-checks the ground term <paramref name="e"/> with the kernel in the current local
    /// context and returns its type (Lean's <c>checkWithKernel</c>).
    /// </summary>
    /// <exception cref="MetaException">The term has metavariables, or the kernel rejects it.</exception>
    public Expr CheckWithKernel(Expr e)
    {
        ArgumentNullException.ThrowIfNull(e);
        var e1 = this.InstantiateMVars(e);
        if (e1.HasExprMVar || e1.HasLevelMVar)
        {
            throw new MetaException($"kernel type checker: the term has metavariables {e1}");
        }
        return KernelInfer(LCtx, e1, null) ?? throw new MetaException($"kernel type checker: the term uses a local declaration with metavariables {e1}");
    }

    // Kernel-checks the ground `e` in a kernel copy of `lctx` and returns its type, in Meta's free
    // variables, or null if `e` (or `expected`) depends on a declaration that is not ground. With
    // `expected`, also checks the type is kernel-defeq to it. A kernel rejection becomes a MetaException.
    private Expr? KernelInfer(LocalContext lctx, Expr e, Expr? expected)
    {
        var ngen = new NameGenerator(KernelCheckPrefix);
        var kctx = new KernelLocalContext();
        var toKernel = new Dictionary<FVarId, FVarExpr>();
        var toMeta = new Dictionary<FVarId, FVarExpr>();
        foreach (var decl in lctx.Decls)
        {
            var type = this.InstantiateMVars(decl.Type);
            var value = decl is LDecl l ? this.InstantiateMVars(l.Value) : null;
            if (type.HasExprMVar || type.HasLevelMVar || value is { HasExprMVar: true } || value is { HasLevelMVar: true })
            {
                continue;
            }
            if (Subst(type) is not { } kType || (value is not null && Subst(value) is null))
            {
                continue;
            }
            var kfvar = value is null
                ? kctx.MkLocalDecl(ngen, decl.UserName, kType, decl.BinderInfo)
                : kctx.MkLetDecl(ngen, decl.UserName, kType, Subst(value)!);
            toKernel[decl.FVarId] = kfvar;
            toMeta[kfvar.Id] = decl.ToExpr();
        }
        if (Subst(e) is not { } ke)
        {
            return null;
        }
        Expr? kExpected = null;
        if (expected is not null && (kExpected = Subst(expected)) is null)
        {
            return null;
        }
        try
        {
            var tc = new TypeChecker(Env, DefinitionSafety.Unsafe, localContext: kctx);
            var type = tc.Check(ke);
            if (kExpected is not null && !tc.IsDefEq(type, kExpected))
            {
                throw new MetaException($"kernel type checker: {e} has type {type} but is expected to have type {expected}");
            }
            return ExprOps.Replace(type, (x, _) => x is FVarExpr f && toMeta.TryGetValue(f.Id, out var m) ? m : null);
        }
        catch (KernelException ex)
        {
            throw new MetaException($"kernel type checker failed at {e}: {ex.Message}", ex);
        }

        Expr? Subst(Expr x)
        {
            bool ok = true;
            var r = ExprOps.Replace(x, (y, _) =>
            {
                if (!y.HasFVar)
                {
                    return y;
                }
                if (y is FVarExpr f)
                {
                    if (toKernel.TryGetValue(f.Id, out var k))
                    {
                        return k;
                    }
                    ok = false;
                    return y;
                }
                return null;
            });
            return ok ? r : null;
        }
    }

    // The debug check of DebugCheckAssignments: a ground value must kernel-check against a ground
    // type in the metavariable's local context.
    private void DebugCheckAssignment(MVarId mvarId, Expr val)
    {
        var v = this.InstantiateMVars(val);
        if (v.HasExprMVar || v.HasLevelMVar)
        {
            return;
        }
        var decl = GetMVarDecl(mvarId);
        var type = this.InstantiateMVars(decl.Type);
        var expected = type.HasExprMVar || type.HasLevelMVar ? null : type;
        try
        {
            KernelInfer(decl.LCtx, v, expected);
        }
        catch (MetaException ex)
        {
            throw new MetaException($"ill-typed assignment ?{mvarId} := {v}: {ex.Message}", ex);
        }
    }

    // Lean's Check.lean: checkAux and its helpers, for terms with metavariables.
    private void CheckAux(Expr e)
    {
        var visited = new HashSet<Expr>();
        Go(e);

        void Go(Expr e)
        {
            if (!visited.Add(e))
            {
                return;
            }
            Budget.Tick();
            switch (e)
            {
                case ForallExpr:
                    ForallTelescope(e, (xs, b) =>
                    {
                        foreach (var x in xs)
                        {
                            var t = GetFVarLocalDecl(x).Type;
                            GetLevel(t);
                            Go(t);
                        }
                        GetLevel(b);
                        Go(b);
                        return 0;
                    });
                    break;
                case LamExpr or LetExpr:
                    LambdaLetTelescope(e, (xs, b) =>
                    {
                        foreach (var x in xs)
                        {
                            var xDecl = GetFVarLocalDecl(x);
                            GetLevel(xDecl.Type);
                            Go(xDecl.Type);
                            if (xDecl is LDecl l)
                            {
                                if (!IsDefEq(l.Type, InferType(l.Value)))
                                {
                                    throw new MetaException($"invalid let declaration '{l.UserName}': the type of the value is not {l.Type}");
                                }
                                Go(l.Value);
                            }
                        }
                        Go(b);
                        return 0;
                    });
                    break;
                case ConstExpr c:
                    if (GetConstInfo(c.Name).LevelParams.Count != c.Levels.Count)
                    {
                        throw new MetaException($"incorrect number of universe levels {e}");
                    }
                    break;
                case AppExpr a:
                    Go(a.Fn);
                    Go(a.Arg);
                    CheckApp(a.Fn, a.Arg);
                    break;
                case MDataExpr m:
                    Go(m.Expr);
                    break;
                case ProjExpr p:
                    Go(p.Struct);
                    CheckProj(p);
                    break;
            }
        }

        void CheckApp(Expr f, Expr a)
        {
            if (Whnf(InferType(f)) is not ForallExpr fType)
            {
                throw FunctionExpected(Expr.App(f, a));
            }
            if (!IsDefEq(fType.BinderType, InferType(a)))
            {
                throw new MetaException($"application type mismatch: {a} is not of type {fType.BinderType} in {Expr.App(f, a)}");
            }
        }

        void CheckProj(ProjExpr p)
        {
            var structType = Whnf(InferType(p.Struct));
            var projType = InferType(p);
            if (IsProp(structType) && !IsProp(projType))
            {
                throw new MetaException($"invalid projection {p} from type {structType}");
            }
        }
    }
}
