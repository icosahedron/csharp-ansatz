using Warrant.Cic;

namespace Warrant.Kernel;

/// <summary>Generates fresh names <c>prefix.1</c>, <c>prefix.2</c>, … (Lean's <c>name_generator</c>).</summary>
public sealed class NameGenerator(Name prefix)
{
    private ulong _next;

    /// <summary>The next fresh name.</summary>
    public Name Next() => prefix.Append(++_next);
}

/// <summary>A free variable's declaration: a hypothesis <c>(x : T)</c> or a local definition <c>(x : T := v)</c>.</summary>
/// <param name="Id">The variable's identity.</param>
/// <param name="UserName">The display name.</param>
/// <param name="Type">The type.</param>
/// <param name="Value">The value, for a local definition.</param>
/// <param name="BinderInfo">The binder annotation used when the variable is abstracted back into a binder.</param>
public sealed record LocalDecl(FVarId Id, Name UserName, Expr Type, Expr? Value, BinderInfo BinderInfo);

/// <summary>
/// The kernel's local context: declarations of the free variables introduced when going under
/// binders. A port of Lean 4's <c>local_ctx</c>.
/// </summary>
/// <remarks>
/// Free-variable names are globally unique (they come from a <see cref="NameGenerator"/>) and each
/// variable keeps one type for its lifetime, so declarations are only ever added. Lean restores the
/// context after leaving a binder to keep it small; keeping extra entries is harmless.
/// </remarks>
public sealed class LocalContext
{
    private readonly LocalContext? _parent;
    private readonly Dictionary<FVarId, LocalDecl> _decls = [];

    /// <summary>Creates an empty context.</summary>
    public LocalContext()
    {
    }

    /// <summary>
    /// Creates a context that sees <paramref name="parent"/>'s declarations but keeps its own
    /// additions (like copying a Lean <c>local_ctx</c>).
    /// </summary>
    public LocalContext(LocalContext parent) => _parent = parent ?? throw new ArgumentNullException(nameof(parent));

    /// <summary>Declares a fresh hypothesis and returns its free variable.</summary>
    public FVarExpr MkLocalDecl(NameGenerator ngen, Name userName, Expr type, BinderInfo binderInfo = BinderInfo.Default)
    {
        var id = new FVarId(ngen.Next());
        _decls.Add(id, new LocalDecl(id, userName, type, null, binderInfo));
        return Expr.FVar(id);
    }

    /// <summary>Declares a fresh local definition and returns its free variable.</summary>
    public FVarExpr MkLetDecl(NameGenerator ngen, Name userName, Expr type, Expr value)
    {
        var id = new FVarId(ngen.Next());
        _decls.Add(id, new LocalDecl(id, userName, type, value, BinderInfo.Default));
        return Expr.FVar(id);
    }

    /// <summary>Looks up a free variable's declaration.</summary>
    public LocalDecl? Find(FVarId id) => _decls.TryGetValue(id, out var d) ? d : _parent?.Find(id);

    /// <summary>Looks up a free variable's declaration.</summary>
    /// <exception cref="KernelException">The variable is unknown.</exception>
    public LocalDecl Get(Expr fvar) =>
        Find(((FVarExpr)fvar).Id) ?? throw new KernelException($"unknown free variable '{((FVarExpr)fvar).Id}'");

    /// <summary>Abstracts <paramref name="fvars"/> out of <paramref name="body"/> as Pi binders (let binders for local definitions).</summary>
    public Expr MkPi(IReadOnlyList<Expr> fvars, Expr body, bool removeDeadLet = false) => MkBinding(false, fvars, body, removeDeadLet);

    /// <summary>Abstracts <paramref name="fvars"/> out of <paramref name="body"/> as lambda binders (let binders for local definitions).</summary>
    public Expr MkLambda(IReadOnlyList<Expr> fvars, Expr body, bool removeDeadLet = false) => MkBinding(true, fvars, body, removeDeadLet);

    /// <summary>Abstracts one free variable as a Pi binder.</summary>
    public Expr MkPi(Expr fvar, Expr body) => MkBinding(false, [fvar], body, false);

    /// <summary>Abstracts one free variable as a lambda binder.</summary>
    public Expr MkLambda(Expr fvar, Expr body) => MkBinding(true, [fvar], body, false);

    private Expr MkBinding(bool isLambda, IReadOnlyList<Expr> fvars, Expr body, bool removeDeadLet)
    {
        var arr = fvars as Expr[] ?? [.. fvars];
        var r = ExprOps.Abstract(body, arr);
        for (int i = arr.Length - 1; i >= 0; i--)
        {
            var decl = Get(arr[i]);
            var prefix = arr.AsSpan(0, i);
            if (decl.Value is { } value)
            {
                if (!removeDeadLet || ExprOps.HasLooseBVar(r, 0))
                {
                    r = Expr.Let(decl.UserName, ExprOps.Abstract(decl.Type, prefix), ExprOps.Abstract(value, prefix), r);
                }
                else
                {
                    r = ExprOps.LowerLooseBVars(r, 1, 1);
                }
            }
            else if (isLambda)
            {
                r = Expr.Lam(decl.UserName, ExprOps.Abstract(decl.Type, prefix), r, decl.BinderInfo);
            }
            else
            {
                r = Expr.Forall(decl.UserName, ExprOps.Abstract(decl.Type, prefix), r, decl.BinderInfo);
            }
        }
        return r;
    }
}
