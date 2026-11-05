using System.Collections.Immutable;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>How a local declaration is shown and treated (Lean's <c>LocalDeclKind</c>).</summary>
public enum LocalDeclKind : byte
{
    /// <summary>An ordinary hypothesis or local definition.</summary>
    Default,

    /// <summary>An implementation detail: hidden from the user and from tactics such as <c>assumption</c>.</summary>
    ImplDetail,

    /// <summary>An auxiliary declaration standing for a recursive reference to a global name.</summary>
    AuxDecl,
}

/// <summary>
/// A local declaration of Meta's local context (Lean's <c>LocalDecl</c>): a hypothesis
/// (<see cref="CDecl"/>) or a local definition (<see cref="LDecl"/>).
/// </summary>
/// <param name="Index">The position in the context; earlier declarations have smaller indices.</param>
/// <param name="FVarId">The free variable this declaration introduces.</param>
/// <param name="UserName">The display name.</param>
/// <param name="Type">The type.</param>
/// <param name="Kind">Whether the declaration is visible.</param>
public abstract record LocalDecl(int Index, FVarId FVarId, Name UserName, Expr Type, LocalDeclKind Kind)
{
    /// <summary>The binder annotation; always the default for a local definition.</summary>
    public abstract BinderInfo BinderInfo { get; }

    /// <summary>Whether this is an auxiliary declaration.</summary>
    public bool IsAuxDecl => Kind == LocalDeclKind.AuxDecl;

    /// <summary>Whether this declaration is an implementation detail (any kind but the default).</summary>
    public bool IsImplementationDetail => Kind != LocalDeclKind.Default;

    /// <summary>Whether this is a nondependent local definition (a <c>have</c>).</summary>
    public bool IsNondep => this is LDecl { Nondep: true };

    /// <summary>
    /// Whether this is a local definition whose value is visible; a nondependent one counts only
    /// with <paramref name="allowNondep"/> (Lean's <c>isLet</c>).
    /// </summary>
    public bool IsLet(bool allowNondep = false) => this is LDecl l && (!l.Nondep || allowNondep);

    /// <summary>The visible value of a local definition, or null (Lean's <c>value?</c>).</summary>
    public Expr? GetValue(bool allowNondep = false) => this is LDecl l && (!l.Nondep || allowNondep) ? l.Value : null;

    /// <summary>The free variable this declaration introduces.</summary>
    public FVarExpr ToExpr() => Expr.FVar(FVarId);

    /// <summary>Whether the type, or the value of a local definition, has an expression metavariable.</summary>
    public bool HasExprMVar => Type.HasExprMVar || (this is LDecl l && l.Value.HasExprMVar);
}

/// <summary>A hypothesis <c>(x : T)</c> (Lean's <c>LocalDecl.cdecl</c>).</summary>
/// <param name="Index">The position in the context.</param>
/// <param name="FVarId">The free variable.</param>
/// <param name="UserName">The display name.</param>
/// <param name="Type">The type.</param>
/// <param name="Info">The binder annotation used when the variable is abstracted.</param>
/// <param name="Kind">Whether the declaration is visible.</param>
public sealed record CDecl(int Index, FVarId FVarId, Name UserName, Expr Type, BinderInfo Info, LocalDeclKind Kind)
    : LocalDecl(Index, FVarId, UserName, Type, Kind)
{
    /// <inheritdoc/>
    public override BinderInfo BinderInfo => Info;
}

/// <summary>A local definition <c>(x : T := v)</c> (Lean's <c>LocalDecl.ldecl</c>).</summary>
/// <param name="Index">The position in the context.</param>
/// <param name="FVarId">The free variable.</param>
/// <param name="UserName">The display name.</param>
/// <param name="Type">The type.</param>
/// <param name="Value">The value.</param>
/// <param name="Nondep">
/// A <c>have</c>: locally the variable behaves as a hypothesis and its value is hidden.
/// </param>
/// <param name="Kind">Whether the declaration is visible.</param>
public sealed record LDecl(int Index, FVarId FVarId, Name UserName, Expr Type, Expr Value, bool Nondep, LocalDeclKind Kind)
    : LocalDecl(Index, FVarId, UserName, Type, Kind)
{
    /// <inheritdoc/>
    public override BinderInfo BinderInfo => BinderInfo.Default;
}

/// <summary>
/// Meta's local context: an ordered, persistent set of local declarations (a port of Lean 4's
/// <c>Lean/LocalContext.lean</c>). Goals snapshot it, and backtracking restores a snapshot by
/// reference, so it is immutable (KTD4).
/// </summary>
/// <remarks>
/// As in Lean, the declarations live in an array indexed by <see cref="LocalDecl.Index"/> in which
/// erased declarations leave holes, plus a map from free variable to declaration.
/// </remarks>
public sealed class LocalContext
{
    /// <summary>The empty context.</summary>
    public static readonly LocalContext Empty = new(
        ImmutableDictionary<FVarId, LocalDecl>.Empty,
        [],
        ImmutableDictionary<FVarId, Name>.Empty);

    private readonly ImmutableDictionary<FVarId, LocalDecl> _fvarIdToDecl;
    private readonly ImmutableList<LocalDecl?> _decls;
    private readonly ImmutableDictionary<FVarId, Name> _auxDeclToFullName;

    private LocalContext(
        ImmutableDictionary<FVarId, LocalDecl> fvarIdToDecl,
        ImmutableList<LocalDecl?> decls,
        ImmutableDictionary<FVarId, Name> auxDeclToFullName)
    {
        _fvarIdToDecl = fvarIdToDecl;
        _decls = decls;
        _auxDeclToFullName = auxDeclToFullName;
    }

    /// <summary>Whether the context has no declarations.</summary>
    public bool IsEmpty => _fvarIdToDecl.IsEmpty;

    /// <summary>The number of index slots, including holes left by erased declarations (Lean's <c>numIndices</c>).</summary>
    public int NumIndices => _decls.Count;

    /// <summary>The number of declarations.</summary>
    public int Size => _fvarIdToDecl.Count;

    /// <summary>The declarations in order.</summary>
    public IEnumerable<LocalDecl> Decls => DeclsFrom(0);

    /// <summary>The declarations in order, starting at index <paramref name="start"/>.</summary>
    public IEnumerable<LocalDecl> DeclsFrom(int start)
    {
        for (int i = start; i < _decls.Count; i++)
        {
            if (_decls[i] is { } d)
            {
                yield return d;
            }
        }
    }

    /// <summary>The declarations in reverse order.</summary>
    public IEnumerable<LocalDecl> DeclsReversed()
    {
        for (int i = _decls.Count - 1; i >= 0; i--)
        {
            if (_decls[i] is { } d)
            {
                yield return d;
            }
        }
    }

    /// <summary>Declares a hypothesis; <paramref name="fvarId"/> must be fresh.</summary>
    public LocalContext MkLocalDecl(FVarId fvarId, Name userName, Expr type, BinderInfo bi = BinderInfo.Default, LocalDeclKind kind = LocalDeclKind.Default) =>
        Push(new CDecl(_decls.Count, fvarId, userName, type, bi, kind), _auxDeclToFullName);

    /// <summary>Declares a local definition; <paramref name="fvarId"/> must be fresh.</summary>
    public LocalContext MkLetDecl(FVarId fvarId, Name userName, Expr type, Expr value, bool nondep = false, LocalDeclKind kind = LocalDeclKind.Default) =>
        Push(new LDecl(_decls.Count, fvarId, userName, type, value, nondep, kind), _auxDeclToFullName);

    /// <summary>Declares an auxiliary declaration standing for the global <paramref name="fullName"/>.</summary>
    public LocalContext MkAuxDecl(FVarId fvarId, Name userName, Expr type, Name fullName) =>
        Push(new CDecl(_decls.Count, fvarId, userName, type, BinderInfo.Default, LocalDeclKind.AuxDecl), _auxDeclToFullName.SetItem(fvarId, fullName));

    /// <summary>Appends <paramref name="newDecl"/>, renumbering it to the next index (Lean's <c>addDecl</c>).</summary>
    public LocalContext AddDecl(LocalDecl newDecl)
    {
        ArgumentNullException.ThrowIfNull(newDecl);
        return Push(newDecl with { Index = _decls.Count }, _auxDeclToFullName);
    }

    private LocalContext Push(LocalDecl decl, ImmutableDictionary<FVarId, Name> aux) =>
        new(_fvarIdToDecl.SetItem(decl.FVarId, decl), _decls.Add(decl), aux);

    /// <summary>The declaration of <paramref name="fvarId"/>, or null.</summary>
    public LocalDecl? Find(FVarId fvarId) => _fvarIdToDecl.TryGetValue(fvarId, out var d) ? d : null;

    /// <summary>The declaration of the free variable <paramref name="e"/>, or null.</summary>
    public LocalDecl? FindFVar(Expr e) => Find(FVarIdOf(e));

    /// <summary>The declaration of <paramref name="fvarId"/>.</summary>
    /// <exception cref="MetaException">The variable is not declared.</exception>
    public LocalDecl Get(FVarId fvarId) => Find(fvarId) ?? throw new MetaException($"unknown free variable '{fvarId}'");

    /// <summary>The declaration of the free variable <paramref name="e"/>.</summary>
    /// <exception cref="MetaException">The variable is not declared.</exception>
    public LocalDecl GetFVar(Expr e) => Get(FVarIdOf(e));

    /// <summary>Whether <paramref name="fvarId"/> is declared.</summary>
    public bool Contains(FVarId fvarId) => _fvarIdToDecl.ContainsKey(fvarId);

    /// <summary>Whether the free variable <paramref name="e"/> is declared.</summary>
    public bool ContainsFVar(Expr e) => Contains(FVarIdOf(e));

    /// <summary>The full global name of an auxiliary declaration, or null.</summary>
    public Name? GetAuxDeclFullName(FVarId fvarId) => _auxDeclToFullName.TryGetValue(fvarId, out var n) ? n : null;

    /// <summary>The declared free variables in order.</summary>
    public FVarId[] GetFVarIds() => [.. Decls.Select(d => d.FVarId)];

    /// <summary>The declared free variables in order, as terms.</summary>
    public Expr[] GetFVars() => [.. Decls.Select(d => (Expr)d.ToExpr())];

    /// <summary>Removes the declaration of <paramref name="fvarId"/>, if any (Lean's <c>erase</c>).</summary>
    public LocalContext Erase(FVarId fvarId)
    {
        if (!_fvarIdToDecl.TryGetValue(fvarId, out var decl))
        {
            return this;
        }
        return new(
            _fvarIdToDecl.Remove(fvarId),
            PopTailNone(_decls.SetItem(decl.Index, null)),
            decl.IsAuxDecl ? _auxDeclToFullName.Remove(fvarId) : _auxDeclToFullName);
    }

    /// <summary>Removes the last declaration (Lean's <c>pop</c>).</summary>
    public LocalContext Pop()
    {
        if (_decls.Count == 0 || _decls[^1] is not { } decl)
        {
            return this;
        }
        return new(
            _fvarIdToDecl.Remove(decl.FVarId),
            PopTailNone(_decls.RemoveAt(_decls.Count - 1)),
            decl.IsAuxDecl ? _auxDeclToFullName.Remove(decl.FVarId) : _auxDeclToFullName);
    }

    private static ImmutableList<LocalDecl?> PopTailNone(ImmutableList<LocalDecl?> decls)
    {
        while (decls.Count > 0 && decls[^1] is null)
        {
            decls = decls.RemoveAt(decls.Count - 1);
        }
        return decls;
    }

    /// <summary>The last declaration named <paramref name="userName"/>, or null (Lean's <c>findFromUserName?</c>).</summary>
    public LocalDecl? FindFromUserName(Name userName) => DeclsReversed().FirstOrDefault(d => d.UserName == userName);

    /// <summary>Whether some declaration is named <paramref name="userName"/>.</summary>
    public bool UsesUserName(Name userName) => FindFromUserName(userName) is not null;

    /// <summary>
    /// <paramref name="suggestion"/> if no declaration uses it, otherwise the first of
    /// <c>suggestion_1</c>, <c>suggestion_2</c>, … that is unused (Lean's <c>getUnusedName</c>).
    /// </summary>
    public Name GetUnusedName(Name suggestion)
    {
        ArgumentNullException.ThrowIfNull(suggestion);
        if (!UsesUserName(suggestion))
        {
            return suggestion;
        }
        for (int i = 1; ; i++)
        {
            var curr = suggestion.AppendIndexAfter(i);
            if (!UsesUserName(curr))
            {
                return curr;
            }
        }
    }

    /// <summary>The declaration in the last slot, or null if that slot is empty.</summary>
    public LocalDecl? LastDecl => _decls.Count == 0 ? null : _decls[^1];

    /// <summary>The declaration at index <paramref name="i"/>, or null for a hole.</summary>
    public LocalDecl? GetAt(int i) => _decls[i];

    /// <summary>Renames the declaration of <paramref name="fvarId"/>.</summary>
    public LocalContext SetUserName(FVarId fvarId, Name userName) => Replace(Get(fvarId) with { UserName = userName });

    /// <summary>Renames the last declaration named <paramref name="fromName"/>, if any.</summary>
    public LocalContext RenameUserName(Name fromName, Name toName) =>
        FindFromUserName(fromName) is { } decl ? Replace(decl with { UserName = toName }) : this;

    /// <summary>
    /// Replaces the declaration of <paramref name="fvarId"/> by <c>f(decl)</c>, which must keep its
    /// index and free variable and change its terms only up to definitional equality.
    /// </summary>
    public LocalContext ModifyLocalDecl(FVarId fvarId, Func<LocalDecl, LocalDecl> f)
    {
        ArgumentNullException.ThrowIfNull(f);
        return Find(fvarId) is { } decl ? Replace(f(decl)) : this;
    }

    /// <summary>Sets the kind of <paramref name="fvarId"/>'s declaration.</summary>
    public LocalContext SetKind(FVarId fvarId, LocalDeclKind kind) => ModifyLocalDecl(fvarId, d => d with { Kind = kind });

    /// <summary>Sets the binder annotation of <paramref name="fvarId"/>'s hypothesis.</summary>
    /// <exception cref="MetaException">The declaration is a local definition.</exception>
    public LocalContext SetBinderInfo(FVarId fvarId, BinderInfo bi) => ModifyLocalDecl(fvarId, d => d switch
    {
        CDecl c => c with { Info = bi },
        _ => throw new MetaException("unexpected let declaration"),
    });

    /// <summary>Sets the type of <paramref name="fvarId"/>'s declaration (to a definitionally equal one).</summary>
    public LocalContext SetType(FVarId fvarId, Expr type) => ModifyLocalDecl(fvarId, d => d with { Type = type });

    private LocalContext Replace(LocalDecl decl) =>
        new(_fvarIdToDecl.SetItem(decl.FVarId, decl), _decls.SetItem(decl.Index, decl), _auxDeclToFullName);

    /// <summary>
    /// Whether this context minus <paramref name="exceptFVars"/>, <c>(x₁ : A₁) … (xₙ : Aₙ)</c>, is
    /// embedded in order in <paramref name="other"/>, i.e. <paramref name="other"/> starts with
    /// <c>B₁* (x₁ : A₁) … Bₙ* (xₙ : Aₙ)</c> (Lean's <c>isSubPrefixOf</c>).
    /// </summary>
    public bool IsSubPrefixOf(LocalContext other, IReadOnlyList<Expr>? exceptFVars = null)
    {
        ArgumentNullException.ThrowIfNull(other);
        var a1 = _decls;
        var a2 = other._decls;
        int i = 0, j = 0;
        while (i < a1.Count)
        {
            if (a1[i] is not { } decl1 || (exceptFVars is not null && exceptFVars.Any(x => FVarIdOf(x) == decl1.FVarId)))
            {
                i++;
                continue;
            }
            while (true)
            {
                if (j >= a2.Count)
                {
                    return false;
                }
                if (a2[j] is { } decl2 && decl1.FVarId == decl2.FVarId)
                {
                    j++;
                    break;
                }
                j++;
            }
            i++;
        }
        return true;
    }

    /// <summary>
    /// Abstracts the free variables <paramref name="xs"/> of this context out of <paramref name="b"/>
    /// as lambdas or Pis, and lets for local definitions (Lean's <c>LocalContext.mkBinding</c>). It
    /// does not handle metavariables; <see cref="MetaM.MkLambdaFVars"/> does.
    /// </summary>
    public Expr MkBinding(bool isLambda, IReadOnlyList<Expr> xs, Expr b, bool usedLetOnly = true, bool generalizeNondepLet = false)
    {
        ArgumentNullException.ThrowIfNull(xs);
        b = b.Abstract(xs);
        for (int i = xs.Count - 1; i >= 0; i--)
        {
            switch (GetFVar(xs[i]))
            {
                case CDecl c:
                    b = MkBinder(isLambda, c.UserName, c.Type.AbstractRange(i, xs), b, c.Info);
                    break;
                case LDecl l when l.Nondep && generalizeNondepLet:
                    b = MkBinder(isLambda, l.UserName, l.Type.AbstractRange(i, xs), b, BinderInfo.Default);
                    break;
                case LDecl l:
                    b = !usedLetOnly || ExprOps.HasLooseBVar(b, 0)
                        ? Expr.Let(l.UserName, l.Type.AbstractRange(i, xs), l.Value.AbstractRange(i, xs), b, l.Nondep)
                        : ExprOps.LowerLooseBVars(b, 1, 1);
                    break;
            }
        }
        return b;
    }

    /// <summary><c>fun xs => b</c> for free variables of this context (Lean's <c>LocalContext.mkLambda</c>).</summary>
    public Expr MkLambda(IReadOnlyList<Expr> xs, Expr b, bool usedLetOnly = true, bool generalizeNondepLet = false) =>
        MkBinding(true, xs, b, usedLetOnly, generalizeNondepLet);

    /// <summary><c>∀ xs, b</c> for free variables of this context (Lean's <c>LocalContext.mkForall</c>).</summary>
    public Expr MkForall(IReadOnlyList<Expr> xs, Expr b, bool usedLetOnly = true, bool generalizeNondepLet = false) =>
        MkBinding(false, xs, b, usedLetOnly, generalizeNondepLet);

    private static Expr MkBinder(bool isLambda, Name n, Expr type, Expr body, BinderInfo bi) =>
        isLambda ? Expr.Lam(n, type, body, bi) : Expr.Forall(n, type, body, bi);

    internal static FVarId FVarIdOf(Expr e) =>
        e is FVarExpr f ? f.Id : throw new MetaException($"free variable expected, got '{e}'");
}
