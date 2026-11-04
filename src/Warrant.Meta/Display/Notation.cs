using System.Globalization;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>
/// How the notation printer names what the kernel environment cannot: translated constants and the
/// fields of translated records. Both come from the caller, which knows the translation; Meta does
/// not reference the translator (KTD7).
/// </summary>
/// <param name="Constant">
/// A constant's display name (for a translated constant, its C# name, as <c>Translation.Display</c>
/// gives it), or null to print the Lean name.
/// </param>
/// <param name="Field">
/// The name of field <c>i</c> (zero-based) of the structure type named, or null to print the
/// projection as Lean does, <c>s.(i+1)</c>.
/// </param>
public sealed record NotationNames(Func<Name, string?>? Constant = null, Func<Name, int, string?>? Field = null);

/// <summary>
/// A small notation printer for goals (KTD7): Lean's infix, prefix and binder notations at Lean's
/// precedences, with implicit and instance arguments hidden, instead of Lean's delaborator and
/// parenthesizer. Terms print on one line.
/// </summary>
/// <remarks>
/// <para>
/// Precedences are those of <c>Init/Notation.lean</c>, <c>Init/Core.lean</c> and the term
/// parsers: <c>↔</c> 20, <c>→</c> 25 (right), <c>∨</c> 30 (right), <c>∧</c> 35 (right),
/// <c>= ≠ ≤ &lt; ≥ &gt;</c> 50, <c>+ -</c> 65 (left), <c>* / %</c> 70 (left), prefix <c>-</c>
/// 75, <c>¬p</c> max with <c>p</c> at 40; an application is <c>leadPrec</c> with its arguments at
/// <c>argPrec</c>; <c>∀</c>, <c>∃</c>, <c>fun</c>, <c>if</c> and <c>let</c> are <c>leadPrec</c>
/// and extend as far right as they can.
/// </para>
/// <para>
/// A term is parenthesized when its precedence is below its slot's, or when a trailing operator
/// that follows it would be swallowed by its open right end (<c>(∀ x, p) ∧ q</c>,
/// <c>(¬a) = b</c>), which is the effect of Lean's parenthesizer.
/// </para>
/// </remarks>
public sealed class Notation
{
    private const int MaxPrec = 1024;
    private const int ArgPrec = 1023;
    private const int LeadPrec = 1022;

    /// <summary>The right end of a term that nothing that follows can extend.</summary>
    private const int Closed = int.MaxValue;

    /// <summary>A printed term: its text, its precedence, and the precedence of its open right end.</summary>
    /// <param name="Text">The text.</param>
    /// <param name="Prec">The precedence of the notation it is.</param>
    /// <param name="Right">An operator of this precedence or more that follows would extend the term's last part.</param>
    private readonly record struct Doc(string Text, int Prec, int Right);

    private sealed record Infix(string Op, int Prec, int Lhs, int Rhs, int Arity);

    /// <summary>Binary notations: the operands are the last two of <c>Arity</c> arguments.</summary>
    private static readonly Dictionary<Name, Infix> Infixes = new()
    {
        [Name.Parse("Iff")] = new(" ↔ ", 20, 21, 21, 2),
        [Name.Parse("Or")] = new(" ∨ ", 30, 31, 30, 2),
        [Name.Parse("And")] = new(" ∧ ", 35, 36, 35, 2),
        [Name.Parse("Eq")] = new(" = ", 50, 51, 51, 3),
        [Name.Parse("Ne")] = new(" ≠ ", 50, 51, 51, 3),
        [Name.Parse("LE.le")] = new(" ≤ ", 50, 51, 51, 4),
        [Name.Parse("LT.lt")] = new(" < ", 50, 51, 51, 4),
        [Name.Parse("GE.ge")] = new(" ≥ ", 50, 51, 51, 4),
        [Name.Parse("GT.gt")] = new(" > ", 50, 51, 51, 4),
        [Name.Parse("HAdd.hAdd")] = new(" + ", 65, 65, 66, 6),
        [Name.Parse("HSub.hSub")] = new(" - ", 65, 65, 66, 6),
        [Name.Parse("HMul.hMul")] = new(" * ", 70, 70, 71, 6),
        [Name.Parse("HDiv.hDiv")] = new(" / ", 70, 70, 71, 6),
        [Name.Parse("HMod.hMod")] = new(" % ", 70, 70, 71, 6),
        [Name.Parse("HPow.hPow")] = new(" ^ ", 75, 76, 75, 6),
    };

    /// <summary>Functions printed in field notation, <c>x.toInt</c>, on their only argument.</summary>
    private static readonly Dictionary<Name, string> FieldFunctions = new()
    {
        [Name.Parse("Int32.toInt")] = "toInt",
        [Name.Parse("Int64.toInt")] = "toInt",
        [Name.Parse("Int.toNat")] = "toNat",
    };

    private static readonly Name NotName = Name.Parse("Not");
    private static readonly Name NegName = Name.Parse("Neg.neg");
    private static readonly Name NatCastName = Name.Parse("Nat.cast");
    private static readonly Name OfNatName = Name.Parse("OfNat.ofNat");
    private static readonly Name IteName = Name.Parse("ite");
    private static readonly Name DiteName = Name.Parse("dite");
    private static readonly Name ExistsName = Name.Parse("Exists");

    private readonly KernelEnvironment _env;
    private readonly MetavarContext _mctx;
    private readonly NotationNames _names;
    private LocalContext _lctx = LocalContext.Empty;
    private int _nextBinder;

    /// <summary>A printer for terms over <paramref name="env"/>'s constants and <paramref name="mctx"/>'s metavariables.</summary>
    /// <param name="env">Supplies the binder infos that decide which arguments are hidden.</param>
    /// <param name="mctx">Instantiates assigned metavariables and names unassigned ones.</param>
    /// <param name="names">Display names for translated constants and record fields.</param>
    public Notation(KernelEnvironment env, MetavarContext mctx, NotationNames? names = null)
    {
        ArgumentNullException.ThrowIfNull(env);
        ArgumentNullException.ThrowIfNull(mctx);
        _env = env;
        _mctx = mctx;
        _names = names ?? new NotationNames();
    }

    /// <summary>Prints <paramref name="e"/>, whose free variables are declared in <paramref name="lctx"/>.</summary>
    /// <param name="e">The term; assigned metavariables are instantiated first.</param>
    /// <param name="lctx">Names the free variables.</param>
    /// <returns>The text.</returns>
    public string Print(Expr e, LocalContext lctx)
    {
        ArgumentNullException.ThrowIfNull(e);
        ArgumentNullException.ThrowIfNull(lctx);
        var saved = _lctx;
        _lctx = lctx;
        try
        {
            return Pp(_mctx.InstantiateMVars(e).Result).Text;
        }
        finally
        {
            _lctx = saved;
        }
    }

    // ---------------------------------------------------------------- terms

    private Doc Pp(Expr e)
    {
        switch (e)
        {
            case FVarExpr f:
                return Atom(_lctx.Find(f.Id) is { } d ? d.UserName.ToString() : f.Id.ToString());
            case MVarExpr mv:
                return Atom(MVarText(mv.Id));
            case BVarExpr b:
                return Atom("#" + b.Index.ToString(CultureInfo.InvariantCulture));
            case SortExpr s:
                return SortDoc(s.Level);
            case ConstExpr c:
                return Atom(ConstText(c.Name));
            case NatLitExpr n:
                return Atom(n.Value.ToString(CultureInfo.InvariantCulture));
            case StrLitExpr s:
                return Atom("\"" + s.Value.Replace("\\", "\\\\", StringComparison.Ordinal).Replace("\"", "\\\"", StringComparison.Ordinal) + "\"");
            case MDataExpr m:
                return Pp(m.Expr);
            case ProjExpr p:
                var field = _names.Field?.Invoke(p.TypeName, p.Index) ?? (p.Index + 1).ToString(CultureInfo.InvariantCulture);
                return new(Closed_(Pp(p.Struct), MaxPrec) + "." + field, MaxPrec, Closed);
            case AppExpr:
                return App(e);
            case LamExpr lam:
                return Lambda(lam);
            case ForallExpr pi:
                return Forall(pi);
            case LetExpr l:
                return Let(l);
            default:
                return Atom(e.ToString());
        }
    }

    private static Doc Atom(string text) => new(text, MaxPrec, Closed);

    private string ConstText(Name name) => _names.Constant?.Invoke(name) ?? name.ToString();

    private string MVarText(MVarId id) => _mctx.FindDecl(id) switch
    {
        { UserName.IsAnonymous: false } d => "?" + d.UserName,
        { } d => "?m." + d.Index.ToString(CultureInfo.InvariantCulture),
        null => "?" + id,
    };

    private static Doc SortDoc(Level level)
    {
        if (level.Kind == LevelKind.Zero)
        {
            return Atom("Prop");
        }
        if (level.Kind == LevelKind.Succ && level.Lhs!.Kind == LevelKind.Zero)
        {
            return Atom("Type");
        }
        var (keyword, arg) = level.Kind == LevelKind.Succ ? ("Type ", level.Lhs!) : ("Sort ", level);
        var text = arg.ToString();
        return new(keyword + (text.Contains(' ', StringComparison.Ordinal) ? $"({text})" : text), LeadPrec, Closed);
    }

    // ---------------------------------------------------------------- applications and notations

    private Doc App(Expr e)
    {
        var fn = e.GetAppFn();
        var args = e.GetAppArgs();
        if (fn is ConstExpr c && Notate(c.Name, args) is ({ } head, int used))
        {
            return used == args.Length ? head : Apply(head, args.AsSpan(used), null);
        }
        var type = fn switch
        {
            ConstExpr k => _env.Find(k.Name)?.Type,
            FVarExpr f => _lctx.Find(f.Id)?.Type,
            _ => null,
        };
        return Apply(Pp(fn), args, type);
    }

    /// <summary>
    /// <c>f a₁ … aₙ</c> with the arguments that <paramref name="fnType"/> binds implicitly or as
    /// instances left out.
    /// </summary>
    private Doc Apply(Doc fn, ReadOnlySpan<Expr> args, Expr? fnType)
    {
        var parts = new List<string> { Closed_(fn, MaxPrec) };
        foreach (var arg in args)
        {
            bool explicitArg = true;
            if (fnType is ForallExpr pi)
            {
                explicitArg = pi.BinderInfo == BinderInfo.Default;
                fnType = pi.Body;
            }
            else
            {
                fnType = null;
            }
            if (explicitArg)
            {
                parts.Add(Closed_(Pp(arg), ArgPrec));
            }
        }
        return parts.Count == 1 ? fn : new(string.Join(' ', parts), LeadPrec, Closed);
    }

    /// <summary>The notation for <c>name args</c>, and how many arguments it consumes; null if none applies.</summary>
    private (Doc Doc, int Used)? Notate(Name name, Expr[] args)
    {
        if (Infixes.TryGetValue(name, out var op) && args.Length >= op.Arity)
        {
            var lhs = Pp(args[op.Arity - 2]);
            var rhs = Pp(args[op.Arity - 1]);
            var (rhsText, rhsRight) = Slot(rhs, op.Rhs, followedBy: null);
            var text = Slot(lhs, op.Lhs, followedBy: op.Prec).Text + op.Op + rhsText;
            return (new(text, op.Prec, Math.Min(op.Rhs, rhsRight)), op.Arity);
        }
        if (name == NotName && args.Length >= 1)
        {
            return (Prefix("¬", MaxPrec, 40, Pp(args[0])), 1);
        }
        if (name == NegName && args.Length >= 3)
        {
            return (Prefix("-", 75, 75, Pp(args[2])), 3);
        }
        if (name == NatCastName && args.Length >= 3)
        {
            // Lean's coercion arrow, which omega's messages show for Nat atoms.
            return (Prefix("↑", MaxPrec, MaxPrec, Pp(args[2])), 3);
        }
        if (name == OfNatName && args.Length >= 3 && args[1] is NatLitExpr n)
        {
            return (Atom(n.Value.ToString(CultureInfo.InvariantCulture)), 3);
        }
        if (name == IteName && args.Length >= 5)
        {
            return (IfThenElse(null, Pp(args[1]), Pp(args[3]), Pp(args[4])), 5);
        }
        if (name == DiteName && args.Length >= 5 && args[3] is LamExpr t && args[4] is LamExpr f)
        {
            var hName = Fresh(t.BinderName, t.Body);
            var cond = Pp(args[1]);
            var thenDoc = WithBinder(hName, t, x => Pp(ExprOps.Instantiate(t.Body, x)));
            var elseDoc = WithBinder(hName, f, x => Pp(ExprOps.Instantiate(f.Body, x)));
            return (IfThenElse(hName, cond, thenDoc, elseDoc), 5);
        }
        if (name == ExistsName && args.Length >= 2 && args[1] is LamExpr)
        {
            return (Exists(args[1]), 2);
        }
        if (FieldFunctions.TryGetValue(name, out var field) && args.Length >= 1)
        {
            return (new(Closed_(Pp(args[0]), MaxPrec) + "." + field, MaxPrec, Closed), 1);
        }
        return null;
    }

    private static Doc Prefix(string op, int prec, int argPrec, Doc arg)
    {
        var (text, right) = Slot(arg, argPrec, followedBy: null);
        var sep = op == "-" && text.StartsWith('-') ? " " : "";
        return new(op + sep + text, prec, Math.Min(argPrec, right));
    }

    private static Doc IfThenElse(string? hyp, Doc cond, Doc thenDoc, Doc elseDoc) =>
        new($"if {(hyp is null ? "" : hyp + " : ")}{cond.Text} then {thenDoc.Text} else {elseDoc.Text}", LeadPrec, Math.Min(0, elseDoc.Right));

    // ---------------------------------------------------------------- binders

    private Doc Exists(Expr pred)
    {
        var names = new List<string>();
        return Scoped(() =>
        {
            Expr body = pred;
            while (true)
            {
                var lam = (LamExpr)body;
                var name = Fresh(lam.BinderName, lam.Body);
                names.Add(name);
                var x = Push(name, lam);
                body = ExprOps.Instantiate(lam.Body, x);
                if (body is AppExpr && body.GetAppFn() is ConstExpr { Name: var n } && n == ExistsName && body.GetAppNumArgs() == 2 && body.GetAppArgs()[1] is LamExpr next)
                {
                    body = next;
                    continue;
                }
                var doc = Pp(body);
                return new Doc($"∃ {string.Join(' ', names)}, {doc.Text}", LeadPrec, Math.Min(0, doc.Right));
            }
        });
    }

    private Doc Lambda(LamExpr lam)
    {
        var names = new List<string>();
        return Scoped(() =>
        {
            Expr body = lam;
            while (body is LamExpr l)
            {
                var name = Fresh(l.BinderName, l.Body);
                names.Add(name);
                body = ExprOps.Instantiate(l.Body, Push(name, l));
            }
            var doc = Pp(body);
            return new Doc($"fun {string.Join(' ', names)} => {doc.Text}", LeadPrec, Math.Min(0, doc.Right));
        });
    }

    /// <summary>
    /// <c>A → B</c> for a nondependent explicit binder, otherwise <c>∀</c> over the run of binders
    /// that are not arrows, consecutive ones with the same type and annotation grouped as
    /// <c>(a b : T)</c>.
    /// </summary>
    private Doc Forall(ForallExpr pi)
    {
        if (IsArrow(pi))
        {
            var lhs = Pp(pi.BinderType);
            var rhs = Pp(ExprOps.LowerLooseBVars(pi.Body, 1, 1));
            var (rhsText, rhsRight) = Slot(rhs, 25, followedBy: null);
            return new(Slot(lhs, 26, followedBy: 25).Text + " → " + rhsText, 25, Math.Min(25, rhsRight));
        }
        return Scoped(() =>
        {
            var groups = new List<(List<string> Names, BinderInfo Info, Expr Type)>();
            Expr body = pi;
            while (body is ForallExpr b && !IsArrow(b))
            {
                var name = Fresh(b.BinderName, b.Body);
                if (groups.Count > 0 && groups[^1].Info == b.BinderInfo && groups[^1].Type == b.BinderType)
                {
                    groups[^1].Names.Add(name);
                }
                else
                {
                    groups.Add(([name], b.BinderInfo, b.BinderType));
                }
                body = ExprOps.Instantiate(b.Body, Push(name, b));
            }
            var binders = string.Join(' ', groups.Select(g =>
            {
                var (open, close) = g.Info switch
                {
                    BinderInfo.Implicit => ("{", "}"),
                    BinderInfo.StrictImplicit => ("⦃", "⦄"),
                    BinderInfo.InstImplicit => ("[", "]"),
                    _ => ("(", ")"),
                };
                return $"{open}{string.Join(' ', g.Names)} : {Pp(g.Type).Text}{close}";
            }));
            var doc = Pp(body);
            return new Doc($"∀ {binders}, {doc.Text}", LeadPrec, Math.Min(0, doc.Right));
        });
    }

    private static bool IsArrow(ForallExpr pi) => pi.BinderInfo == BinderInfo.Default && !ExprOps.HasLooseBVar(pi.Body, 0);

    private Doc Let(LetExpr l)
    {
        var name = Fresh(l.BinderName, l.Body);
        var value = Pp(l.Value);
        return Scoped(() =>
        {
            var x = Expr.FVar(NextFVarId());
            _lctx = _lctx.MkLetDecl(x.Id, Name.Parse(name), l.BinderType, l.Value);
            var doc = Pp(ExprOps.Instantiate(l.Body, x));
            return new Doc($"let {name} := {value.Text}; {doc.Text}", LeadPrec, Math.Min(0, doc.Right));
        });
    }

    /// <summary>Runs <paramref name="k"/>, which may declare bound variables, and drops them afterwards.</summary>
    private Doc Scoped(Func<Doc> k)
    {
        var saved = _lctx;
        try
        {
            return k();
        }
        finally
        {
            _lctx = saved;
        }
    }

    private T WithBinder<T>(string name, BindingExpr b, Func<Expr, T> k)
    {
        var saved = _lctx;
        try
        {
            return k(Push(name, b));
        }
        finally
        {
            _lctx = saved;
        }
    }

    /// <summary>Declares the bound variable of <paramref name="b"/> as <paramref name="name"/> and returns it.</summary>
    private FVarExpr Push(string name, BindingExpr b)
    {
        var x = Expr.FVar(NextFVarId());
        _lctx = _lctx.MkLocalDecl(x.Id, Name.Parse(name), b.BinderType, b.BinderInfo);
        return x;
    }

    private FVarId NextFVarId() => new(Name.From("_pp").Append((ulong)_nextBinder++));

    /// <summary>
    /// The name to show for a binder: its own, unless the body mentions a variable already shown by
    /// that name, in which case the first unused <c>name_i</c> (Lean's <c>pp.safeShadowing</c> and
    /// <c>getUnusedName</c>).
    /// </summary>
    private string Fresh(Name binderName, Expr body)
    {
        var suggestion = binderName.IsAnonymous ? Name.From("x") : binderName;
        bool captures = ExprOps.Find(body, (e, _) => e is FVarExpr f && _lctx.Find(f.Id)?.UserName == suggestion) is not null;
        return (captures ? _lctx.GetUnusedName(suggestion) : suggestion).ToString();
    }

    // ---------------------------------------------------------------- parentheses

    /// <summary>
    /// <paramref name="d"/> in a slot of precedence <paramref name="prec"/>, followed by an operator
    /// of precedence <paramref name="followedBy"/> if any; returns the text and the right end it
    /// leaves open.
    /// </summary>
    private static (string Text, int Right) Slot(Doc d, int prec, int? followedBy) =>
        d.Prec < prec || (followedBy is int q && q >= d.Right) ? ($"({d.Text})", Closed) : (d.Text, d.Right);

    /// <summary><paramref name="d"/> where nothing may extend it: an application's head or argument, a projected term.</summary>
    private static string Closed_(Doc d, int prec) =>
        d.Prec < prec || d.Right != Closed ? $"({d.Text})" : d.Text;
}
