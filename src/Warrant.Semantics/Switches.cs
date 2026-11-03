using Warrant.Cic;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>
/// <c>switch</c> (docs/m4/05, "switch"). Over a <c>[Closed]</c> enum it is the type's recursor with a constant motive, one
/// argument per constructor in declaration order (KTD9). Over an integer or an open enum it is a chain of <c>ite</c> tests
/// in source order, with the default last.
/// </summary>
internal sealed partial class BodyTranslator
{
    /// <summary>A switch expression.</summary>
    private Expr Switch(SwitchExpr s, Env env)
    {
        var scrutinee = Value(s.Scrutinee, env);
        var type = _types.Cic(s.Type);
        if (_types.IsClosed(s.Scrutinee.Type))
        {
            // Each constructor takes the value of the first arm that covers it; an arm covering several is copied.
            var members = _types.Closed(s.Scrutinee.Type).Members;
            var values = s.Arms.Select(a => Value(a.Value, env)).ToList();
            var minors = members.Select(m =>
            {
                int arm = FirstIndex(s.Arms, a => Covers(a.Pattern, m.Name, members));
                return arm >= 0 ? values[arm] : throw new TranslationException(null, $"the switch does not cover {m.Name}.");
            });
            return Recursor(s.Scrutinee.Type, type, minors, scrutinee);
        }

        // C# requires every arm after a discard to be unreachable, so the first discard is the last arm that can match.
        int discard = FirstIndex(s.Arms, a => a.Pattern is DiscardPattern);
        if (discard < 0)
        {
            throw new TranslationException(null, "a switch expression over an integer or open enum has no discard arm.");
        }
        var prim = _types.Underlying(s.Scrutinee.Type);
        var result = Value(s.Arms[discard].Value, env);
        for (int i = discard - 1; i >= 0; i--)
        {
            result = Operators.Ite(type, Matches(s.Arms[i].Pattern, scrutinee, prim, env), Value(s.Arms[i].Value, env), result);
        }
        return result;
    }

    /// <summary>
    /// A switch statement: one branch per section, plus an empty branch for the values no section matches when there is no
    /// default. A section ends in <c>return</c> or falls through to <paramref name="k"/> (extraction dropped its <c>break</c>).
    /// </summary>
    private Expr SwitchStatement(SwitchStmt s, Env env, Continuation k)
    {
        var scrutinee = Value(s.Scrutinee, env);
        var sections = s.Sections;
        int @default = FirstIndex(sections, IsDefault);
        var branches = sections.Select(section => (VirStmt)new BlockStmt(section.Body)).ToList();

        if (_types.IsClosed(s.Scrutinee.Type))
        {
            var members = _types.Closed(s.Scrutinee.Type).Members;
            var cover = members
                .Select(m => FirstIndex(sections, section => !IsDefault(section) && section.Labels.Any(l => Covers(l, m.Name, members))))
                .Select(i => i >= 0 ? i : @default)
                .ToList();
            if (cover.Contains(-1))
            {
                branches.Add(EmptyBlock);
                cover = [.. cover.Select(i => i >= 0 ? i : branches.Count - 1)];
            }
            return Branches(branches, (terms, type) => SharedRecursor(s.Scrutinee.Type, type, terms, cover, scrutinee), env, k);
        }

        if (@default >= 0 && sections[@default].Labels.Count > 1)
        {
            throw new TranslationException(null, "a default section with case labels is not supported.");
        }
        if (@default < 0)
        {
            branches.Add(EmptyBlock);
        }
        int fallback = @default >= 0 ? @default : branches.Count - 1;
        var prim = _types.Underlying(s.Scrutinee.Type);
        return Branches(
            branches,
            (terms, type) =>
            {
                var result = terms[fallback];
                for (int i = sections.Count - 1; i >= 0; i--)
                {
                    if (i != @default)
                    {
                        var test = sections[i].Labels.Select(l => Matches(l, scrutinee, prim, env)).Aggregate(Conditions.Or);
                        result = Operators.Ite(type, test, terms[i], result);
                    }
                }
                return result;
            },
            env,
            k);
    }

    /// <summary>
    /// The recursor over a closed type for a switch statement, whose branch terms are statements and their continuations: a
    /// branch used by several constructors is <c>let</c>-bound once rather than copied.
    /// </summary>
    private Expr SharedRecursor(VirType closed, Expr type, IReadOnlyList<Expr> terms, List<int> cover, Expr scrutinee)
    {
        var shared = new List<Expr>();
        var minors = terms.ToArray();
        for (int i = 0; i < minors.Length; i++)
        {
            if (cover.Count(c => c == i) > 1 && minors[i] is not FVarExpr)
            {
                var fvar = _lctx.MkLetDecl(_ngen, Name.From("branch"), type, minors[i]);
                shared.Add(fvar);
                minors[i] = fvar;
            }
        }
        return _lctx.MkLambda(shared, Recursor(closed, type, cover.Select(i => minors[i]), scrutinee));
    }

    /// <summary><c>@T.rec.{1} (fun _ =&gt; R) m₁ … mₙ t</c>: every M4 result type is in <c>Type</c>, so the motive's level is 1.</summary>
    internal static Expr Recursor(Expr closedType, string closedKey, Expr resultType, IEnumerable<Expr> minors, Expr major)
    {
        var motive = Expr.Lam(Init.Unused, closedType, Conditions.Closed(resultType));
        return Expr.App(Expr.Const(LeanNames.Recursor(closedKey), Level.One), [motive, .. minors, major]);
    }

    private Expr Recursor(VirType closed, Expr resultType, IEnumerable<Expr> minors, Expr major) =>
        Recursor(_types.Cic(closed), Key(closed), resultType, minors, major);

    /// <summary>Whether a pattern over a closed enum covers a member: a constant naming it, an <c>or</c>, or a discard.</summary>
    private static bool Covers(VirPattern pattern, string member, VirList<VirClosedMember> members) => pattern switch
    {
        DiscardPattern => true,
        ConstPattern { Value: MemberExpr m } => members.Any(x => x.Name == m.Name)
            ? string.Equals(m.Name, member, StringComparison.Ordinal)
            : throw new TranslationException(null, $"{m.Name} is not a member of the closed type."),
        OrPattern o => Covers(o.L, member, members) || Covers(o.R, member, members),
        _ => throw new TranslationException(null, $"unsupported pattern {pattern.GetType().Name} over a closed type."),
    };

    /// <summary>A pattern over an integer or open enum as a condition on the scrutinee, at the underlying type.</summary>
    private Condition Matches(VirPattern pattern, Expr scrutinee, VirPrimitive prim, Env env) => pattern switch
    {
        ConstPattern c => Conditions.Eq(prim, scrutinee, Value(c.Value, env)),
        RelationalPattern { Op: RelationalOp.Lt } r => Conditions.Lt(prim, scrutinee, Value(r.Value, env)),
        RelationalPattern { Op: RelationalOp.Le } r => Conditions.Le(prim, scrutinee, Value(r.Value, env)),
        RelationalPattern { Op: RelationalOp.Gt } r => Conditions.Lt(prim, Value(r.Value, env), scrutinee),
        RelationalPattern { Op: RelationalOp.Ge } r => Conditions.Le(prim, Value(r.Value, env), scrutinee),
        AndPattern a => Conditions.And(Matches(a.L, scrutinee, prim, env), Matches(a.R, scrutinee, prim, env)),
        OrPattern o => Conditions.Or(Matches(o.L, scrutinee, prim, env), Matches(o.R, scrutinee, prim, env)),
        NotPattern n => Conditions.Not(Matches(n.Operand, scrutinee, prim, env)),
        _ => throw new TranslationException(null, $"unsupported pattern {pattern.GetType().Name}."),
    };

    private static int FirstIndex<T>(IReadOnlyList<T> items, Func<T, bool> predicate)
    {
        for (int i = 0; i < items.Count; i++)
        {
            if (predicate(items[i]))
            {
                return i;
            }
        }
        return -1;
    }
}
