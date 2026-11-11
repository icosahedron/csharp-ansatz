using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics;

/// <summary>
/// Type units (docs/m4/05, "Types" and "Equality on records and closed types", KTD9 and KTD10):
/// an open enum is an <c>abbrev</c> of its underlying type with an <c>abbrev</c> constant per member; a closed type is an
/// inductive with one nullary constructor per member plus <c>$index</c>; a sealed record is an inductive with the single
/// constructor <c>$mk</c> plus <c>$eq</c>.
/// </summary>
internal static class TypeDeclarations
{
    /// <summary>The declarations of a type unit, in the order they must be admitted.</summary>
    /// <param name="unit">The type unit.</param>
    /// <param name="types">The type table.</param>
    /// <param name="regular">The <c>regular</c> hint Lean would give a definition with this value.</param>
    public static List<KernelDeclaration> Translate(VirUnit unit, TypeTable types, Func<Expr, ReducibilityHints> regular)
    {
        var name = LeanNames.ForKey(unit.Key);
        var self = Expr.Const(name);
        switch (unit.Definition)
        {
            case EnumDefinition e:
                {
                    var prim = types.Underlying(e.Underlying);
                    if (prim is not (VirPrimitive.Int32 or VirPrimitive.Int64))
                    {
                        throw new TranslationException(unit.Key, "an enum's underlying type must be int or long.");
                    }
                    var result = new List<KernelDeclaration> { Abbrev(name, Expr.Type, Literals.Type(prim)) };
                    result.AddRange(e.Members.Select(m => Abbrev(LeanNames.Member(unit.Key, m.Name), self, Literals.Of(prim, m.Value))));
                    return result;
                }
            case ClosedDefinition c:
                {
                    var ctors = c.Members.Select(m => new InductiveConstructor(LeanNames.Member(unit.Key, m.Name), self));
                    var lctx = new LocalContext();
                    var o = lctx.MkLocalDecl(new NameGenerator(Name.From("_warrant")), Name.From("o"), self);
                    var minors = c.Members.Select((_, i) => (Expr)Expr.NatLit(i));
                    var index = lctx.MkLambda([o], BodyTranslator.Recursor(self, unit.Key, Init.Nat, minors, o));
                    return [Inductive(name, ctors), Definition(LeanNames.Index(unit.Key), lctx.MkPi([o], Init.Nat), index, regular)];
                }
            case RecordDefinition r:
                {
                    Expr ctorType = self;
                    for (int i = r.Fields.Count - 1; i >= 0; i--)
                    {
                        ctorType = Expr.Forall(Name.From(r.Fields[i].Name), types.Cic(r.Fields[i].Type), Conditions.Closed(ctorType));
                    }
                    var ctor = new InductiveConstructor(LeanNames.Constructor(unit.Key), ctorType);
                    return [Inductive(name, [ctor]), Equality(unit.Key, r, types, regular)];
                }
            default:
                throw new TranslationException(unit.Key, "a type unit has no definition.");
        }
    }

    /// <summary>
    /// <c>R.$eq a b</c>: the fields compared in order and joined with <c>Bool.and</c>, as the compiler-generated
    /// <c>Equals</c> does. An integer, <c>bool</c> or open-enum field is <c>decide (a.f = b.f)</c> at its underlying type, a
    /// <c>decimal</c> field compares values, <c>decide (Warrant.Decimal.eq a.f b.f)</c> (M6 KTD7, so <c>1.0m</c> and
    /// <c>1.00m</c> fields are equal, as <c>decimal.Equals</c> makes them), a record field uses that record's <c>$eq</c>, and
    /// a closed field compares <c>$index</c> values with <c>Nat.beq</c>.
    /// </summary>
    private static DefinitionDecl Equality(string key, RecordDefinition record, TypeTable types, Func<Expr, ReducibilityHints> regular)
    {
        var name = LeanNames.ForKey(key);
        var self = Expr.Const(name);
        var lctx = new LocalContext();
        var ngen = new NameGenerator(Name.From("_warrant"));
        var a = lctx.MkLocalDecl(ngen, Name.From("a"), self);
        var b = lctx.MkLocalDecl(ngen, Name.From("b"), self);
        Expr? body = null;
        for (int i = 0; i < record.Fields.Count; i++)
        {
            var type = record.Fields[i].Type;
            var fa = Expr.Proj(name, i, a);
            var fb = Expr.Proj(name, i, b);
            Expr same;
            if (types.IsRecord(type))
            {
                same = Expr.App(Expr.Const(LeanNames.Equality(((RefType)type).Key)), fa, fb);
            }
            else if (types.IsClosed(type))
            {
                var index = Expr.Const(LeanNames.Index(((RefType)type).Key));
                same = Operators.NatBeq(Expr.App(index, fa), Expr.App(index, fb));
            }
            else
            {
                same = Operators.Decide(Conditions.Eq(types.Underlying(type), fa, fb));
            }
            body = body is null ? same : Operators.And(body, same);
        }
        return Definition(LeanNames.Equality(key), lctx.MkPi([a, b], Init.Bool), lctx.MkLambda([a, b], body ?? Init.True), regular);
    }

    private static InductiveDecl Inductive(Name name, IEnumerable<InductiveConstructor> ctors) =>
        new([], 0, [new InductiveType(name, Expr.Type, ctors.ToEquatableArray())], false);

    private static DefinitionDecl Abbrev(Name name, Expr type, Expr value) =>
        new(new DefinitionInfo(name, [], type, value, ReducibilityHints.Abbrev, DefinitionSafety.Safe, [name]));

    internal static DefinitionDecl Definition(Name name, Expr type, Expr value, Func<Expr, ReducibilityHints> regular) =>
        new(new DefinitionInfo(name, [], type, value, regular(value), DefinitionSafety.Safe, [name]));
}
