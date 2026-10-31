using LeanSharp.Cic;

namespace LeanSharp.Cic.Tests;

public class EnvTests
{
    private static ConstantDeclaration Axiom(string name) =>
        new(new AxiomInfo(Name.Parse(name), EquatableArray<Name>.Empty, Expr.Prop, false));

    [Fact]
    public void AddAndLookUp()
    {
        var env = new Env();
        env.Add(Axiom("A"));
        env.Add(Axiom("B"));
        Assert.Equal(2, env.ConstantCount);
        Assert.True(env.Contains(Name.Parse("A")));
        Assert.True(env.TryGet(Name.Parse("B"), out var b));
        Assert.Equal(ConstantKind.Axiom, b.Kind);
        Assert.Null(env.Find(Name.Parse("C")));
        Assert.Equal(2, env.Declarations.Count);
    }

    [Fact]
    public void RejectsDuplicatesAtomically()
    {
        var env = new Env();
        env.Add(Axiom("A"));
        var ex = Assert.Throws<DuplicateConstantException>(() => env.Add(Axiom("A")));
        Assert.Equal(Name.Parse("A"), ex.ConstantName);

        // An inductive block that repeats a name inside itself is rejected without partial effects.
        var nat = Name.Parse("N");
        var type = new InductiveInfo(nat, EquatableArray<Name>.Empty, Expr.Type, 0, 0,
            EquatableArray.Create(nat), EquatableArray.Create(nat), 0, false, false, false);
        var ctor = new ConstructorInfo(nat, EquatableArray<Name>.Empty, Expr.Const(nat), nat, 0, 0, 0, false);
        var block = new InductiveDeclaration(EquatableArray.Create(type), EquatableArray.Create(ctor), EquatableArray<RecursorInfo>.Empty);
        Assert.Throws<DuplicateConstantException>(() => env.Add(block));
        Assert.False(env.Contains(nat));
        Assert.Single(env.Declarations);
    }

    [Fact]
    public void ConstantInfosCompareStructurally()
    {
        Assert.Equal(Axiom("A"), Axiom("A"));
        Assert.NotEqual(Axiom("A"), Axiom("B"));
    }
}
