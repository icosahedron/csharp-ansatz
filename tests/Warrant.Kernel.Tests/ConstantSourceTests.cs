using System.Diagnostics.CodeAnalysis;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Kernel.Tests;

/// <summary>
/// The kernel's lazy base (M5b KTD18): an environment on an <see cref="IConstantSource"/> finds the source's constants
/// after its own, still rejects what it rejected before, and believes the source's quotient flag only when the source's
/// quotient constants are the kernel's own. The source here is a dictionary of the checked semantics bundle's constants.
/// </summary>
public sealed class ConstantSourceTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private static readonly Name QuotTheorem = Name.From("Test", "liftMk");

    [Fact]
    public void ADeclarationWhoseDependencyIsMissingFromTheSourceIsRejectedAsUnknown()
    {
        var env = new KernelEnvironment(Source(quotients: true, without: Name.From("Eq", "refl")));

        var error = Reject(env, QuotReductionTheorem());

        Assert.Contains("unknown constant 'Eq.refl'", error, StringComparison.Ordinal);
        Assert.Null(env.Find(QuotTheorem));
    }

    [Fact]
    public void AConstantTheSourceHoldsCannotBeDeclaredAgain()
    {
        var env = new KernelEnvironment(Source(quotients: true));
        var axiom = new AxiomDecl(new AxiomInfo(Name.From("Nat"), EquatableArray<Name>.Empty, Expr.Prop, false));

        var error = KernelThread.Run(() => Assert.Throws<KernelException>(() => Kernel.Add(env, axiom)).Message);

        Assert.Contains("'Nat' has already been declared", error, StringComparison.Ordinal);
    }

    [Fact]
    public void WithoutTheSourcesClaimQuotientsAreNotInitializedAndQuotientReductionDoesNotHappen()
    {
        var env = new KernelEnvironment(Source(quotients: false));

        Assert.False(env.IsQuotInitialized);
        Assert.Contains("type mismatch", Reject(env, QuotReductionTheorem()), StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void AClaimWhoseQuotientConstantsDifferFromTheKernelsIsNotBelieved()
    {
        // Quot.ind with another type: the claim stands, the constants do not match.
        var ind = (QuotInfo)bundle.Env.Get(Name.From("Quot", "ind"));
        var source = Source(quotients: true, replace: ind with { Type = Expr.Prop });
        var env = new KernelEnvironment(source);

        Assert.False(env.IsQuotInitialized);
        Assert.Contains("type mismatch", Reject(env, QuotReductionTheorem()), StringComparison.OrdinalIgnoreCase);
        // Nor can the package be added on top: its names are taken.
        Assert.Contains("has already been declared", KernelThread.Run(() =>
            Assert.Throws<KernelException>(() => Kernel.Add(env, new QuotDecl())).Message), StringComparison.Ordinal);
    }

    [Fact]
    public void AClaimWithTheKernelsOwnQuotientConstantsIsBelievedAndQuotientsReduce()
    {
        var env = new KernelEnvironment(Source(quotients: true));

        Assert.True(env.IsQuotInitialized);
        KernelThread.Run(() => Kernel.Add(env, QuotReductionTheorem()));
        Assert.IsType<TheoremInfo>(env.Find(QuotTheorem));
    }

    [Fact]
    public void ASourceBackedEnvironmentCountsTheSourceForksSeeItAndItDoesNotEnumerate()
    {
        var source = Source(quotients: true);
        var env = new KernelEnvironment(source);
        KernelThread.Run(() => Kernel.Add(env, QuotReductionTheorem()));
        env.Freeze();
        var fork = env.Fork();

        Assert.Equal(source.Count + 1, env.Count);
        Assert.Equal(source.Count + 1, fork.Count);
        Assert.NotNull(fork.Find(Name.From("Nat", "add")));
        Assert.NotNull(fork.Find(QuotTheorem));
        Assert.Null(fork.Find(Name.From("No", "such", "constant")));
        Assert.Throws<InvalidOperationException>(() => fork.Constants.Count());
        Assert.Throws<InvalidOperationException>(() => env.Constants.Count());
    }

    private DictionarySource Source(bool quotients, Name? without = null, ConstantInfo? replace = null)
    {
        var constants = bundle.Env.Constants.Where(c => c.Name != without).ToDictionary(c => c.Name);
        if (replace is not null)
        {
            constants[replace.Name] = replace;
        }
        return new DictionarySource(constants, quotients);
    }

    private static string Reject(KernelEnvironment env, KernelDeclaration declaration) =>
        KernelThread.Run(() => Assert.ThrowsAny<KernelException>(() => Kernel.Add(env, declaration)).Message);

    /// <summary>
    /// <c>theorem Test.liftMk.{u,v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) (h : ∀ a b, r a b → f a = f b)
    /// (a : α) : Quot.lift f h (Quot.mk r a) = f a := Eq.refl (f a)</c>, which holds only by quotient reduction.
    /// </summary>
    private static TheoremDecl QuotReductionTheorem()
    {
        var u = Level.Param(Name.From("u"));
        var v = Level.Param(Name.From("v"));
        Expr B(int i) => Expr.BVar(i);
        var anon = Name.From("x");
        var eq = Expr.Const(Name.From("Eq"), v);

        // Binder types, each under the binders before it.
        var alphaType = Expr.Sort(u);
        var rType = Expr.Forall(anon, B(0), Expr.Forall(anon, B(1), Expr.Prop));
        var betaType = Expr.Sort(v);
        var fType = Expr.Forall(anon, B(2), B(1));
        // [α r β f] ⊢ ∀ a b, r a b → f a = f b
        var hType = Expr.Forall(Name.From("a"), B(3),
            Expr.Forall(Name.From("b"), B(4),
                Expr.Forall(anon, Expr.App(B(4), B(1), B(0)),
                    Expr.App(eq, B(4), Expr.App(B(3), B(2)), Expr.App(B(3), B(1))))));
        var aType = B(4);
        // [α r β f h a] ⊢ Quot.lift f h (Quot.mk r a) = f a
        var mk = Expr.App(Expr.Const(Name.From("Quot", "mk"), u), B(5), B(4), B(0));
        var lift = Expr.App(Expr.Const(Name.From("Quot", "lift"), u, v), B(5), B(4), B(3), B(2), B(1), mk);
        var claim = Expr.App(eq, B(3), lift, Expr.App(B(2), B(0)));
        var proof = Expr.App(Expr.Const(Name.From("Eq", "refl"), v), B(3), Expr.App(B(2), B(0)));

        (string Name, Expr Type, BinderInfo Info)[] binders =
        [
            ("α", alphaType, BinderInfo.Implicit), ("r", rType, BinderInfo.Implicit), ("β", betaType, BinderInfo.Implicit),
            ("f", fType, BinderInfo.Default), ("h", hType, BinderInfo.Default), ("a", aType, BinderInfo.Default),
        ];
        Expr type = claim, value = proof;
        foreach (var (name, binderType, info) in binders.Reverse())
        {
            type = Expr.Forall(Name.From(name), binderType, type, info);
            value = Expr.Lam(Name.From(name), binderType, value, info);
        }
        return new TheoremDecl(new TheoremInfo(QuotTheorem, EquatableArray.Create(Name.From("u"), Name.From("v")), type, value, EquatableArray.Create(QuotTheorem)));
    }

    private sealed class DictionarySource(Dictionary<Name, ConstantInfo> constants, bool quotients) : IConstantSource
    {
        public int Count => constants.Count;

        public bool QuotientsInitialized => quotients;

        public bool TryGet(Name name, [NotNullWhen(true)] out ConstantInfo? constant) => constants.TryGetValue(name, out constant);
    }
}
