using System.Diagnostics;
using Warrant.Cic;

namespace Warrant.Kernel.Tests;

/// <summary>
/// A cancelled token rejects like exhausted fuel (M5b KTD12): the kernel throws <see cref="KernelResourceException"/>, so
/// cancelling can only reject a declaration, never admit one. Each rejection is paired with a positive control that
/// differs only in the token, so a kernel rejecting everything cannot pass.
/// </summary>
public class CancellationTests(InitMediumFixture initMedium) : IClassFixture<InitMediumFixture>
{
    private static readonly EquatableArray<Name> NoParams = EquatableArray<Name>.Empty;

    private static Name N(string s) => Name.Parse(s);

    private static Expr C(string name, params Level[] levels) => Expr.Const(N(name), levels);

    private TheoremDecl AddCommCopy(string name)
    {
        var addComm = (TheoremInfo)initMedium.Env.Get(N("Nat.add_comm"));
        return new TheoremDecl(new TheoremInfo(N(name), NoParams, addComm.Type, addComm.Proof, [N(name)]));
    }

    private void Admit(KernelDeclaration d, KernelLimits limits) =>
        KernelThread.Run(() => Kernel.Add(initMedium.Env.Fork(), d, limits));

    [Fact]
    public void ACancelledTokenRejectsADeclarationTheKernelWouldAccept()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var ex = Assert.Throws<KernelResourceException>(
            () => Admit(AddCommCopy("test.cancelled"), KernelLimits.Interactive with { CancellationToken = cts.Token }));
        Assert.Contains("cancelled", ex.Message, StringComparison.Ordinal);

        using var live = new CancellationTokenSource();
        Admit(AddCommCopy("test.notCancelled"), KernelLimits.Interactive with { CancellationToken = live.Token });
        Admit(AddCommCopy("test.noToken"), KernelLimits.Interactive);
    }

    [Fact]
    public void ALiveTokenDoesNotChangeFuel()
    {
        var addComm = (TheoremInfo)initMedium.Env.Get(N("Nat.add_comm"));
        long FuelFor(KernelLimits limits) => KernelThread.Run(() =>
        {
            var tc = new TypeChecker(initMedium.Env, limits: limits);
            tc.IsDefEq(tc.Check(addComm.Proof, NoParams), addComm.Type);
            return tc.FuelUsed;
        });

        using var live = new CancellationTokenSource();
        Assert.Equal(FuelFor(KernelLimits.Interactive), FuelFor(KernelLimits.Interactive with { CancellationToken = live.Token }));
    }

    [Fact]
    public void ALongComputationCancelledAfter100MsStopsWithinASecond()
    {
        // decide (Nat.rec true (fun _ ih => ih) 10^9 = true): the kernel unfolds the recursor one step at a time, for tens
        // of seconds before even its stack runs out; with unlimited fuel, only the token stops it sooner.
        var motive = Expr.Lam(N("n"), C("Nat"), C("Bool"));
        var step = Expr.Lam(N("n"), C("Nat"), Expr.Lam(N("ih"), C("Bool"), Expr.BVar(0)));
        var rec = Expr.App(C("Nat.rec", Level.One), motive, C("Bool.true"), step, Expr.NatLit(1_000_000_000));
        var decide = Expr.App(C("instDecidableEqBool"), rec, C("Bool.true"));
        var unlimited = KernelLimits.Interactive with { Fuel = long.MaxValue };

        using var cts = new CancellationTokenSource(TimeSpan.FromMilliseconds(100));
        var stopwatch = Stopwatch.StartNew();
        var ex = Assert.Throws<KernelResourceException>(() => KernelThread.Run(() =>
            new TypeChecker(initMedium.Env, limits: unlimited with { CancellationToken = cts.Token }).Whnf(decide)));
        stopwatch.Stop();

        Assert.Contains("cancelled", ex.Message, StringComparison.Ordinal);
        Assert.True(stopwatch.Elapsed < TimeSpan.FromMilliseconds(1100), $"the kernel stopped {stopwatch.Elapsed} after it started");
    }
}
