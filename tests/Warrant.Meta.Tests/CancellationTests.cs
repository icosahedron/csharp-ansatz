using System.Diagnostics;
using Warrant.Cic;
using Warrant.Kernel;
using static Warrant.Meta.Tests.InitTerms;
using static Warrant.Meta.Tests.MetaTestSupport;

namespace Warrant.Meta.Tests;

/// <summary>
/// Cancellation and deadlines inside Meta (M5b KTD12): a cancelled token stops a tactic, and the kernel running out of a
/// budget inside <see cref="MetaM.Check"/> stays a resource failure, which <c>first</c> and <c>try</c> do not recover
/// from. Each failure is paired with a control that differs only in the token or the deadline.
/// </summary>
public sealed class CancellationTests(AttributeSidecarFixture fixture) : IClassFixture<AttributeSidecarFixture>
{
    /// <summary><c>1 + 2</c>: a ground term, so <see cref="MetaM.Check"/> hands it to the kernel.</summary>
    private static readonly Expr Ground = NatAdd(NatLit(1), NatLit(2));

    [Fact]
    public void ASimpLoopStopsWithinASecondOfCancellation()
    {
        // simp with Nat.add_zero reversed, n = n + 0, rewrites x to x + 0, then that to x + 0 + 0, and so on: with no
        // step limit and unlimited fuel, only the token stops it.
        using var cts = new CancellationTokenSource();
        var m = fixture.NewMeta(new MetaLimits(long.MaxValue) { CancellationToken = cts.Token });
        var stopwatch = new Stopwatch();
        var ex = Assert.Throws<MetaResourceException>(() => KernelThread.Run(() =>
            m.WithLocalDeclD(N("x"), Nat, x =>
            {
                var loop = new SimpTheorems();
                loop.AddRange(m.MkSimpTheoremsFromConst(N("Nat.add_zero"), inverse: true));
                var context = DefaultSimpSet.Context(m, SimpConfig.Default with { MaxSteps = int.MaxValue }, loop);
                cts.CancelAfter(TimeSpan.FromMilliseconds(100));
                stopwatch.Start();
                return new Simplifier(m, context).Run(x);
            })));
        stopwatch.Stop();

        Assert.Contains("cancelled", ex.Message, StringComparison.Ordinal);
        Assert.True(stopwatch.Elapsed < TimeSpan.FromMilliseconds(1100), $"simp stopped {stopwatch.Elapsed} after it started");
    }

    [Fact]
    public void ACancellationInsideCheckIsNotAFailureFirstOrTryRecoverFrom()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var cancelled = KernelLimits.Interactive with { CancellationToken = cts.Token };

        var (m, t) = NewTactic(cancelled);
        var first = Assert.Throws<MetaResourceException>(() => t.First(() => m.Check(Ground), () => { }));
        Assert.Contains("cancelled", first.Message, StringComparison.Ordinal);
        Assert.IsType<KernelResourceException>(first.InnerException);
        Assert.Throws<MetaResourceException>(() => t.Try(() => m.Check(Ground)));
        Assert.Throws<MetaResourceException>(() => m.IsTypeCorrect(Ground));

        var (live, liveTactic) = NewTactic(KernelLimits.Interactive);
        Assert.True(liveTactic.First(() => live.Check(Ground), () => { }));
        Assert.True(live.IsTypeCorrect(Ground));
    }

    [Fact]
    public void ADeadlinePassedInsideCheckIsAResourceFailure()
    {
        var (m, t) = NewTactic(KernelLimits.Interactive with { Deadline = DateTimeOffset.UtcNow.AddMinutes(-1) });
        var ex = Assert.Throws<MetaResourceException>(() => t.Try(() => m.Check(Ground)));
        Assert.Contains("deadline", ex.Message, StringComparison.Ordinal);

        var (future, futureTactic) = NewTactic(KernelLimits.Interactive with { Deadline = DateTimeOffset.UtcNow.AddHours(1) });
        Assert.True(futureTactic.Try(() => future.Check(Ground)));
    }

    [Fact]
    public void MetaTakesItsDeadlineAndTokenToTheKernelByDefault()
    {
        using var cts = new CancellationTokenSource();
        var deadline = DateTimeOffset.UtcNow.AddHours(1);
        var m = fixture.NewMeta(new MetaLimits(1000) { Deadline = deadline, CancellationToken = cts.Token });
        Assert.Equal(deadline, m.KernelLimits.Deadline);
        Assert.Equal(cts.Token, m.KernelLimits.CancellationToken);
        Assert.Equal(KernelLimits.Interactive.Fuel, m.KernelLimits.Fuel);
    }

    // Meta has no deadline and a live token of its own, so only the kernel inside Check can run out.
    private (MetaM Meta, TacticM Tactic) NewTactic(KernelLimits kernel)
    {
        var m = new MetaM(fixture.Bundle.Fork()) { Attributes = fixture.Sidecar.Fork(), KernelLimits = kernel };
        return (m, new TacticM(m, []));
    }
}
