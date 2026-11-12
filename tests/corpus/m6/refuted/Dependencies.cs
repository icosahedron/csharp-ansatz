// M6 U14's refuted contracts with dependencies (KTD4, KTD9, KTD25, #96, #97), a compilation of its own: an Ensures that
// holds only through GetPayment's contract fails when the call asks for another id, or relies on SavePayment's empty
// contract, or on two calls agreeing, which the world threaded between them does not give, with or without a [ProofFor]
// script; a contract-class member whose Spec calls admit no result; and an awaited call that breaks its callee's Requires.
using System.Threading.Tasks;
using Warrant;

namespace Corpus.M6.Refuted.Dependencies;

public sealed record Payment(int Id, int Amount);

public interface IPaymentStore
{
    Task<Payment?> GetPayment(int id);
    Task SavePayment(Payment p);
}

[ContractFor(typeof(IPaymentStore))]
internal abstract class PaymentStoreContract : IPaymentStore
{
    public Task<Payment?> GetPayment(int id)
    {
        Spec.Ensures<Payment?>(r => r is null || r.Id == id);
        return default!;
    }

    public Task SavePayment(Payment p) => default!;
}

public sealed class Lookups(IPaymentStore store)
{
    [Verified]
    public async Task<bool> Neighbour(int id)
    {
        Spec.Ensures<bool>(r => r);
        var p = await store.GetPayment(id + 1);
        return p is null || p.Id == id;
    }

    [Verified]
    public async Task<bool> Saved(Payment p)
    {
        Spec.Ensures<bool>(r => r);
        await store.SavePayment(p);
        var q = await store.GetPayment(p.Id);
        return q is not null;
    }

    [Verified]
    public async Task<bool> Twice(int id)
    {
        Spec.Ensures<bool>(r => r);
        var a = await store.GetPayment(id);
        var b = await store.GetPayment(id);
        return (a is null) == (b is null);
    }

    [Verified]
    public async Task<bool> TwiceScripted(int id)
    {
        Spec.Ensures<bool>(r => r);
        var a = await store.GetPayment(id);
        var b = await store.GetPayment(id);
        return (a is null) == (b is null);
    }

    // Would close if the two calls agreed: one goal per case of the last call's result (`r`), each left to simp.
    [ProofFor(nameof(TwiceScripted))]
    static Proof TwiceScriptedProof() => Prove.Contract().By(Tactic.VcGen(), Tactic.AllGoals(Tactic.Try(Tactic.Cases("r"))), Tactic.AllGoals(Tactic.Simp()));
}

public interface ICounter
{
    int Count();
}

[ContractFor(typeof(ICounter))]
internal abstract class CounterContract : ICounter
{
    public int Count()
    {
        Spec.Ensures<int>(r => r > 0 && r < 0);
        return default!;
    }
}

public sealed class Tally(ICounter counter)
{
    [Verified]
    public int Size() => counter.Count();
}

// An awaited call that breaks its callee's precondition: x < 200 does not give Next's x < 100 (#228).
public static class Steps
{
    [Verified]
    public static async Task<int> Next(int x)
    {
        Spec.Requires(x < 100);
        return x + 1;
    }

    [Verified]
    public static async Task Run(int x)
    {
        Spec.Requires(x < 200);
        await Next(x);
    }
}
