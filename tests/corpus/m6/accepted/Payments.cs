// Design §5.2's payment example (M6 U18): ProcessPayment calls IPaymentStore through a never-assigned primary-constructor
// parameter, and PaymentStoreContract states what the store is assumed to do (KTD9, KTD10, KTD22).
using System.Threading.Tasks;
using Warrant;

namespace Corpus.M6.Payments;

public enum PaymentStatus { Pending, Processed }

public enum PaymentResult { Valid, Invalid }

public enum Result { Success, InvalidId, NotFound, Invalid }

public sealed record Payment(int Id, decimal Amount, PaymentStatus Status);

public interface IPaymentStore
{
    Task<Payment?> GetPayment(int id);
    Task SavePayment(Payment p);
}

// Assumed behaviour of the external dependency. Nothing here is verified; everything here is reported as an assumption.
[ContractFor(typeof(IPaymentStore))]
file abstract class PaymentStoreContract : IPaymentStore
{
    public Task<Payment?> GetPayment(int id)
    {
        Spec.Ensures<Payment?>(r => r is null || r.Id == id);
        return default!;
    }

    public Task SavePayment(Payment p) => default!;   // no guarantees assumed
}

public sealed class PaymentService(IPaymentStore store)
{
    [Verified]
    public static PaymentResult Validate(Payment payment) =>
        payment.Amount > 0m ? PaymentResult.Valid : PaymentResult.Invalid;

    [Verified]
    public async Task<Result> ProcessPayment(int paymentId)
    {
        Spec.Ensures<Result>(r => r != Result.Success || paymentId > 0);

        if (paymentId <= 0) return Result.InvalidId;

        var payment = await store.GetPayment(paymentId);
        if (payment is null) return Result.NotFound;

        if (Validate(payment) != PaymentResult.Valid) return Result.Invalid;

        await store.SavePayment(payment with { Status = PaymentStatus.Processed });
        return Result.Success;
    }
}

// An Ensures that holds only through GetPayment's contract (M6 U20, #97): nothing here says what the store returns.
public sealed class PaymentLookup(IPaymentStore store)
{
    [Verified]
    public async Task<bool> Found(int id)
    {
        Spec.Ensures<bool>(r => r);
        var p = await store.GetPayment(id);
        return p is null || p.Id == id;
    }

    // #226: two field reads after the null test, each its own case of the result; the contract's fact is about the first.
    [Verified]
    public async Task<int> IdIfPending(int id)
    {
        Spec.Ensures<int>(r => r == 0 || r == id);
        var p = await store.GetPayment(id);
        if (p is null || p.Status != PaymentStatus.Pending) return 0;
        return p.Id;
    }
}
