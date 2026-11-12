// M6 U18's dependencies, contract classes and async methods (KTD9, KTD10, KTD22): a readonly field of an interface that
// inherits IDisposable, a Task<Order?> result that is nullable once awaited (#171), a void and a synchronous member, an
// abstract contract member, a ValueTask, a member with an unmodelled type that nothing calls, and verified async methods.
using System;
using System.Threading.Tasks;
using Warrant;

namespace Corpus.M6.Dependencies;

public sealed record Order(int Id, int Quantity);

public interface IOrders : IDisposable
{
    Task<Order?> Find(int id);
    int Count();
    void Log(int id);
    ValueTask<int> Reserve(int id, int quantity);
    string Describe(int id);
}

[ContractFor(typeof(IOrders))]
internal abstract class OrdersContract : IOrders
{
    public Task<Order?> Find(int id)
    {
        Spec.Requires(id > 0);
        Spec.Ensures<Order?>(r => r is null || r.Id == id);
        return default!;
    }

    public int Count()
    {
        Spec.Ensures<int>(r => r >= 0);
        return default!;
    }

    public void Log(int id) { Spec.Requires(id > 0); }

    public abstract ValueTask<int> Reserve(int id, int quantity);

    // string is not modelled; the member is allowed until a verified call uses it.
    public string Describe(int id) => default!;

    public void Dispose() { }
}

public sealed class OrderService
{
    private readonly IOrders orders;

    public OrderService(IOrders orders) => this.orders = orders;

    [Verified]
    public async Task<int> QuantityOf(int id)
    {
        Spec.Requires(id > 0);
        var order = await orders.Find(id);
        return order is null ? 0 : order.Quantity;
    }

    [Verified]
    public int Counted(int id)
    {
        Spec.Requires(id > 0);
        orders.Log(id);
        var n = orders.Count();
        orders.Dispose();
        return n;
    }

    [Verified]
    public async ValueTask<int> Reserved(int id) => await orders.Reserve(id, 1);
}

public static class Steps
{
    [Verified]
    public static async Task<int> Next(int x)
    {
        Spec.Requires(x < 100);
        Spec.Ensures<int>(r => r == x + 1);
        return x + 1;
    }

    [Verified]
    public static async Task Run(int x)
    {
        Spec.Requires(x < 100);
        Spec.Ensures(() => x < 100);
        await Next(x);
    }
}
