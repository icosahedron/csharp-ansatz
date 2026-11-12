// M6 U18's dependencies, contract classes and async methods (KTD9, KTD10, KTD22): a readonly field of an interface that
// inherits IDisposable, a Task<Order?> result that is nullable once awaited (#171), a void and a synchronous member, an
// abstract contract member, a ValueTask, a member with an unmodelled type that nothing calls, and verified async methods;
// and (#215) a CancellationToken passed through to a dependency and a bare return in a Task method.
using System;
using System.Threading;
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

// #215: a CancellationToken parameter passed through to dependency calls, and a bare `return;` in a Task method.
public interface IShipments
{
    Task<Order?> Find(int id, CancellationToken ct);
    Task Ship(Order order, CancellationToken ct);
}

[ContractFor(typeof(IShipments))]
internal abstract class ShipmentsContract : IShipments
{
    public Task<Order?> Find(int id, CancellationToken ct)
    {
        Spec.Ensures<Order?>(r => r is null || r.Id == id);
        return default!;
    }

    public Task Ship(Order order, CancellationToken ct)
    {
        Spec.Requires(order.Id > 0);
        return default!;
    }
}

public sealed class ShipmentService(IShipments shipments)
{
    [Verified]
    public async Task<int> IdOf(int id, CancellationToken ct)
    {
        Spec.Ensures<int>(r => r == 0 || r == id);
        var order = await shipments.Find(id, ct);
        if (order is null) return 0;
        return order.Id;
    }

    [Verified]
    public async Task ShipIfFound(int id, CancellationToken ct)
    {
        if (id <= 0) return;
        var order = await shipments.Find(id, ct);
        if (order is null) return;
        await shipments.Ship(order, ct);
    }
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
