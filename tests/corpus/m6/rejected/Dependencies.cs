// What M6 U18 rejects, one construct per member or class: dependencies that break KTD9's rules, other uses of a class's
// state, Tasks that are not the direct operand of await (KTD22), and contract classes without the contract shape (KTD10).
using System.Threading.Tasks;
using Warrant;

namespace Corpus.Rejected
{
    // Moved from the M4 corpus: M6 accepts a class's verified instance methods, but this one reads a field.
    public sealed class Counter
    {
        private readonly int _start;

        public Counter(int start) => _start = start;

        [Verified]
        public int Next() => _start + 1;
    }
}

namespace Corpus.M6.Rejected.Dependencies
{
    public sealed record Item(int Id);

    public interface IStock
    {
        int Count(int id);
        Task<int> Load(int id);
        Task Save(int id);
        int Size { get; }
    }

    public interface IUncontracted { int Get(); }

    public interface IBox<T> { int Get(); }

    public interface IShaky { int Get(); }

    public interface ITwice { int Get(); }

    public interface IPublic { int Get(); }

    public interface IWide { int Get(); }

    public interface IExtra { int Get(); }

    public interface ILax { Item? Find(int id); }

    [ContractFor(typeof(IStock))]
    internal abstract class StockContract : IStock
    {
        public int Count(int id)
        {
            Spec.Ensures<int>(r => r >= 0);
            return default!;
        }

        public abstract Task<int> Load(int id);

        public Task Save(int id) => default!;

        public abstract int Size { get; }
    }

    [ContractFor(typeof(IStock))]
    internal abstract class StockAgain : IStock
    {
        public abstract int Count(int id);
        public abstract Task<int> Load(int id);
        public abstract Task Save(int id);
        public abstract int Size { get; }
    }

    [ContractFor(typeof(IShaky))]
    internal class ShakyContract : IShaky
    {
        public int Get() => default!;
    }

    [ContractFor(typeof(ITwice))]
    internal abstract class TwiceContract : ITwice
    {
        public int Get()
        {
            Spec.Ensures<int>(r => r >= 0);
            Twice();
            return default!;
        }

        private static void Twice() { }
    }

    [ContractFor(typeof(IPublic))]
    public abstract class PublicContract : IPublic
    {
        public abstract int Get();
    }

    [ContractFor(typeof(IWide))]
    internal abstract class WideContract : IWide, IUncontracted
    {
        public abstract int Get();
    }

    [ContractFor(typeof(IExtra))]
    internal abstract class ExtraContract : IExtra
    {
        public abstract int Get();

        public int Extra() => default!;
    }

    [ContractFor(typeof(Item))]
    internal abstract class ItemContract
    {
    }

    [ContractFor(typeof(ILax))]
    internal abstract class LaxContract : ILax
    {
        public Item Find(int id) => default!;
    }

    public abstract class Base
    {
        protected readonly IStock inherited = null!;
    }

    public sealed class Store : Base
    {
        private static readonly IStock Shared = null!;
        private readonly IStock stock;
        private readonly IUncontracted loose;
        private readonly IBox<int> box;
        private readonly IShaky shaky;
        private readonly int limit;
        private IStock mutable;

        public Store(IStock stock, IUncontracted loose, IBox<int> box, IShaky shaky)
        {
            this.stock = stock;
            this.loose = loose;
            this.box = box;
            this.shaky = shaky;
            mutable = stock;
            limit = 3;
        }

        [Verified]
        public int Mutable(int id) => mutable.Count(id);

        [Verified]
        public int FromShared(int id) => Shared.Count(id);

        [Verified]
        public int Inherited(int id) => inherited.Count(id);

        [Verified]
        public int Generic() => box.Get();

        [Verified]
        public int Loose() => loose.Get();

        [Verified]
        public int Shaky() => shaky.Get();

        [Verified]
        public int Limit(int id) => id + limit;

        [Verified]
        public int Tested(int id) => stock == null ? 0 : id;

        [Verified]
        public int Sized() => stock.Size;

        [Verified]
        public int InClaim(int id)
        {
            Spec.Ensures<int>(r => r == stock.Count(id));
            return stock.Count(id);
        }

#pragma warning disable CS4014, CS1998 // The point of the member: a Task that is not awaited.
        [Verified]
        public async Task Discarded(int id)
        {
            stock.Save(id);
        }
#pragma warning restore CS4014, CS1998

        [Verified]
        public async Task<int> Configured(int id) => await stock.Load(id).ConfigureAwait(false);

        [Verified]
        public async Task<int> Delayed(int id)
        {
            await Task.Delay(1);
            return id;
        }

        [Verified]
        public async void Fire(int id) => await stock.Save(id);

        [Verified]
        public async Task Early(int id)
        {
            if (id < 0) return;
            await stock.Save(id);
        }

        [Verified]
        public async Task<int> Ordered(int id) => Sum(b: await stock.Load(id), a: stock.Count(id));

        [Verified]
        public static int Sum(int a, int b) => a + b;
    }

    public sealed class Assigned(IStock stock)
    {
        public void Reset() => stock = null!;

        [Verified]
        public int Count(int id) => stock.Count(id);
    }
}
