using Microsoft.CodeAnalysis;
using Warrant.Extraction;
using Warrant.Frontend;
using Warrant.Vir;
using static Warrant.Extraction.Tests.Inline;

namespace Warrant.Extraction.Tests;

/// <summary>
/// M6 U18: extraction reads <c>[ContractFor]</c> classes (KTD10), the dependencies of verified instance methods (KTD9) and
/// <c>async</c> methods (KTD22), in the build and, through <see cref="Diagnoser"/>, in the IDE.
/// </summary>
public class DependencyExtractionTests
{
    private const string GetKey = "M:Payments.IPaymentStore.GetPayment(System.Int32)";
    private const string SaveKey = "M:Payments.IPaymentStore.SavePayment(Payments.Payment)";
    private const string ProcessKey = "M:Payments.PaymentService.ProcessPayment(System.Int32)";

    /// <summary>Design §5.2's payment example, with <c>store</c> a primary-constructor parameter.</summary>
    private const string PaymentExample = """
        #nullable enable
        using System.Threading.Tasks;

        namespace Payments;

        public enum PaymentStatus { Pending, Processed }
        public enum PaymentResult { Valid, Invalid }
        public enum Result { Success, InvalidId, NotFound, Invalid }

        public sealed record Payment(int Id, decimal Amount, PaymentStatus Status);

        public interface IPaymentStore
        {
            Task<Payment?> GetPayment(int id);
            Task SavePayment(Payment p);
        }

        [ContractFor(typeof(IPaymentStore))]
        file abstract class PaymentStoreContract : IPaymentStore
        {
            public Task<Payment?> GetPayment(int id)
            {
                Spec.Ensures<Payment?>(r => r is null || r.Id == id);
                return default!;
            }

            public Task SavePayment(Payment p) => default!;
        }

        public sealed class PaymentService(IPaymentStore store)
        {
            [Verified]
            public static PaymentResult Validate(Payment payment) => payment.Amount > 0m ? PaymentResult.Valid : PaymentResult.Invalid;

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
        """;

    /// <summary>A store interface, its contract class, and a service class with the given members, which hold <c>store</c>.</summary>
    private static ExtractionResult Service(string members, string contract = "", string store = "") =>
        Extract($$"""
            #nullable enable
            using System;
            using System.Threading.Tasks;

            public sealed record Payment(int Id, decimal Amount);

            public interface IStore
            {
                int Count(int id);
                void Log(int id);
                Task<int> Load(int id);
                Task<Payment?> Find(int id);
                Task<Payment> Fetch(int id);
                Task Save(Payment p);
                ValueTask<int> Peek(int id);
                string Name(int id);
                int Size { get; }
                {{store}}
            }

            [ContractFor(typeof(IStore))]
            internal abstract class StoreContract : IStore
            {
                public int Count(int id) { Spec.Requires(id > 0); Spec.Ensures<int>(r => r >= 0); return default!; }
                public void Log(int id) { Spec.Requires(id > 0); }
                public abstract Task<int> Load(int id);
                public Task<Payment?> Find(int id) { Spec.Ensures<Payment?>(r => r is null || r.Id == id); return default!; }
                public Task<Payment> Fetch(int id) => default!;
                public Task Save(Payment p) { Spec.Ensures(() => p.Id > 0); return default!; }
                public ValueTask<int> Peek(int id) => default!;
                public string Name(int id) => default!;
                public abstract int Size { get; }
                {{contract}}
            }

            public sealed class Service
            {
                private readonly IStore store;

                public Service(IStore store) => this.store = store;

            {{members}}
            }
            """);

    // ---- The payment example (design §5.2) ----

    [Fact]
    public void ProcessPaymentExtractsWithTheStoresTwoMembersAsDependenciesAndTheContractClassesEnsuresAsTheirContracts()
    {
        var result = Extract(PaymentExample);

        Assert.Empty(result.Diagnostics);
        Assert.Equal(
            new[]
            {
                "T:Payments.PaymentStatus", "T:Payments.Payment", GetKey, SaveKey, "T:Payments.PaymentResult",
                "M:Payments.PaymentService.Validate(Payments.Payment)", "T:Payments.Result", ProcessKey,
            }.Order(StringComparer.Ordinal),
            result.Units.Select(u => u.Key).Order(StringComparer.Ordinal));

        var process = Unit(result, ProcessKey);
        Assert.Equal(VirUnitKind.Function, process.Kind);
        Assert.Null(process.Self);
        Assert.Equal([new VirParam("paymentId", VirType.Int32)], process.Params!);
        Assert.Equal(VirType.Task(VirType.Ref("T:Payments.Result")), process.Returns);
        var store = Assert.Single(process.Dependencies!);
        Assert.Equal(new VirDependency("store", "T:Payments.IPaymentStore", new VirList<string>([GetKey, SaveKey])), store);
        Assert.Contains(GetKey, process.Deps);
        Assert.Contains(SaveKey, process.Deps);
        Assert.Equal(
            [
                new VirAssumption(VirAssumptionKind.NonNull, "store"),
                new VirAssumption(VirAssumptionKind.NonNull, "store.GetPayment()"),
                new VirAssumption(VirAssumptionKind.NonNull, "store.SavePayment()"),
                new VirAssumption(VirAssumptionKind.ExternalContract, GetKey),
                new VirAssumption(VirAssumptionKind.ExternalContract, SaveKey),
            ],
            process.Assumptions);

        // var payment = await store.GetPayment(paymentId): the awaited value is the Task's nullable result.
        var body = Assert.IsType<BlockStmt>(process.Body).Stmts;
        Assert.IsType<EnsuresStmt>(body[0]);
        var payment = VirType.Nullable(VirType.Ref("T:Payments.Payment"));
        var get = Assert.IsType<DeclStmt>(body[2]);
        Assert.Equal("payment", get.Name);
        Assert.Equal(
            new AwaitExpr(payment, new ExternalCallExpr(VirType.Task(payment), 0, GetKey, VirList.Of<VirExpr>(new ParamExpr(VirType.Int32, 0)))),
            get.Init);

        // await store.SavePayment(payment with { ... }); is an awaited call whose result is discarded.
        var save = Assert.IsType<EvalStmt>(body[5]);
        var awaited = Assert.IsType<AwaitExpr>(save.Value);
        Assert.Equal(VirType.Unit, awaited.Type);
        var call = Assert.IsType<ExternalCallExpr>(awaited.Operand);
        Assert.Equal((0, SaveKey, (VirType)VirType.Task(VirType.Unit)), (call.Dependency, call.Member, call.Type));
        Assert.IsType<WithExpr>(Assert.Single(call.Args));
    }

    [Fact]
    public void ThePaymentStoresMembersBecomeContractUnits()
    {
        var result = Extract(PaymentExample);

        var get = Unit(result, GetKey);
        Assert.Equal(VirUnitKind.Contract, get.Kind);
        Assert.Equal([new VirParam("id", VirType.Int32)], get.Params!);
        var payment = VirType.Ref("T:Payments.Payment");
        Assert.Equal(VirType.Task(VirType.Nullable(payment)), get.Returns);
        var r = new LocalExpr(VirType.Nullable(payment), 0);
        Assert.Equal(
            new BlockStmt(VirList.Of<VirStmt>(new EnsuresStmt(0, "r", new LogicalExpr(
                LogicalOp.Or,
                new IsNullExpr(r),
                new CompareExpr(CompareOp.Eq, CompareKind.Int, new GetExpr(VirType.Int32, "Id", new UnwrapExpr(payment, UnwrapKind.NonNull, r)), new ParamExpr(VirType.Int32, 0)))))),
            get.Body);
        Assert.Equal(["T:Payments.Payment"], get.Deps);

        // `=> default!` assumes nothing about the result.
        var save = Unit(result, SaveKey);
        Assert.Equal(VirUnitKind.Contract, save.Kind);
        Assert.Equal(VirType.Task(VirType.Unit), save.Returns);
        Assert.Equal(new BlockStmt(VirList<VirStmt>.Empty), save.Body);
        Assert.Equal(["p"], NonNull(save));
    }

    [Fact]
    public void ADependencyCanBeAReadonlyFieldAndEachFieldIsItsOwnDependency()
    {
        var result = Extract("""
            #nullable enable
            public interface ICounter { int Next(int x); }

            [ContractFor(typeof(ICounter))]
            internal abstract class CounterContract : ICounter
            {
                public int Next(int x) { Spec.Ensures<int>(r => r > x); return default!; }
            }

            public sealed class Twice
            {
                private readonly ICounter first;
                private readonly ICounter second;

                public Twice(ICounter first, ICounter second) { this.first = first; this.second = second; }

                [Verified]
                public int Run(int x) => second.Next(first.Next(x)) + this.first.Next(x);
            }
            """);

        var unit = Unit(result, "M:Twice.Run(System.Int32)");
        const string next = "M:ICounter.Next(System.Int32)";
        Assert.Equal(
            [new VirDependency("second", "T:ICounter", VirList.Of(next)), new VirDependency("first", "T:ICounter", VirList.Of(next))],
            unit.Dependencies!);
        var sum = Assert.IsType<BinaryExpr>(unit.Body);
        var outer = Assert.IsType<ExternalCallExpr>(sum.L);
        Assert.Equal(0, outer.Dependency);
        Assert.Equal(1, Assert.IsType<ExternalCallExpr>(Assert.Single(outer.Args)).Dependency);
        Assert.Equal(1, Assert.IsType<ExternalCallExpr>(sum.R).Dependency);
        Assert.Equal(["first", "second"], NonNull(unit).Order(StringComparer.Ordinal));
        Assert.Equal(VirUnitKind.Contract, Unit(result, next).Kind);
    }

    // ---- Calls through a dependency ----

    [Fact]
    public void ASynchronousAndAVoidMemberAreCalledThroughADependency()
    {
        var result = Service("""
                [Verified]
                public int Counted(int id)
                {
                    store.Log(id);
                    return store.Count(id);
                }
            """);

        var unit = Unit(result, "M:Service.Counted(System.Int32)");
        var stmts = Assert.IsType<BlockStmt>(unit.Body).Stmts;
        var log = Assert.IsType<ExternalCallExpr>(Assert.IsType<EvalStmt>(stmts[0]).Value);
        Assert.Equal((VirType)VirType.Unit, log.Type);
        Assert.Equal(VirType.Int32, Assert.IsType<ExternalCallExpr>(Assert.IsType<ReturnStmt>(stmts[1]).Value).Type);
        Assert.Equal(["store"], NonNull(unit));
        Assert.Equal(new BlockStmt(VirList.Of<VirStmt>(new RequiresStmt(new CompareExpr(CompareOp.Gt, CompareKind.Int, new ParamExpr(VirType.Int32, 0), new LitExpr(VirType.Int32, 0))))), Unit(result, "M:IStore.Log(System.Int32)").Body);
    }

    [Fact]
    public void AMemberReturningATaskOfANullableRecordExtractsAsANullableResult()
    {
        var result = Service("""
                [Verified]
                public async Task<int> IdOf(int id)
                {
                    var p = await store.Find(id);
                    return p is null ? 0 : p.Id;
                }
            """);

        var unit = Unit(result, "M:Service.IdOf(System.Int32)");
        var payment = VirType.Nullable(VirType.Ref("T:Payment"));
        var decl = Assert.IsType<DeclStmt>(Assert.IsType<BlockStmt>(unit.Body).Stmts[0]);
        var await = Assert.IsType<AwaitExpr>(decl.Init);
        Assert.Equal(payment, await.Type);
        Assert.Equal(VirType.Task(payment), await.Operand.Type);
        Assert.Equal(VirType.Task(payment), Unit(result, "M:IStore.Find(System.Int32)").Returns);
        // The Task is assumed present; the record inside it may be null.
        Assert.Equal(["store", "store.Find()"], NonNull(unit));
    }

    [Fact]
    public void ANonNullableRecordInsideATaskIsAssumedPresentAndAValueTaskIsNotAReference()
    {
        var result = Service("""
                [Verified]
                public async Task<int> Both(int id)
                {
                    var p = await store.Fetch(id);
                    return p.Id + await store.Peek(id);
                }
            """);

        var unit = Unit(result, "M:Service.Both(System.Int32)");
        Assert.Equal(["store", "store.Fetch()", "await store.Fetch()"], NonNull(unit));
        Assert.Equal(VirType.Task(VirType.Int32), Unit(result, "M:IStore.Peek(System.Int32)").Returns);
    }

    [Fact]
    public void AnAbstractContractMemberAssumesNothing()
    {
        var result = Service("""
                [Verified]
                public async Task<int> Loaded(int id) => await store.Load(id);
            """);

        var load = Unit(result, "M:IStore.Load(System.Int32)");
        Assert.Equal(VirUnitKind.Contract, load.Kind);
        Assert.Equal(new BlockStmt(VirList<VirStmt>.Empty), load.Body);
        Assert.IsType<AwaitExpr>(Unit(result, "M:Service.Loaded(System.Int32)").Body);
    }

    [Fact]
    public void OnlyTheContractMembersAVerifiedMethodCallsBecomeUnitsAndAnUnmodelledMemberIsAcceptedUntilCalled()
    {
        var result = Service("""
                [Verified]
                public int Counted(int id) => store.Count(id);

                [Verified]
                public int Named(int id) => store.Name(id) == null ? 0 : 1;
            """);

        Assert.NotNull(result.Find("M:Service.Counted(System.Int32)"));
        Assert.Equal(["M:IStore.Count(System.Int32)"], result.Units.Where(u => u.Unit.Kind == VirUnitKind.Contract).Select(u => u.Key));
        Assert.Equal("WRT0002 | string", Only(result, "M:Service.Named(System.Int32)"));
        Assert.Empty(result.DiagnosticsFor("T:StoreContract"));
    }

    [Fact]
    public void AContractWhoseMemberCannotBeTranslatedRejectsItsCaller()
    {
        var result = Service(
            """
                [Verified]
                public int Bad(int id) => store.Shift(id);
            """,
            contract: "public int Shift(int id) { Spec.Ensures<int>(r => r == id << 1); return default!; }",
            store: "int Shift(int id);");

        Assert.Equal("WRT0002 | shift", Only(result, "M:IStore.Shift(System.Int32)"));
        Assert.Equal("WRT0002 | depends on a rejected unit", Only(result, "M:Service.Bad(System.Int32)"));
    }

    [Fact]
    public void ADependencyCalledInsideASpecExpressionIsRejected()
    {
        var result = Service("""
                [Verified]
                public int Counted(int id)
                {
                    Spec.Ensures<int>(r => r == store.Count(id));
                    return store.Count(id);
                }
            """);

        Assert.Equal("WRT0002 | dependency call in a Spec expression", Only(result, "M:Service.Counted(System.Int32)"));
    }

    // ---- Dependency discovery (KTD9) ----

    [Fact]
    public void AMutableFieldOfAContractedTypeIsRejected()
    {
        var result = Extract("""
            public interface ICounter { int Next(int x); }

            [ContractFor(typeof(ICounter))]
            internal abstract class CounterContract : ICounter { public abstract int Next(int x); }

            public sealed class Holder
            {
                private ICounter counter;
                public Holder(ICounter counter) => this.counter = counter;

                [Verified]
                public int Run(int x) => counter.Next(x);
            }
            """);

        Assert.Equal("WRT0002 | mutable dependency field", Only(result, "M:Holder.Run(System.Int32)"));
    }

    [Theory]
    [InlineData("Func<int> f = () => { counter = null!; return 0; };")]
    [InlineData("counter = null!;")]
    [InlineData("Swap(ref counter);")]
    [InlineData("(counter, _) = (null!, 1);")]
    public void APrimaryConstructorParameterAssignedAnywhereInTheClassIsRejected(string assignment)
    {
        var result = Extract($$"""
            using System;
            public interface ICounter { int Next(int x); }

            [ContractFor(typeof(ICounter))]
            internal abstract class CounterContract : ICounter { public abstract int Next(int x); }

            public sealed class Holder(ICounter counter)
            {
                public void Reset() { {{assignment}} }
                private static void Swap(ref ICounter c) { }

                [Verified]
                public int Run(int x) => counter.Next(x);
            }
            """);

        Assert.Equal("WRT0002 | assigned primary-constructor parameter", Only(result, "M:Holder.Run(System.Int32)"));
    }

    [Fact]
    public void InheritedStaticAndGenericInterfaceDependenciesAreRejectedWithNamedConstructs()
    {
        var result = Extract("""
            public interface ICounter { int Next(int x); }
            public interface IBox<T> { int Get(int x); }

            [ContractFor(typeof(ICounter))]
            internal abstract class CounterContract : ICounter { public abstract int Next(int x); }

            public abstract class Base
            {
                protected readonly ICounter inherited = null!;
            }

            public sealed class Holder : Base
            {
                private static readonly ICounter shared = null!;
                private readonly IBox<int> box = null!;

                [Verified] public int FromBase(int x) => inherited.Next(x);
                [Verified] public int FromStatic(int x) => shared.Next(x);
                [Verified] public int FromGeneric(int x) => box.Get(x);
            }
            """);

        Assert.Equal("WRT0002 | inherited dependency", Only(result, "M:Holder.FromBase(System.Int32)"));
        Assert.Equal("WRT0002 | static dependency", Only(result, "M:Holder.FromStatic(System.Int32)"));
        Assert.Equal("WRT0002 | generic interface dependency", Only(result, "M:Holder.FromGeneric(System.Int32)"));
    }

    [Fact]
    public void AnInterfaceWithoutAContractClassIsRejectedNamingIt()
    {
        var result = Extract("""
            public interface IClock { int Now(); }

            public sealed class Holder(IClock clock)
            {
                [Verified] public int Run() => clock.Now();
            }
            """);

        var d = Assert.Single(result.DiagnosticsFor("M:Holder.Run"));
        Assert.Equal("WRT0002 | dependency without a contract class", d.Id + " | " + d.Construct);
        Assert.Contains("IClock", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EveryOtherMemberAccessOnThisStaysRejected()
    {
        var result = Service("""
                private readonly int limit = 3;

                public int Helper(int x) => x;

                [Verified] public int ReadsAField(int x) => x + limit;
                [Verified] public int CallsAMethod(int x) => Helper(x);
                [Verified] public int TestsTheDependency(int x) => store == null ? 0 : x;
                [Verified] public int ReadsAProperty(int x) => store.Size;
            """);

        Assert.Equal("WRT0002 | member access on this", Only(result, "M:Service.ReadsAField(System.Int32)"));
        Assert.Equal("WRT0002 | member access on this", Only(result, "M:Service.CallsAMethod(System.Int32)"));
        Assert.Equal("WRT0002 | dependency used other than to call a member", Only(result, "M:Service.TestsTheDependency(System.Int32)"));
        Assert.Equal("WRT0002 | property of a dependency", Only(result, "M:Service.ReadsAProperty(System.Int32)"));
    }

    [Fact]
    public void AnInstancePropertyOfAClassAndAStructsInstanceMethodAreStillRejected()
    {
        var result = Extract("""
            public sealed class Holder
            {
                [Verified] public int Value => 1;
            }

            public struct Point
            {
                [Verified] public int Zero() => 0;
            }
            """);

        Assert.Equal("WRT0002 | instance member of a class", Only(result, "P:Holder.Value"));
        Assert.Equal("WRT0002 | instance member of a class", Only(result, "M:Point.Zero"));
    }

    // ---- Interfaces from referenced projects (#87) ----

    [Fact]
    public void AnInterfaceFromAReferencedProjectIsAcceptedAndARecordFromItIsRejected()
    {
        var library = CompilationFactory.Create(
            [new SourceFile("Lib.cs", """
                #nullable enable
                namespace Lib;
                public sealed record Item(int Id);
                public interface IItems
                {
                    int Count(int id);
                    Item Get(int id);
                }
                """)],
            checkOverflow: false,
            assemblyName: "Lib");
        using var image = new MemoryStream();
        Assert.True(library.Emit(image).Success);
        var consumer = CompilationFactory.Create(
            [new SourceFile("Test.cs", """
                #nullable enable
                using Warrant;

                [ContractFor(typeof(Lib.IItems))]
                internal abstract class ItemsContract : Lib.IItems
                {
                    public int Count(int id) { Spec.Ensures<int>(r => r >= 0); return default!; }
                    public Lib.Item Get(int id) => default!;
                }

                public sealed class Holder(Lib.IItems items)
                {
                    [Verified] public int Counted(int id) => items.Count(id);
                    [Verified] public int Got(int id) => items.Get(id) is null ? 0 : 1;
                }
                """)],
            checkOverflow: false).AddReferences(MetadataReference.CreateFromImage(image.ToArray()));

        var result = Extractor.Extract(consumer);

        var counted = Unit(result, "M:Holder.Counted(System.Int32)");
        Assert.Equal("T:Lib.IItems", Assert.Single(counted.Dependencies!).Interface);
        Assert.Equal(VirUnitKind.Contract, Unit(result, "M:Lib.IItems.Count(System.Int32)").Kind);
        var d = Assert.Single(result.DiagnosticsFor("M:Holder.Got(System.Int32)"));
        Assert.Equal("WRT0002 | type defined outside the compilation", d.Id + " | " + d.Construct);
    }

    // ---- The contract class's shape (KTD10) ----

    private static ExtractionResult Contract(string contract, string interfaces = "") =>
        Extract($$"""
            #nullable enable
            using System;
            using System.Threading.Tasks;

            public interface IStore
            {
                int Get(int id);
                void Save(int value);
            }

            public interface IOther { int Other(); }

            {{interfaces}}

            {{contract}}
            """);

    [Theory]
    [InlineData("public int Get(int id) { Spec.Requires(id > 0); var x = id; return default!; }", "contract member body other than Spec calls and return default!")]
    [InlineData("public int Get(int id) { Spec.Requires(id > 0); return 0; }", "contract member body other than Spec calls and return default!")]
    [InlineData("public int Get(int id) => id;", "contract member body other than Spec calls and return default!")]
    [InlineData("public int Get(int id) { Spec.Assert(id > 0); return default!; }", "contract member body other than Spec calls and return default!")]
    public void AMemberBodyThatIsNotSpecCallsAndReturnDefaultIsRejectedNamingTheStep(string get, string construct)
    {
        var result = Contract($$"""
            [ContractFor(typeof(IStore))]
            internal abstract class StoreContract : IStore
            {
                {{get}}
                public void Save(int value) { }
            }
            """);

        var d = Assert.Single(result.DiagnosticsFor("T:StoreContract"));
        Assert.Equal("WRT0002 | " + construct, d.Id + " | " + d.Construct);
        Assert.Contains("contract shape", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void NoThrowInAContractMemberIsRejectedAsOutOfScope()
    {
        // #182: Spec.NoThrow states that a method's own explicit throws are unreachable; a contract member has none.
        var result = Contract("""
            [ContractFor(typeof(IStore))]
            internal abstract class StoreContract : IStore
            {
                public int Get(int id) { Spec.Requires(id > 0); Spec.NoThrow(); return default!; }
                public void Save(int value) { }
            }
            """);

        var d = Assert.Single(result.DiagnosticsFor("T:StoreContract"));
        Assert.Equal("WRT0002 | Spec.NoThrow in a contract member", d.Id + " | " + d.Construct);
        Assert.Contains("Spec.NoThrow is for a verified method's own body", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AVoidMemberWithOnlySpecCallsAndAnAbstractMemberAreAccepted()
    {
        var result = Contract("""
            [ContractFor(typeof(IStore))]
            file abstract class StoreContract : IStore
            {
                public abstract int Get(int id);
                public void Save(int value) { Spec.Requires(value > 0); Spec.Ensures(() => value > 0); }
            }
            """);

        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void AnInterfaceThatInheritsIDisposableIsAcceptedWithDisposeInTheClass()
    {
        var result = Extract("""
            using System;
            public interface IConnection : IDisposable { int Read(int id); }

            [ContractFor(typeof(IConnection))]
            internal abstract class ConnectionContract : IConnection
            {
                public int Read(int id) { Spec.Ensures<int>(r => r >= 0); return default!; }
                public void Dispose() { }
            }

            public sealed class Reader(IConnection connection)
            {
                [Verified]
                public int Run(int id)
                {
                    var x = connection.Read(id);
                    connection.Dispose();
                    return x;
                }
            }
            """);

        Assert.Empty(result.Diagnostics);
        var run = Unit(result, "M:Reader.Run(System.Int32)");
        Assert.Equal(["M:IConnection.Read(System.Int32)", "M:System.IDisposable.Dispose"], Assert.Single(run.Dependencies!).Members);
        var dispose = Unit(result, "M:System.IDisposable.Dispose");
        Assert.Equal(VirUnitKind.Contract, dispose.Kind);
        Assert.Equal(VirType.Unit, dispose.Returns);
    }

    [Fact]
    public void AnInheritedMemberThatTwoContractClassesStateIsRejectedAsAmbiguous()
    {
        var result = Extract("""
            using System;
            public interface IReader : IDisposable { int Read(); }
            public interface IWriter : IDisposable { void Write(int x); }

            [ContractFor(typeof(IReader))]
            internal abstract class ReaderContract : IReader
            {
                public abstract int Read();
                public void Dispose() { Spec.Requires(true); }
            }

            [ContractFor(typeof(IWriter))]
            internal abstract class WriterContract : IWriter
            {
                public abstract void Write(int x);
                public abstract void Dispose();
            }

            public sealed class Closer(IReader reader)
            {
                [Verified] public void Close() => reader.Dispose();
            }
            """);

        var d = Assert.Single(result.DiagnosticsFor("M:System.IDisposable.Dispose"));
        Assert.Equal("WRT0002 | interface member with two contract classes", d.Id + " | " + d.Construct);
        Assert.Contains("ReaderContract", d.Message, StringComparison.Ordinal);
        Assert.Contains("WriterContract", d.Message, StringComparison.Ordinal);
        Assert.Equal("WRT0002 | depends on a rejected unit", Only(result, "M:Closer.Close"));
    }

    [Fact]
    public void AnInterfaceMemberWithADefaultBodyAndNoContractMemberIsRejectedWhenCalled()
    {
        var result = Extract("""
            public interface ICounter
            {
                int Next(int x);
                int Twice(int x) => Next(Next(x));
            }

            [ContractFor(typeof(ICounter))]
            internal abstract class CounterContract : ICounter { public abstract int Next(int x); }

            public sealed class Holder(ICounter counter)
            {
                [Verified] public int Run(int x) => counter.Twice(x);
            }
            """);

        Assert.Equal("WRT0002 | interface member without a contract member", Only(result, "M:ICounter.Twice(System.Int32)"));
        Assert.Equal("WRT0002 | depends on a rejected unit", Only(result, "M:Holder.Run(System.Int32)"));
    }

    [Fact]
    public void ASecondContractClassForTheSameInterfaceIsRejectedNamingBoth()
    {
        var result = Contract("""
            [ContractFor(typeof(IStore))]
            internal abstract class FirstContract : IStore
            {
                public abstract int Get(int id);
                public abstract void Save(int value);
            }

            [ContractFor(typeof(IStore))]
            internal abstract class SecondContract : IStore
            {
                public abstract int Get(int id);
                public abstract void Save(int value);
            }
            """);

        Assert.Empty(result.DiagnosticsFor("T:FirstContract"));
        var d = Assert.Single(result.DiagnosticsFor("T:SecondContract"));
        Assert.Equal("WRT0002 | second contract class for an interface", d.Id + " | " + d.Construct);
        Assert.Contains("FirstContract", d.Message, StringComparison.Ordinal);
        Assert.Contains("SecondContract", d.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("[ContractFor(typeof(IStore))] internal abstract class C : IStore, IOther { public abstract int Get(int id); public abstract void Save(int value); public abstract int Other(); }", "contract class that does not implement exactly its interface")]
    [InlineData("[ContractFor(typeof(IStore))] internal abstract class C : IOther { public abstract int Other(); }", "contract class that does not implement exactly its interface")]
    [InlineData("public abstract class B { } [ContractFor(typeof(IStore))] internal abstract class C : B, IStore { public abstract int Get(int id); public abstract void Save(int value); }", "contract class that does not implement exactly its interface")]
    [InlineData("[ContractFor(typeof(IStore))] public abstract class C : IStore { public abstract int Get(int id); public abstract void Save(int value); }", "contract class that is not file or internal")]
    [InlineData("[ContractFor(typeof(IStore))] internal class C : IStore { public int Get(int id) => default!; public void Save(int value) { } }", "contract class that is not abstract")]
    [InlineData("[ContractFor(typeof(IStore))] internal abstract class C : IStore { public abstract int Get(int id); public abstract void Save(int value); private int count; }", "contract class member that is not a member of its interface")]
    [InlineData("[ContractFor(typeof(IStore))] internal abstract class C : IStore { public abstract int Get(int id); public abstract void Save(int value); public int Extra() => default!; }", "contract class member that is not a member of its interface")]
    [InlineData("[ContractFor(typeof(IStore))] internal abstract class C : IStore { protected C() { } public abstract int Get(int id); public abstract void Save(int value); }", "contract class member that is not a member of its interface")]
    [InlineData("[ContractFor(typeof(int))] internal abstract class C { }", "[ContractFor] of a type that is not an interface")]
    public void AContractClassOfTheWrongShapeIsRejectedNamingTheStep(string contract, string construct)
    {
        var result = Contract(contract);

        var d = Assert.Single(result.DiagnosticsFor("T:C"));
        Assert.Equal("WRT0002 | " + construct, d.Id + " | " + d.Construct);
    }

    [Fact]
    public void ACallThroughAnInterfaceWhoseContractClassIsRejectedIsRejected()
    {
        var result = Contract(
            """
            [ContractFor(typeof(IStore))]
            internal class StoreContract : IStore { public int Get(int id) => default!; public void Save(int value) { } }

            public sealed class Holder(IStore store)
            {
                [Verified] public int Run(int id) => store.Get(id);
            }
            """);

        Assert.Equal("WRT0002 | contract class that is not abstract", Only(result, "T:StoreContract"));
        Assert.Equal("WRT0002 | dependency whose contract class is rejected", Only(result, "M:Holder.Run(System.Int32)"));
    }

    [Fact]
    public void AContractMemberWhoseNullabilityDiffersFromTheInterfaceIsRejected()
    {
        var result = Extract("""
            #nullable enable
            public sealed record Payment(int Id);
            public interface IStore { Payment? Find(int id); }

            [ContractFor(typeof(IStore))]
            internal abstract class StoreContract : IStore
            {
                public Payment Find(int id) => default!;
            }
            """);

        Assert.Equal("WRT0002 | contract member whose nullability differs from its interface", Only(result, "T:StoreContract"));
    }

    // ---- async (KTD22) ----

    [Fact]
    public void AwaitOfADependencyCallIsAcceptedAndAwaitOfTaskDelayIsRejected()
    {
        var result = Service("""
                [Verified]
                public async Task<int> Loaded(int id) => await store.Load(id);

                [Verified]
                public async Task<int> Delayed(int id)
                {
                    await Task.Delay(1);
                    return id;
                }
            """);

        Assert.NotNull(result.Find("M:Service.Loaded(System.Int32)"));
        Assert.Equal("WRT0002 | Task combinator", Only(result, "M:Service.Delayed(System.Int32)"));
    }

    [Theory]
    [InlineData("public async Task Discarded(Payment p) { store.Save(p); }", "M:Service.Discarded(Payment)", "Task-returning call that is not awaited")]
    [InlineData("public async Task Stored(int id) { var t = store.Load(id); await t; }", "M:Service.Stored(System.Int32)", "Task-returning call that is not awaited")]
    [InlineData("public async Task Assigned(Payment p) { _ = store.Save(p); }", "M:Service.Assigned(Payment)", "Task-returning call that is not awaited")]
    [InlineData("public Task<int> Returned(int id) { return store.Load(id); }", "M:Service.Returned(System.Int32)", "Task-returning call that is not awaited")]
    [InlineData("public async Task<int> Configured(int id) => await store.Load(id).ConfigureAwait(false);", "M:Service.Configured(System.Int32)", "ConfigureAwait")]
    [InlineData("public async Task<int> Combined(int id) { await Task.WhenAll(store.Load(id)); return id; }", "M:Service.Combined(System.Int32)", "Task combinator")]
    [InlineData("public async void Fire(int id) { await store.Load(id); }", "M:Service.Fire(System.Int32)", "async void method")]
    public void ATaskThatIsNotTheDirectOperandOfAwaitIsRejected(string member, string key, string construct)
    {
        var result = Service("[Verified] " + member);

        Assert.Equal("WRT0002 | " + construct, Only(result, key));
    }

    // ---- CancellationToken and return; (#215) ----

    private const string Token = "T:System.Threading.CancellationToken";

    [Fact]
    public void ABareReturnInAVoidOrTaskMethodReturnsTheUnitLiteral()
    {
        var result = Service("""
                [Verified]
                public async Task Early(int id) { if (id < 0) return; await store.Load(id); }

                [Verified]
                public void Logged(int id)
                {
                    if (id <= 0) return;
                    store.Log(id);
                }
            """);

        Assert.Empty(result.Diagnostics);
        var early = Assert.IsType<BlockStmt>(Unit(result, "M:Service.Early(System.Int32)").Body);
        var then = Assert.IsType<IfStmt>(early.Stmts[0]).Then;
        Assert.Equal(new ReturnStmt(LitExpr.Unit), Assert.Single(Assert.IsType<BlockStmt>(then).Stmts));
        Assert.Equal(VirType.Unit, Unit(result, "M:Service.Logged(System.Int32)").Returns);
    }

    [Fact]
    public void ACancellationTokenParameterIsOpaqueAndPassedThroughToADependencyCall()
    {
        var result = Service(
            """
                [Verified]
                public async Task<int> Loaded(int id, System.Threading.CancellationToken ct) => await store.LoadWithin(id, ct);
            """,
            contract: "public Task<int> LoadWithin(int id, System.Threading.CancellationToken ct) { Spec.Ensures<int>(r => r >= 0); return default!; }",
            store: "Task<int> LoadWithin(int id, System.Threading.CancellationToken ct);");

        Assert.Empty(result.Diagnostics);
        var loaded = Unit(result, "M:Service.Loaded(System.Int32,System.Threading.CancellationToken)");
        Assert.Equal(new VirParam("ct", VirType.Opaque(Token)), loaded.Params![1]);
        var call = Assert.IsType<ExternalCallExpr>(Assert.IsType<AwaitExpr>(loaded.Body).Operand);
        Assert.Equal(new ParamExpr(VirType.Opaque(Token), 1), call.Args[1]);
        var contract = Unit(result, "M:IStore.LoadWithin(System.Int32,System.Threading.CancellationToken)");
        Assert.Equal(VirType.Opaque(Token), contract.Params![1].Type);
    }

    [Theory]
    [InlineData("public async Task<int> Defaulted(int id) => await store.LoadWithin(id, default);", "M:Service.Defaulted(System.Int32)", "WRT0002 | cancellation token other than a parameter")]
    [InlineData("public async Task<int> Omitted(int id) => await store.LoadWithin(id);", "M:Service.Omitted(System.Int32)", "WRT0002 | cancellation token other than a parameter")]
    [InlineData("public async Task<int> NoToken(int id) => await store.LoadWithin(id, System.Threading.CancellationToken.None);", "M:Service.NoToken(System.Int32)", "WRT0002 | cancellation token other than a parameter")]
    [InlineData("public async Task<int> Kept(int id, System.Threading.CancellationToken ct) { var t = ct; return await store.LoadWithin(id, t); }", "M:Service.Kept(System.Int32,System.Threading.CancellationToken)", "WRT0002 | cancellation token other than a parameter")]
    [InlineData("public int Asked(int id, System.Threading.CancellationToken ct) => ct.IsCancellationRequested ? 0 : id;", "M:Service.Asked(System.Int32,System.Threading.CancellationToken)", "WRT0005 | P:System.Threading.CancellationToken.IsCancellationRequested")]
    [InlineData("public async Task<int> Checked(int id, System.Threading.CancellationToken ct) { ct.ThrowIfCancellationRequested(); return await store.LoadWithin(id, ct); }", "M:Service.Checked(System.Int32,System.Threading.CancellationToken)", "WRT0005 | M:System.Threading.CancellationToken.ThrowIfCancellationRequested")]
    public void ACancellationTokenIsOnlyPassedOn(string member, string key, string expected)
    {
        var result = Service(
            "[Verified] " + member,
            contract: "public Task<int> LoadWithin(int id, System.Threading.CancellationToken ct = default) => default!;",
            store: "Task<int> LoadWithin(int id, System.Threading.CancellationToken ct = default);");

        Assert.Equal(expected, Only(result, key));
    }

    [Fact]
    public void ATheoremOrARecordCannotHoldACancellationToken()
    {
        var result = Extract("""
            using System.Threading;
            public sealed record Job(int Id, CancellationToken Token);
            public static class T
            {
                [Theorem]
                public static Proof Any(CancellationToken ct) => Prove.That(true);

                [Verified]
                public static int IdOf(Job job) => job.Id;
            }
            """);

        Assert.Equal("WRT0002 | cancellation token other than a parameter", Only(result, "M:T.Any(System.Threading.CancellationToken)"));
        Assert.Equal("WRT0002 | cancellation token other than a parameter", Only(result, "T:Job"));
    }

    [Fact]
    public void AnAsyncMethodMayAwaitAVerifiedAsyncMethodAndAVoidMethodTakesAnEnsuresWithoutTheResult()
    {
        var result = Extract("""
            using System.Threading.Tasks;
            public static class C
            {
                [Verified]
                public static async Task<int> Inner(int x)
                {
                    Spec.Ensures<int>(r => r == x);
                    return x;
                }

                [Verified]
                public static async ValueTask<int> Outer(int x) => await Inner(x) + 1;

                [Verified]
                public static void Check(int x)
                {
                    Spec.Requires(x > 0);
                    Spec.Ensures(() => x > 0);
                }

                [Verified]
                public static async Task Done(int x)
                {
                    Spec.Ensures(() => x == x);
                    await Inner(x);
                }
            }
            """);

        Assert.Empty(result.Diagnostics);
        Assert.Equal(VirType.Task(VirType.Int32), Unit(result, "M:C.Inner(System.Int32)").Returns);
        var outer = Unit(result, "M:C.Outer(System.Int32)");
        Assert.Equal(VirType.Task(VirType.Int32), outer.Returns);
        var await = Assert.IsType<AwaitExpr>(Assert.IsType<BinaryExpr>(outer.Body).L);
        Assert.Equal(new CallExpr(VirType.Task(VirType.Int32), "M:C.Inner(System.Int32)", VirList.Of<VirExpr>(new ParamExpr(VirType.Int32, 0))), await.Operand);
        Assert.Equal(VirType.Unit, Unit(result, "M:C.Check(System.Int32)").Returns);
        var done = Unit(result, "M:C.Done(System.Int32)");
        Assert.Equal(VirType.Task(VirType.Unit), done.Returns);
        Assert.IsType<EvalStmt>(Assert.IsType<BlockStmt>(done.Body).Stmts[1]);
    }

    [Theory]
    [InlineData("public static void F(int x) { Spec.Ensures<int>(r => r == x); }", "M:C.F(System.Int32)", "Spec.Ensures with a result on a method that returns none")]
    [InlineData("public static async Task F(int x) { Spec.Ensures<int>(r => r == x); await Task.CompletedTask; }", "M:C.F(System.Int32)", "Spec.Ensures with a result on a method that returns none")]
    [InlineData("public static async Task<int> F(int x) { Spec.Ensures(() => x > 0); return x; }", "M:C.F(System.Int32)", "Spec.Ensures without the result")]
    [InlineData("public static async ValueTask<int> F(int x) { Spec.Ensures<long>(r => r > 0); return x; }", "M:C.F(System.Int32)", "Spec.Ensures type argument that is not the return type")]
    [InlineData("public static void F(int x) => Spec.Ensures(() => x > 0);", "M:C.F(System.Int32)", "Spec.Ensures in an expression-bodied member")]
    public void EnsuresOnVoidAndTaskMethodsFollowsTheirResult(string member, string key, string construct)
    {
        var result = Extract($$"""
            using System.Threading.Tasks;
            public static class C
            {
                [Verified]
                {{member}}
            }
            """);

        Assert.Equal("WRT0002 | " + construct, Only(result, key));
    }

    [Fact]
    public void NamedArgumentsOutOfOrderAroundAnExternalCallAreRejected()
    {
        var result = Service("""
                [Verified]
                public async Task<int> Ordered(int id) => Sum(b: await store.Load(id), a: store.Count(id));

                [Verified]
                public static int Sum(int a, int b) => a + b;
            """);

        Assert.Equal("WRT0002 | named arguments out of order with a dependency call", Only(result, "M:Service.Ordered(System.Int32)"));
    }

    // ---- The analyzer reads the same contract classes (KTD9) ----

    [Fact]
    public void TheDiagnoserReportsWhatTheBuildReportsForContractClassesAndDependencies()
    {
        var compilation = CompilationFactory.Create([new SourceFile("Test.cs", "using Warrant;\n" + PaymentExample + """

            [ContractFor(typeof(IPaymentStore))]
            internal abstract class Twin : IPaymentStore
            {
                public abstract Task<Payment?> GetPayment(int id);
                public abstract Task SavePayment(Payment p);
            }
            """)], checkOverflow: false);
        var full = Extractor.Extract(compilation, new ExtractionOptions { BuildDefines = true });
        var diagnoser = new Diagnoser(compilation);

        var reported = diagnoser.Members().SelectMany(m => diagnoser.Member(m))
            .Concat(diagnoser.ContractClasses().SelectMany(t => diagnoser.ContractClass(t)))
            .ToHashSet();

        Assert.Equal(full.Diagnostics.ToHashSet(), reported);
        Assert.Equal("second contract class for an interface", Assert.Single(full.Diagnostics).Construct);
        Assert.NotNull(full.Find(ProcessKey));
    }

    [Fact]
    public void AContractClassIsFoundOnlyInTheVerifiedMethodsCompilation()
    {
        var library = CompilationFactory.Create(
            [new SourceFile("Lib.cs", """
                using Warrant;
                namespace Lib;
                public interface ICounter { int Next(int x); }

                [ContractFor(typeof(ICounter))]
                internal abstract class CounterContract : ICounter { public abstract int Next(int x); }
                """)],
            checkOverflow: false,
            assemblyName: "Lib");
        using var image = new MemoryStream();
        Assert.True(library.Emit(image).Success);
        var consumer = CompilationFactory.Create(
            [new SourceFile("Test.cs", """
                using Warrant;
                public sealed class Holder(Lib.ICounter counter)
                {
                    [Verified] public int Run(int x) => counter.Next(x);
                }
                """)],
            checkOverflow: false).AddReferences(MetadataReference.CreateFromImage(image.ToArray()));

        var result = Extractor.Extract(consumer);

        Assert.Equal("WRT0002 | dependency without a contract class", Only(result, "M:Holder.Run(System.Int32)"));
        var diagnoser = new Diagnoser(consumer);
        Assert.Equal(result.Diagnostics, diagnoser.Member(diagnoser.Members().Single()));
    }
}
