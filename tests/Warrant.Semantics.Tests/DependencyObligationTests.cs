using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>
/// Dependency obligations (plan M6 U19, KTD4, KTD9, KTD22, KTD25): a method that calls a dependency is a function of one
/// operation per (dependency, member) pair, its obligation takes each member's contract as a hypothesis over every world
/// (design D9), an external call threads the world, <c>await</c> is <c>bind</c>, and a contract-class member's
/// <c>Spec</c> calls are checked not to be unsatisfiable. The engine proves these obligations (plan U20, <c>ExternalCallTests</c>).
/// </summary>
public sealed class DependencyObligationTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private static readonly Expr TypeT = Expr.Sort(Level.One);
    private static readonly Expr Int32T = C("Int32");
    private static readonly Expr ClrExnT = C("Warrant.ClrExn");
    private static readonly Expr UnitT = C("Unit");

    private static Name N(string dotted) => Name.Parse(dotted);

    private static Expr C(string dotted, params Level[] levels) => Expr.Const(N(dotted), levels);

    private static Expr I(int n) => Literals.Int32(n);

    private (Translation Translation, KernelEnvironment Env) Translate(string source)
    {
        var translation = TranslationCorpus.Translate(TranslationCorpus.Inline("#nullable enable\nusing System;\nusing System.Threading.Tasks;\n" + source), bundle.Env);
        return (translation, TranslationCorpus.Admit(bundle, translation));
    }

    /// <summary>A unit of an M6 corpus compilation and every unit it depends on, translated and admitted.</summary>
    private (Translation Translation, KernelEnvironment Env) TranslateCorpus(string compilation, string key)
    {
        var result = Extraction.Extractor.Extract(CorpusSet.M6.Compile(compilation));
        var byKey = result.Units.ToDictionary(u => u.Key, u => u.Unit, StringComparer.Ordinal);
        var closure = new Dictionary<string, VirUnit>(StringComparer.Ordinal);
        void Add(string k)
        {
            if (closure.TryAdd(k, byKey[k]))
            {
                foreach (var dep in byKey[k].Deps)
                {
                    Add(dep);
                }
            }
        }
        Add(key);
        var translation = Translator.Translate(closure.Values, bundle.Env);
        return (translation, TranslationCorpus.Admit(bundle, translation));
    }

    private static DefinitionInfo Definition(Translation translation, string key) =>
        Assert.IsType<DefinitionDecl>(Assert.Single(translation.Find(key)!.Declarations)).Value;

    private static void AssertProposition(KernelEnvironment env, Expr statement) =>
        KernelThread.Run(() =>
        {
            var tc = new TypeChecker(env);
            Assert.Equal(Expr.Sort(Level.Zero), tc.Whnf(tc.Check(statement)));
        });

    // ---- The D9 statement (KTD9) ----

    private const string Payments = "Corpus.M6.Payments";
    private const string ProcessPayment = "M:Corpus.M6.Payments.PaymentService.ProcessPayment(System.Int32)";
    private const string GetPayment = "M:Corpus.M6.Payments.IPaymentStore.GetPayment(System.Int32)";
    private const string SavePayment = "M:Corpus.M6.Payments.IPaymentStore.SavePayment(Corpus.M6.Payments.Payment)";

    /// <summary>
    /// <c>ProcessPayment</c>'s obligation, written out by hand in the D9 shape:
    /// <code>
    /// ∀ (σ : Type) (store_GetPayment : Int32 → ClrM σ (Option Payment)) (store_SavePayment : Payment → ClrM σ Unit)
    ///   (paymentId : Int32),
    ///   (∀ (id : Int32), ⦃⌜True⌝⦄ store_GetPayment id ⦃post⟨fun r =&gt; ⌜r.isNone = true ∨ (r.getD default).Id = id⌝, allowed⟩⦄) →
    ///   (∀ (p : Payment), ⦃⌜True⌝⦄ store_SavePayment p ⦃post⟨fun r =&gt; ⌜True⌝, allowed⟩⦄) →
    ///   ⦃⌜True⌝⦄ ProcessPayment store_GetPayment store_SavePayment paymentId ⦃post⟨fun r =&gt; ⌜¬r = Success ∨ paymentId &gt; 0⌝, allowed⟩⦄
    /// </code>
    /// </summary>
    private static Expr HandWrittenProcessPaymentObligation(Name function)
    {
        var lctx = new LocalContext();
        var ngen = new NameGenerator(Name.From("_test"));
        Expr Local(string name, Expr type) => lctx.MkLocalDecl(ngen, Name.From(name), type);
        var payment = Expr.Const(LeanNames.ForKey($"T:{Payments}.Payment"));
        var nullablePayment = Expr.App(C("Option", Level.Zero), payment);
        var result = Expr.Const(LeanNames.ForKey($"T:{Payments}.Result"));

        var σ = Local("σ", TypeT);
        Expr M(Expr alpha) => Expr.App(C("Warrant.ClrM"), σ, alpha);
        var idArg = Local("id", Int32T);
        var get = Local("store_GetPayment", lctx.MkPi([idArg], M(nullablePayment)));
        var pArg = Local("p", payment);
        var save = Local("store_SavePayment", lctx.MkPi([pArg], M(UnitT)));
        var paymentId = Local("paymentId", Int32T);
        Expr Assertion(Expr p) => Expr.App(C("Std.Do.SPred.pure", Level.Zero), Expr.App(C("Std.Do.PostShape.args", Level.Zero), Triples.Shape(σ)), p);
        Expr Triple(Expr alpha, Expr program, Expr ensures, Expr r) =>
            Triples.Triple(σ, alpha, program, Assertion(C("True")), Triples.Post(σ, alpha, lctx.MkLambda([r], Assertion(ensures))));

        // GetPayment's contract: r is null || r.Id == id, where r.Id reads the record's Id once r is known not to be null.
        var id = Local("id", Int32T);
        var r1 = Local("r", nullablePayment);
        var isNull = Expr.App(C("Eq", Level.One), C("Bool"), Expr.App(C("Option.isNone", Level.Zero), payment, r1), C("Bool.true"));
        var zeroDecimal = Literals.Decimal(new DecimalLitExpr(false, 0, 0));
        var defaultPayment = Expr.App(Expr.Const(LeanNames.Constructor($"T:{Payments}.Payment")), I(0), zeroDecimal, I(0));
        var recordId = Expr.Proj(LeanNames.ForKey($"T:{Payments}.Payment"), 0, Expr.App(C("Warrant.Nullable.coalesce"), payment, r1, defaultPayment));
        var getEnsures = Expr.App(C("Or"), isNull, Expr.App(C("Eq", Level.One), Int32T, recordId, id));
        var hGet = Local("store_GetPayment_spec", lctx.MkPi([id], Triple(nullablePayment, Expr.App(get, id), getEnsures, r1)));

        // SavePayment's contract, => default!: nothing.
        var p = Local("p", payment);
        var r2 = Local("r", UnitT);
        var hSave = Local("store_SavePayment_spec", lctx.MkPi([p], Triple(UnitT, Expr.App(save, p), C("True"), r2)));

        // r != Result.Success || paymentId > 0
        var r = Local("r", result);
        var success = Expr.Const(LeanNames.Member($"T:{Payments}.Result", "Success"));
        var ensures = Expr.App(C("Or"),
            Expr.App(C("Not"), Expr.App(C("Eq", Level.One), Int32T, r, success)),
            Expr.App(C("GT.gt", Level.Zero), Int32T, C("instLTInt32"), paymentId, I(0)));
        var program = Expr.App(Expr.Const(function), σ, get, save, paymentId);
        return lctx.MkPi([σ, get, save, paymentId, hGet, hSave], Triple(result, program, ensures, r));
    }

    [Fact]
    public void ProcessPaymentsObligationBindsTwoOperationsAndTheirContractsAsHypotheses()
    {
        var (translation, env) = TranslateCorpus("accepted", ProcessPayment);
        var unit = translation.Find(ProcessPayment)!;
        var contract = unit.Contract!;
        Assert.True(contract.Raising);
        Assert.Equal(2, contract.Operations);
        Assert.Equal(6, contract.Binders);
        Assert.Equal(
            ["σ", "store_GetPayment", "store_SavePayment", "paymentId", "store_GetPayment_spec", "store_SavePayment_spec"],
            contract.BinderNames.Select(n => n.ToString()));
        Assert.Equal(HandWrittenProcessPaymentObligation(unit.Name), contract.Theorem.Type);
        AssertProposition(env, contract.Theorem.Type);

        // The definition takes the operations after the world: ∀ {σ} get save (paymentId : Int32), ClrM σ Result.
        var type = Assert.IsType<ForallExpr>(Definition(translation, ProcessPayment).Type);
        Assert.Equal(BinderInfo.Implicit, type.BinderInfo);
        var get = Assert.IsType<ForallExpr>(type.Body);
        Assert.Equal("store_GetPayment", get.BinderName.ToString());
        var save = Assert.IsType<ForallExpr>(get.Body);
        Assert.Equal("store_SavePayment", save.BinderName.ToString());
        var paymentId = Assert.IsType<ForallExpr>(save.Body);
        Assert.Equal(Int32T, paymentId.BinderType);
        Assert.Equal(Expr.App(C("Warrant.ClrM"), Expr.BVar(3), Expr.Const(LeanNames.ForKey($"T:{Payments}.Result"))), paymentId.Body);
    }

    [Fact]
    public void AHypothesisStatesTheMembersRequiresAndEnsuresAtEveryArgument()
    {
        var (translation, env) = Translate("""
            public interface IStore { int Count(int id); }

            [ContractFor(typeof(IStore))]
            internal abstract class StoreContract : IStore
            {
                public int Count(int id) { Spec.Requires(id > 0); Spec.Ensures<int>(r => r >= id); return default!; }
            }

            public sealed class S(IStore store)
            {
                [Verified]
                public int Size(int id)
                {
                    Spec.Requires(id > 0);
                    Spec.Ensures<int>(r => r >= 1);
                    return store.Count(id);
                }
            }
            """);
        var contract = translation.Find("M:S.Size(System.Int32)")!.Contract!;
        AssertProposition(env, contract.Theorem.Type);
        Assert.Equal(1, contract.Operations);
        // ∀ σ store_Count id, (∀ id, ⦃⌜id > 0⌝⦄ store_Count id ⦃⇓r => ⌜r ≥ id⌝⦄) → …
        var hypothesis = Assert.IsType<ForallExpr>(Assert.IsType<ForallExpr>(Assert.IsType<ForallExpr>(Assert.IsType<ForallExpr>(contract.Theorem.Type).Body).Body).Body);
        Assert.Equal("store_Count_spec", hypothesis.BinderName.ToString());
        var x = Assert.IsType<ForallExpr>(hypothesis.BinderType);
        var args = x.Body.GetAppArgs();
        Assert.Equal(Expr.App(Expr.BVar(2), Expr.BVar(0)), args[4]);
        Assert.Equal(Expr.App(C("GT.gt", Level.Zero), Int32T, C("instLTInt32"), Expr.BVar(0), I(0)), args[5].GetAppArgs()[1]);
        var ensures = Assert.IsType<LamExpr>(args[6].GetAppArgs()[2]).Body.GetAppArgs()[1];
        Assert.Equal(Expr.App(C("GE.ge", Level.Zero), Int32T, C("instLEInt32"), Expr.BVar(0), Expr.BVar(1)), ensures);
        // The body is the operation itself: Size σ op id = op id.
        Assert.Equal(
            Expr.Lam(N("σ"), TypeT, Expr.Lam(N("store_Count"), Expr.Forall(N("id"), Int32T, Expr.App(C("Warrant.ClrM"), Expr.BVar(1), Int32T)),
                Expr.Lam(N("id"), Int32T, Expr.App(Expr.BVar(1), Expr.BVar(0)))), BinderInfo.Implicit),
            Definition(translation, "M:S.Size(System.Int32)").Value);
    }

    // ---- External calls thread the world (KTD4) ----

    /// <summary>
    /// <c>fun σ s =&gt; (f σ args s)</c> run from the state <paramref name="state"/> of the world <c>Nat</c>, against
    /// <paramref name="expected"/>, the <c>Except</c> and final state.
    /// </summary>
    private static bool Runs(KernelEnvironment env, Translation translation, string key, Expr result, Expr state, Expr expected, params Expr[] args)
    {
        var nat = C("Nat");
        var except = Expr.App(C("Except", Level.Zero, Level.Zero), ClrExnT, result);
        var stateM = Expr.App(C("StateM", Level.Zero), nat);
        var run = Expr.App(C("StateT.run", Level.Zero, Level.Zero), nat, C("Id", Level.Zero), except,
            Expr.App(C("ExceptT.run", Level.Zero, Level.Zero), ClrExnT, stateM, result, Expr.App(Expr.Const(translation.Find(key)!.Name), [nat, .. args])),
            state);
        return KernelThread.Run(() =>
        {
            var tc = new TypeChecker(env);
            tc.Check(run);
            return tc.IsDefEq(run, expected);
        });
    }

    [Fact]
    public void ACallMadeTwiceThreadsTheWorldSoAMockCanAnswerEachCallDifferently()
    {
        var (translation, env) = Translate("""
            public interface ICounter { int Next(); }

            [ContractFor(typeof(ICounter))]
            internal abstract class CounterContract : ICounter
            {
                public int Next() => default!;
            }

            public sealed class S(ICounter counter)
            {
                [Verified]
                public int Gap()
                {
                    var a = counter.Next();
                    var b = counter.Next();
                    return b - a;
                }
            }
            """);
        // The world is the number of calls made: the mock returns it, then counts the call (KTD21's reply tape).
        var nat = C("Nat");
        Expr Ok(Expr value) => Expr.App(C("Except.ok", Level.Zero, Level.Zero), ClrExnT, Int32T, value);
        var next = Expr.Lam(N("s"), nat, Expr.App(C("Prod.mk", Level.Zero, Level.Zero),
            Expr.App(C("Except", Level.Zero, Level.Zero), ClrExnT, Int32T), nat,
            Ok(Expr.App(C("Int32.ofNat"), Expr.BVar(0))), Expr.App(C("Nat.succ"), Expr.BVar(0))));
        Expr Result(int value, int calls) => Expr.App(C("Prod.mk", Level.Zero, Level.Zero),
            Expr.App(C("Except", Level.Zero, Level.Zero), ClrExnT, Int32T), nat, Ok(I(value)), Expr.NatLit(calls));
        const string gap = "M:S.Gap";
        Assert.True(Runs(env, translation, gap, Int32T, Expr.NatLit(0), Result(1, 2), next));
        Assert.True(Runs(env, translation, gap, Int32T, Expr.NatLit(5), Result(1, 7), next));
        Assert.False(Runs(env, translation, gap, Int32T, Expr.NatLit(0), Result(0, 2), next), "the two calls are not the same call");
    }

    // ---- Async is sequencing (KTD22) ----

    [Fact]
    public void AwaitingAVerifiedAsyncMethodIsABindAndATaskMethodIsAClrMUnitProgram()
    {
        const string next = "M:Corpus.M6.Dependencies.Steps.Next(System.Int32)";
        const string run = "M:Corpus.M6.Dependencies.Steps.Run(System.Int32)";
        var (translation, env) = TranslateCorpus("accepted", run);

        // Next never awaits and cannot raise: Task<int> is its value type, as in M4.
        Assert.Equal(Expr.Forall(N("x"), Int32T, Int32T), Definition(translation, next).Type);
        // Run is async Task: ∀ {σ} (x : Int32), ClrM σ Unit.
        var definition = Definition(translation, run);
        Assert.Equal(
            Expr.Forall(N("σ"), TypeT, Expr.Forall(N("x"), Int32T, Expr.App(C("Warrant.ClrM"), Expr.BVar(1), UnitT)), BinderInfo.Implicit),
            definition.Type);
        // await Next(x); is pure (Next x) >>= fun v => pure (), the callee node the walker proves Next's precondition at.
        var body = Assert.IsType<LamExpr>(Assert.IsType<LamExpr>(definition.Value).Body).Body;
        Assert.Equal(C("Bind.bind", Level.Zero, Level.Zero), body.GetAppFn());
        var args = body.GetAppArgs();
        Assert.Equal(C("Pure.pure", Level.Zero, Level.Zero), args[4].GetAppFn());
        Assert.Equal(Expr.App(Expr.Const(translation.Find(next)!.Name), Expr.BVar(0)), args[4].GetAppArgs()[3]);
        var rest = Assert.IsType<LamExpr>(args[5]).Body;
        Assert.Equal(C("Pure.pure", Level.Zero, Level.Zero), rest.GetAppFn());
        Assert.Equal(C("Unit.unit"), rest.GetAppArgs()[3]);
        AssertProposition(env, translation.Find(run)!.Contract!.Theorem.Type);
    }

    [Fact]
    public void ATaskReturningCallIsAwaitedAsABindOfItsProgram()
    {
        var (translation, env) = Translate("""
            public interface IStore { Task<int> Load(int id); Task Save(int id); void Log(int id); }

            [ContractFor(typeof(IStore))]
            internal abstract class StoreContract : IStore
            {
                public Task<int> Load(int id) { Spec.Ensures<int>(r => r >= 0); return default!; }
                public Task Save(int id) => default!;
                public void Log(int id) { }
            }

            public sealed class S(IStore store)
            {
                [Verified]
                public async Task<int> Twice(int id)
                {
                    var a = await store.Load(id);
                    await store.Save(a);
                    store.Log(a);
                    return a;
                }

                [Verified]
                public async Task Store(int id) => await store.Save(id);
            }
            """);
        // Twice: Load, Save and Log, in that order, from the operations bound after the world.
        var twice = Definition(translation, "M:S.Twice(System.Int32)");
        Expr Op(Expr alpha) => Expr.Forall(N("id"), Int32T, Expr.App(C("Warrant.ClrM"), Expr.BVar(1), alpha));
        var σ = Assert.IsType<ForallExpr>(twice.Type);
        var load = Assert.IsType<ForallExpr>(σ.Body);
        Assert.Equal(("store_Load", Op(Int32T)), (load.BinderName.ToString(), load.BinderType));
        var log = Assert.IsType<ForallExpr>(load.Body);
        Assert.Equal("store_Log", log.BinderName.ToString());
        var save = Assert.IsType<ForallExpr>(log.Body);
        Assert.Equal("store_Save", save.BinderName.ToString());
        var program = Assert.IsType<LamExpr>(Assert.IsType<LamExpr>(Assert.IsType<LamExpr>(Assert.IsType<LamExpr>(Assert.IsType<LamExpr>(twice.Value).Body).Body).Body).Body).Body;
        // store_Load id >>= fun a => store_Save a >>= fun _ => store_Log a >>= fun _ => pure a
        Assert.Equal(Expr.App(Expr.BVar(3), Expr.BVar(0)), program.GetAppArgs()[4]);
        var afterLoad = Assert.IsType<LamExpr>(program.GetAppArgs()[5]).Body;
        Assert.Equal(Expr.App(Expr.BVar(2), Expr.BVar(0)), afterLoad.GetAppArgs()[4]);
        var afterSave = Assert.IsType<LamExpr>(afterLoad.GetAppArgs()[5]).Body;
        Assert.Equal(Expr.App(Expr.BVar(4), Expr.BVar(1)), afterSave.GetAppArgs()[4]);
        // `=> await store.Save(id)` in an async Task is Save's program itself.
        Assert.Equal(
            Expr.Lam(N("σ"), TypeT, Expr.Lam(N("store_Save"), Op(UnitT), Expr.Lam(N("id"), Int32T, Expr.App(Expr.BVar(1), Expr.BVar(0)))), BinderInfo.Implicit),
            Definition(translation, "M:S.Store(System.Int32)").Value);
        AssertProposition(env, translation.Find("M:S.Twice(System.Int32)")!.Contract!.Theorem.Type);
    }

    // ---- Contract-class members (KTD10, KTD25, KTD26) ----

    [Fact]
    public void AContractMemberWhoseEnsuresAdmitsNoResultHasAVacuityCheckAtItsEnsures()
    {
        var (translation, env) = Translate("""
            public interface IStore { int Count(int id); }

            [ContractFor(typeof(IStore))]
            internal abstract class StoreContract : IStore
            {
                public int Count(int id) { Spec.Requires(id > 0); Spec.Ensures<int>(r => r > 0 && r < 0); return default!; }
            }

            public sealed class S(IStore store)
            {
                [Verified] public int Size(int id) => store.Count(id);
            }
            """);
        var unit = translation.Find("M:IStore.Count(System.Int32)")!;
        Assert.Equal(VirUnitKind.Contract, unit.Kind);
        Assert.Empty(unit.Declarations);
        Assert.Null(unit.Contract);
        var member = unit.MemberContract!;
        Assert.Empty(member.WellDefinedness);
        Assert.Collection(
            member.Vacuity,
            requires => Assert.IsType<RequiresStmt>(requires.Node),
            ensures =>
            {
                Assert.IsType<EnsuresStmt>(ensures.Node);
                Assert.Equal("Cs.IStore.«Count(System.Int32)».$vacuous_2", ensures.Theorem.Name.ToString());
                Assert.Equal(4, ensures.Binders);
                // ∀ (id r : Int32), id > 0 → r > 0 ∧ r < 0 → False
                Expr Gt(Expr a, Expr b) => Expr.App(C("GT.gt", Level.Zero), Int32T, C("instLTInt32"), a, b);
                Expr Lt(Expr a, Expr b) => Expr.App(C("LT.lt", Level.Zero), Int32T, C("instLTInt32"), a, b);
                Assert.Equal(
                    Expr.Forall(N("id"), Int32T, Expr.Forall(N("r"), Int32T, Expr.Forall(N("h"), Gt(Expr.BVar(1), I(0)),
                        Expr.Forall(N("h"), Expr.App(C("And"), Gt(Expr.BVar(1), I(0)), Lt(Expr.BVar(1), I(0))), C("False"))))),
                    ensures.Theorem.Type);
                AssertProposition(env, ensures.Theorem.Type);
            });
    }

    [Fact]
    public void AContractMembersPartialOperationGetsAWellDefinednessObligationUnderItsGuard()
    {
        var (translation, env) = TranslateCorpus("accepted", ProcessPayment);
        var member = translation.Find(GetPayment)!.MemberContract!;
        // r.Id in r is null || r.Id == id: the unwrap does not raise, given r is not null.
        var wd = Assert.Single(member.WellDefinedness);
        Assert.Equal(SpecObligationKind.WellDefinedOperation, wd.Kind);
        Assert.Equal(4, wd.Binders);
        AssertProposition(env, wd.Theorem.Type);
        Assert.Single(member.Vacuity);
        Assert.Empty(translation.Find(SavePayment)!.MemberContract!.Vacuity);
    }

    // ---- The M6 corpus ----

    /// <summary>Every compilation of the M6 corpus translates in full now, and every declaration and statement is admitted.</summary>
    [Theory]
    [InlineData("accepted")]
    [InlineData("refuted")]
    [InlineData("checked-project")]
    public void TheM6CorpusTranslates(string compilation)
    {
        var result = Extraction.Extractor.Extract(CorpusSet.M6.Compile(compilation));
        var translation = Translator.Translate(result.Units.Select(u => u.Unit), bundle.Env);
        var env = TranslationCorpus.Admit(bundle, translation);
        foreach (var unit in translation.Units)
        {
            if (unit.Contract is { } contract)
            {
                AssertProposition(env, contract.Theorem.Type);
            }
            foreach (var obligation in unit.MemberContract is { } member ? member.Vacuity.Concat(member.WellDefinedness) : [])
            {
                AssertProposition(env, obligation.Theorem.Type);
            }
        }
    }
}
