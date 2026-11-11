using System.Numerics;
using System.Runtime.CompilerServices;
using FsCheck;
using FsCheck.Fluent;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Semantics.Tests;

/// <summary>
/// CLR-agreement tests (docs/m4/07, plan U9, KTD19): each row of the operator and condition tables, applied to literals
/// of boundary operands and, as a property with shrinking and a pinned seed, of random operands, is definitionally equal in the kernel to the literal of the result C# computes
/// (unchecked). The literal encoder is checked on its own against the CLR's bit patterns, because both sides of every
/// other comparison go through it. The operations M4 rejects have their CLR behaviour pinned on the CLR side only.
/// </summary>
public sealed class ClrAgreementTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    /// <summary>Cases per property by default; <see cref="Pbt"/> pins the seed and reads the environment (M5a KTD26).</summary>
    private const int Cases = 150;

    private static readonly Expr BitVecToNat = Expr.Const(Name.Parse("BitVec.toNat"));
    private static readonly Expr Int32ToBitVec = Expr.Const(Name.Parse("Int32.toBitVec"));
    private static readonly Expr Int64ToBitVec = Expr.Const(Name.Parse("Int64.toBitVec"));
    private static readonly Expr NatType = Expr.Const(Name.Parse("Nat"));

    private readonly KernelEnvironment env = bundle.Fork();

    // ------------------------------------------------------------------ rows

    /// <summary>An arithmetic row: the CIC term builder and the C# meaning on <c>int</c> and on <c>long</c>.</summary>
    private sealed record ArithmeticRow(string Name, Func<VirPrimitive, Expr, Expr, Expr> Build, Func<int, int, int> Int32, Func<long, long, long> Int64);

    private static readonly ArithmeticRow[] ArithmeticRows =
    [
        new("+", (p, a, b) => Operators.Binary(BinaryOp.Add, p, a, b), (a, b) => unchecked(a + b), (a, b) => unchecked(a + b)),
        new("-", (p, a, b) => Operators.Binary(BinaryOp.Sub, p, a, b), (a, b) => unchecked(a - b), (a, b) => unchecked(a - b)),
        new("*", (p, a, b) => Operators.Binary(BinaryOp.Mul, p, a, b), (a, b) => unchecked(a * b), (a, b) => unchecked(a * b)),
    ];

    /// <summary>A comparison row as a value: <c>decide</c> of its condition, against the C# result.</summary>
    private sealed record ComparisonRow(string Name, Func<VirPrimitive, Expr, Expr, Condition> Build, Func<long, long, bool> Clr);

    private static readonly ComparisonRow[] ComparisonRows =
    [
        new("==", Conditions.Eq, (a, b) => a == b),
        new("!=", (p, a, b) => Conditions.Not(Conditions.Eq(p, a, b)), (a, b) => a != b),
        new("<", Conditions.Lt, (a, b) => a < b),
        new("<=", Conditions.Le, (a, b) => a <= b),
        new(">", (p, a, b) => Conditions.Lt(p, b, a), (a, b) => a > b),
        new(">=", (p, a, b) => Conditions.Le(p, b, a), (a, b) => a >= b),
    ];

    public static TheoryData<string> ArithmeticNames() => [.. ArithmeticRows.Select(r => r.Name)];

    public static TheoryData<string> ComparisonNames() => [.. ComparisonRows.Select(r => r.Name)];

    // ------------------------------------------------------------------ kernel oracle

    /// <summary>The term type-checks at <paramref name="type"/> and is definitionally equal to <paramref name="expected"/>.</summary>
    private bool Agrees(Expr term, Expr expected, Expr type)
    {
        var tc = new TypeChecker(env);
        return tc.IsDefEq(tc.Check(term), type) && tc.IsDefEq(term, expected);
    }

    private bool AgreesInt32(Expr term, int clr) => Agrees(term, Literals.Int32(clr), Literals.Type(VirPrimitive.Int32));

    private bool AgreesInt64(Expr term, long clr) => Agrees(term, Literals.Int64(clr), Literals.Type(VirPrimitive.Int64));

    private bool AgreesBool(Expr term, bool clr) => Agrees(term, Literals.Bool(clr), Literals.Type(VirPrimitive.Bool));

    // ------------------------------------------------------------------ arithmetic

    [Theory]
    [MemberData(nameof(ArithmeticNames))]
    public void Int32ArithmeticAgrees(string name)
    {
        var row = ArithmeticRows.Single(r => r.Name == name);
        bool Ok((int A, int B) p) =>
            AgreesInt32(row.Build(VirPrimitive.Int32, Literals.Int32(p.A), Literals.Int32(p.B)), row.Int32(p.A, p.B));
        KernelThread.Run(() =>
        {
            Assert.All(Generators.Int32BoundaryPairs(), p => Assert.True(Ok(p), $"{p.Item1} {name} {p.Item2}"));
            Pbt.Check(Prop.ForAll(Generators.Int32Pairs, Ok), Cases);
        });
    }

    [Theory]
    [MemberData(nameof(ArithmeticNames))]
    public void Int64ArithmeticAgrees(string name)
    {
        var row = ArithmeticRows.Single(r => r.Name == name);
        bool Ok((long A, long B) p) =>
            AgreesInt64(row.Build(VirPrimitive.Int64, Literals.Int64(p.A), Literals.Int64(p.B)), row.Int64(p.A, p.B));
        KernelThread.Run(() =>
        {
            Assert.All(Generators.Int64BoundaryPairs(), p => Assert.True(Ok(p), $"{p.Item1} {name} {p.Item2}"));
            Pbt.Check(Prop.ForAll(Generators.Int64Pairs, Ok), Cases);
        });
    }

    [Fact]
    public void NegationAgrees()
    {
        bool Ok32(int x) => AgreesInt32(Operators.Neg(VirPrimitive.Int32, Literals.Int32(x)), unchecked(-x));
        bool Ok64(long x) => AgreesInt64(Operators.Neg(VirPrimitive.Int64, Literals.Int64(x)), unchecked(-x));
        KernelThread.Run(() =>
        {
            Assert.All(Generators.Int32Boundaries, x => Assert.True(Ok32(x), $"-({x})"));
            Assert.All(Generators.Int64Boundaries, x => Assert.True(Ok64(x), $"-({x}L)"));
            Pbt.Check(Prop.ForAll(Generators.Int32s, Ok32), Cases);
            Pbt.Check(Prop.ForAll(Generators.Int64s, Ok64), Cases);
        });
    }

    // ------------------------------------------------------------------ comparisons

    [Theory]
    [MemberData(nameof(ComparisonNames))]
    public void Int32ComparisonAgrees(string name)
    {
        var row = ComparisonRows.Single(r => r.Name == name);
        bool Ok((int A, int B) p) =>
            AgreesBool(Operators.Decide(row.Build(VirPrimitive.Int32, Literals.Int32(p.A), Literals.Int32(p.B))), row.Clr(p.A, p.B));
        KernelThread.Run(() =>
        {
            Assert.All(Generators.Int32BoundaryPairs(), p => Assert.True(Ok(p), $"{p.Item1} {name} {p.Item2}"));
            Pbt.Check(Prop.ForAll(Generators.Int32Pairs, Ok), Cases);
        });
    }

    [Theory]
    [MemberData(nameof(ComparisonNames))]
    public void Int64ComparisonAgrees(string name)
    {
        var row = ComparisonRows.Single(r => r.Name == name);
        bool Ok((long A, long B) p) =>
            AgreesBool(Operators.Decide(row.Build(VirPrimitive.Int64, Literals.Int64(p.A), Literals.Int64(p.B))), row.Clr(p.A, p.B));
        KernelThread.Run(() =>
        {
            Assert.All(Generators.Int64BoundaryPairs(), p => Assert.True(Ok(p), $"{p.Item1} {name} {p.Item2}"));
            Pbt.Check(Prop.ForAll(Generators.Int64Pairs, Ok), Cases);
        });
    }

    [Fact]
    public void NamedComparisonsAgree() => KernelThread.Run(() =>
    {
        var lt = Conditions.Lt(VirPrimitive.Int32, Literals.Int32(int.MinValue), Literals.Int32(int.MaxValue));
        Assert.True(AgreesBool(Operators.Decide(lt), true), "int.MinValue < int.MaxValue");
        Assert.True(AgreesBool(Operators.Decide(Conditions.Lt(VirPrimitive.Int32, Literals.Int32(-1), Literals.Int32(1))), true), "-1 < 1");
        Assert.True(AgreesBool(Operators.Decide(Conditions.Lt(VirPrimitive.Int32, Literals.Int32(1), Literals.Int32(-1))), false), "!(1 < -1)");
    });

    // ------------------------------------------------------------------ conversions

    [Fact]
    public void ConversionsAgree()
    {
        bool Widen(int x) => AgreesInt64(Operators.Convert(VirPrimitive.Int32, VirPrimitive.Int64, Literals.Int32(x)), x);
        bool Narrow(long x) => AgreesInt32(Operators.Convert(VirPrimitive.Int64, VirPrimitive.Int32, Literals.Int64(x)), unchecked((int)x));
        KernelThread.Run(() =>
        {
            Assert.All(Generators.Int32Boundaries, x => Assert.True(Widen(x), $"(long){x}"));
            Assert.All(Generators.Int64Boundaries.Concat(Generators.Int32Boundaries.Select(x => (long)x)), x => Assert.True(Narrow(x), $"(int){x}L"));
            Assert.True(Narrow(3000000000L), "(int)3000000000L");
            Assert.Equal(-1294967296, unchecked((int)Runtime(3000000000L)));
            Pbt.Check(Prop.ForAll(Generators.Int32s, Widen), Cases);
            Pbt.Check(Prop.ForAll(Generators.Int64s, Narrow), Cases);
        });
    }

    // ------------------------------------------------------------------ bool

    private static readonly (bool X, bool Y)[] BoolPairs = [(false, false), (false, true), (true, false), (true, true)];

    [Fact]
    public void BoolValueOperatorsAgree() => KernelThread.Run(() =>
    {
        foreach (var (x, y) in BoolPairs)
        {
            Expr a = Literals.Bool(x), b = Literals.Bool(y);
            Assert.True(AgreesBool(Operators.And(a, b), x && y), $"{x} && {y}");
            Assert.True(AgreesBool(Operators.And(a, b), x & y), $"{x} & {y}");
            Assert.True(AgreesBool(Operators.Or(a, b), x || y), $"{x} || {y}");
            Assert.True(AgreesBool(Operators.Or(a, b), x | y), $"{x} | {y}");
            Assert.True(AgreesBool(Operators.Xor(a, b), x ^ y), $"{x} ^ {y}");
            Assert.True(AgreesBool(Operators.Decide(Conditions.Eq(VirPrimitive.Bool, a, b)), x == y), $"{x} == {y}");
            Assert.True(AgreesBool(Operators.Decide(Conditions.Not(Conditions.Eq(VirPrimitive.Bool, a, b))), x != y), $"{x} != {y}");
        }
        foreach (var x in new[] { false, true })
        {
            Assert.True(AgreesBool(Operators.Not(Literals.Bool(x)), !x), $"!{x}");
        }
    });

    /// <summary>The condition forms of the Boolean operators, read back as values with <c>decide</c>.</summary>
    [Fact]
    public void BoolConditionsAgree() => KernelThread.Run(() =>
    {
        foreach (var (x, y) in BoolPairs)
        {
            var px = Conditions.IsTrue(Literals.Bool(x));
            var py = Conditions.IsTrue(Literals.Bool(y));
            Assert.True(AgreesBool(Operators.Decide(px), x), $"{x}");
            Assert.True(AgreesBool(Operators.Decide(Conditions.Not(px)), !x), $"!{x}");
            Assert.True(AgreesBool(Operators.Decide(Conditions.And(px, py)), x && y), $"{x} && {y}");
            Assert.True(AgreesBool(Operators.Decide(Conditions.Or(px, py)), x || y), $"{x} || {y}");
            Assert.True(AgreesBool(Operators.Decide(Conditions.Implies(px, py)), !x || y), $"Implies({x}, {y})");
        }
    });

    // ------------------------------------------------------------------ literals, independently of the encoder

    /// <summary><c>BitVec.toNat (T.toBitVec lit)</c> reduces to the unsigned bit pattern C# computes.</summary>
    private bool BitPatternAgrees(Expr toBitVec, int width, Expr literal, BigInteger clr)
    {
        var term = Expr.App(BitVecToNat, Expr.NatLit(width), Expr.App(toBitVec, literal));
        var tc = new TypeChecker(env);
        return tc.IsDefEq(tc.Check(term), NatType) && tc.Whnf(term).Equals(Expr.NatLit(clr));
    }

    private bool Int32BitsAgree(int x) => BitPatternAgrees(Int32ToBitVec, 32, Literals.Int32(x), unchecked((uint)x));

    private bool Int64BitsAgree(long x) => BitPatternAgrees(Int64ToBitVec, 64, Literals.Int64(x), unchecked((ulong)x));

    [Fact]
    public void LiteralsReduceToTheClrBitPattern() => KernelThread.Run(() =>
    {
        Assert.All(Generators.Int32Boundaries, x => Assert.True(Int32BitsAgree(x), $"{x}"));
        Assert.All(Generators.Int64Boundaries, x => Assert.True(Int64BitsAgree(x), $"{x}L"));
        Pbt.Check(Prop.ForAll(Generators.Int32s, Int32BitsAgree), Cases);
        Pbt.Check(Prop.ForAll(Generators.Int64s, Int64BitsAgree), Cases);
    });

    [Fact]
    public void TheBitPatternOracleRejectsAWrongPattern() => KernelThread.Run(() =>
    {
        Assert.False(BitPatternAgrees(Int32ToBitVec, 32, Literals.Int32(-1), uint.MaxValue - 1));
        Assert.False(BitPatternAgrees(Int32ToBitVec, 32, Literals.Int32(int.MinValue), 1u << 30));
    });

    // ------------------------------------------------------------------ raising operations in ClrM (M6 U3, KTD4, KTD6)

    /// <summary>
    /// A raising row: the <c>lean/Warrant/Checked.lean</c> models on <c>int</c> and on <c>long</c>, and the C# meaning,
    /// which may throw. Every row's CLR side runs in a <c>checked</c> context except <c>/</c> and <c>%</c>, which throw
    /// in any context.
    /// </summary>
    private sealed record RaisingRow(string Name, string Model, Func<int, int, int> Int32, Func<long, long, long> Int64);

    private static readonly RaisingRow[] RaisingRows =
    [
        new("checked +", "addChecked", (a, b) => checked(a + b), (a, b) => checked(a + b)),
        new("checked -", "subChecked", (a, b) => checked(a - b), (a, b) => checked(a - b)),
        new("checked *", "mulChecked", (a, b) => checked(a * b), (a, b) => checked(a * b)),
        new("/", "div", (a, b) => unchecked(a / b), (a, b) => unchecked(a / b)),
        new("%", "rem", (a, b) => unchecked(a % b), (a, b) => unchecked(a % b)),
    ];

    public static TheoryData<string> RaisingNames() => [.. RaisingRows.Select(r => r.Name)];

    private static readonly Expr TypeT = Expr.Sort(Level.One);
    private static readonly Expr ClrExnT = Expr.Const(Name.Parse("Warrant.ClrExn"));

    /// <summary>The <c>Warrant.ClrExn</c> constructor a CLR exception stands for (KTD4).</summary>
    private static Expr ClrExn(Exception e) => Expr.Const(Name.Parse("Warrant.ClrExn." + e switch
    {
        OverflowException => "overflow",
        DivideByZeroException => "divideByZero",
        NullReferenceException => "nullReference",
        InvalidOperationException => "invalidOperation",
        _ => throw new ArgumentException($"no ClrExn models {e.GetType()}", nameof(e)),
    }));

    /// <summary>The CLR exceptions a <c>Warrant.ClrExn</c> constructor stands for.</summary>
    private static bool IsModelled(Exception e) =>
        e is OverflowException or DivideByZeroException or NullReferenceException or InvalidOperationException;

    /// <summary>
    /// <c>fun (σ : Type) (s : σ) => (StateT.run (ExceptT.run (program σ)) s).1</c>: the <c>Except</c> component of the
    /// program run from an arbitrary world, which the kernel compares under a fresh <c>σ</c> and <c>s</c>.
    /// </summary>
    private static Expr RunFromAnyWorld(Expr result, Func<Expr, Expr> program)
    {
        var sigma = Expr.BVar(1);
        var except = Expr.App(Expr.Const(Name.Parse("Except"), Level.Zero, Level.Zero), ClrExnT, result);
        var stateM = Expr.App(Expr.Const(Name.Parse("StateM"), Level.Zero), sigma);
        var run = Expr.App(Expr.Const(Name.Parse("StateT.run"), Level.Zero, Level.Zero), sigma, Expr.Const(Name.Parse("Id"), Level.Zero), except,
            Expr.App(Expr.Const(Name.Parse("ExceptT.run"), Level.Zero, Level.Zero), ClrExnT, stateM, result, program(sigma)),
            Expr.BVar(0));
        var body = Expr.App(Expr.Const(Name.Parse("Prod.fst"), Level.Zero, Level.Zero), except, sigma, run);
        return Expr.Lam(Name.From("σ"), TypeT, Expr.Lam(Name.From("s"), Expr.BVar(0), body));
    }

    /// <summary><c>fun σ s => Except.ok v</c> or <c>fun σ s => Except.error e</c>, from the CLR's result or exception.</summary>
    private static Expr Outcome(Expr result, Func<Expr> clr)
    {
        Expr value;
        string ctor;
        try
        {
            value = clr();
            ctor = "Except.ok";
        }
        catch (Exception e) when (IsModelled(e))
        {
            value = ClrExn(e);
            ctor = "Except.error";
        }
        var body = Expr.App(Expr.Const(Name.Parse(ctor), Level.Zero, Level.Zero), ClrExnT, result, value);
        return Expr.Lam(Name.From("σ"), TypeT, Expr.Lam(Name.From("s"), Expr.BVar(0), body));
    }

    private static Expr Model(string type, string op, Expr sigma, params Expr[] args) =>
        Expr.App(Expr.Const(Name.Parse($"Warrant.{type}.{op}")), [sigma, .. args]);

    /// <summary>The model's outcome from every world is the CLR's: its value, or the <c>ClrExn</c> of its exception.</summary>
    private bool RaisingAgrees(VirPrimitive result, Func<Expr, Expr> program, Func<Expr> clr) =>
        RaisingAgrees(Literals.Type(result), program, clr);

    /// <summary>As above, at any result type.</summary>
    private bool RaisingAgrees(Expr resultT, Func<Expr, Expr> program, Func<Expr> clr)
    {
        var type = Expr.Forall(Name.From("σ"), TypeT, Expr.Forall(Name.From("s"), Expr.BVar(0),
            Expr.App(Expr.Const(Name.Parse("Except"), Level.Zero, Level.Zero), ClrExnT, resultT)));
        return Agrees(RunFromAnyWorld(resultT, program), Outcome(resultT, clr), type);
    }

    [Theory]
    [MemberData(nameof(RaisingNames))]
    public void Int32RaisingOperationsAgree(string name)
    {
        var row = RaisingRows.Single(r => r.Name == name);
        bool Ok((int A, int B) p) => RaisingAgrees(VirPrimitive.Int32,
            s => Model("Int32", row.Model, s, Literals.Int32(p.A), Literals.Int32(p.B)), () => Literals.Int32(row.Int32(p.A, p.B)));
        KernelThread.Run(() =>
        {
            Assert.All(Generators.Int32BoundaryPairs(), p => Assert.True(Ok(p), $"{p.Item1} {name} {p.Item2}"));
            Pbt.Check(Prop.ForAll(Generators.Int32Pairs, Ok), Cases);
        });
    }

    [Theory]
    [MemberData(nameof(RaisingNames))]
    public void Int64RaisingOperationsAgree(string name)
    {
        var row = RaisingRows.Single(r => r.Name == name);
        bool Ok((long A, long B) p) => RaisingAgrees(VirPrimitive.Int64,
            s => Model("Int64", row.Model, s, Literals.Int64(p.A), Literals.Int64(p.B)), () => Literals.Int64(row.Int64(p.A, p.B)));
        KernelThread.Run(() =>
        {
            Assert.All(Generators.Int64BoundaryPairs(), p => Assert.True(Ok(p), $"{p.Item1} {name} {p.Item2}"));
            Pbt.Check(Prop.ForAll(Generators.Int64Pairs, Ok), Cases);
        });
    }

    [Fact]
    public void CheckedNegationAgrees()
    {
        bool Ok32(int x) => RaisingAgrees(VirPrimitive.Int32,
            s => Model("Int32", "negChecked", s, Literals.Int32(x)), () => Literals.Int32(checked(-x)));
        bool Ok64(long x) => RaisingAgrees(VirPrimitive.Int64,
            s => Model("Int64", "negChecked", s, Literals.Int64(x)), () => Literals.Int64(checked(-x)));
        KernelThread.Run(() =>
        {
            Assert.All(Generators.Int32Boundaries, x => Assert.True(Ok32(x), $"checked(-({x}))"));
            Assert.All(Generators.Int64Boundaries, x => Assert.True(Ok64(x), $"checked(-({x}L))"));
            Pbt.Check(Prop.ForAll(Generators.Int32s, Ok32), Cases);
            Pbt.Check(Prop.ForAll(Generators.Int64s, Ok64), Cases);
        });
    }

    [Fact]
    public void CheckedNarrowingAgrees()
    {
        bool Ok(long x) => RaisingAgrees(VirPrimitive.Int32,
            s => Model("Int64", "toInt32Checked", s, Literals.Int64(x)), () => Literals.Int32(checked((int)x)));
        KernelThread.Run(() =>
        {
            var boundaries = Generators.Int64Boundaries
                .Concat(Generators.Int32Boundaries.Select(x => (long)x))
                .Concat([(long)int.MaxValue + 1, (long)int.MinValue - 1]);
            Assert.All(boundaries, x => Assert.True(Ok(x), $"checked((int){x}L)"));
            Pbt.Check(Prop.ForAll(Generators.Int64s, Ok), Cases);
        });
    }

    /// <summary>The named cases of KTD6 and R5, each pinned on the CLR first so the expected outcome is not assumed.</summary>
    [Fact]
    public void NamedRaisingCasesAgree()
    {
        int seven = Runtime(-7), two = Runtime(2), min = Runtime(int.MinValue), minusOne = Runtime(-1), zero = Runtime(0), max = Runtime(int.MaxValue);
        Assert.Equal(-3, seven / two);
        Assert.Equal(-1, seven % two);
        Assert.Throws<OverflowException>(() => checked(max + 1));
        KernelThread.Run(() =>
        {
            bool Div(int a, int b) => RaisingAgrees(VirPrimitive.Int32, s => Model("Int32", "div", s, Literals.Int32(a), Literals.Int32(b)), () => Literals.Int32(a / b));
            bool Rem(int a, int b) => RaisingAgrees(VirPrimitive.Int32, s => Model("Int32", "rem", s, Literals.Int32(a), Literals.Int32(b)), () => Literals.Int32(a % b));
            Assert.True(Div(seven, two), "-7 / 2 == -3");
            Assert.True(Rem(seven, two), "-7 % 2 == -1");
            Assert.True(Div(7, zero), "7 / 0 raises divideByZero");
            Assert.True(Rem(7, zero), "7 % 0 raises divideByZero");
            Assert.True(Div(min, minusOne), "int.MinValue / -1 raises overflow");
            Assert.True(Rem(min, minusOne), "int.MinValue % -1 raises overflow");
            Assert.True(RaisingAgrees(VirPrimitive.Int32, s => Model("Int32", "addChecked", s, Literals.Int32(max), Literals.Int32(1)),
                () => Literals.Int32(checked(max + 1))), "checked(int.MaxValue + 1) raises overflow");
        });
    }

    [Fact]
    public void TheRaisingOracleRejectsAWrongOutcome() => KernelThread.Run(() =>
    {
        var wrongException = new OverflowException();
        var divideByZero = RunFromAnyWorld(Literals.Type(VirPrimitive.Int32), s => Model("Int32", "div", s, Literals.Int32(7), Literals.Int32(0)));
        var tc = new TypeChecker(env);
        Assert.False(tc.IsDefEq(divideByZero, Outcome(Literals.Type(VirPrimitive.Int32), () => throw wrongException)), "7 / 0 is not overflow");
        Assert.False(tc.IsDefEq(divideByZero, Outcome(Literals.Type(VirPrimitive.Int32), () => Literals.Int32(0))), "7 / 0 is not Lean's 0");
        var minDiv = RunFromAnyWorld(Literals.Type(VirPrimitive.Int32), s => Model("Int32", "div", s, Literals.Int32(int.MinValue), Literals.Int32(-1)));
        Assert.False(tc.IsDefEq(minDiv, Outcome(Literals.Type(VirPrimitive.Int32), () => Literals.Int32(int.MinValue))), "int.MinValue / -1 does not wrap");
    });

    // ------------------------------------------------------------------ nullable values (M6 U16, KTD5)

    /// <summary><c>Option.some v</c> or <c>Option.none</c> at <paramref name="type"/>: a nullable value (KTD5).</summary>
    private static Expr Optional(Expr type, Expr? value) => value is null
        ? Expr.App(Expr.Const(Name.Parse("Option.none"), Level.Zero), type)
        : Expr.App(Expr.Const(Name.Parse("Option.some"), Level.Zero), type, value);

    private static Expr OptionalInt32(int? x) => Optional(Literals.Type(VirPrimitive.Int32), x is { } v ? Literals.Int32(v) : null);

    private static Expr OptionalInt64(long? x) => Optional(Literals.Type(VirPrimitive.Int64), x is { } v ? Literals.Int64(v) : null);

    /// <summary>A model of <c>lean/Warrant/Nullable.lean</c> at world <paramref name="sigma"/> and value type <paramref name="type"/>.</summary>
    private static Expr NullableModel(string op, Expr sigma, Expr type, Expr x) =>
        Expr.App(Expr.Const(Name.Parse($"Warrant.Nullable.{op}")), sigma, type, x);

    private static Expr Coalesce(Expr type, Expr x, Expr d) =>
        Expr.App(Expr.Const(Name.Parse("Warrant.Nullable.coalesce")), type, x, d);

    /// <summary>A reference type whose null dereference the CLR side performs.</summary>
    private sealed record Box(long V);

    /// <summary><c>null</c> one time in five, otherwise a boundary-biased value.</summary>
    private static Arbitrary<int?> NullableInt32s { get; } =
        Arb.From(Gen.Frequency<int?>((1, Gen.Constant<int?>(null)), (4, Generators.Int32Values.Select(v => (int?)v))));

    private static Arbitrary<long?> NullableInt64s { get; } =
        Arb.From(Gen.Frequency<long?>((1, Gen.Constant<long?>(null)), (4, Generators.Int64Values.Select(v => (long?)v))));

    private static IEnumerable<int?> NullableInt32Boundaries => Generators.Int32Boundaries.Select(v => (int?)v).Prepend(null);

    private static IEnumerable<long?> NullableInt64Boundaries => Generators.Int64Boundaries.Select(v => (long?)v).Prepend(null);

    [Fact]
    public void NullableValueAgrees()
    {
        var int32 = Literals.Type(VirPrimitive.Int32);
        var int64 = Literals.Type(VirPrimitive.Int64);
        bool Ok32(int? x) =>
            RaisingAgrees(int32, s => NullableModel("value", s, int32, OptionalInt32(x)), () => Literals.Int32(Runtime(x)!.Value)) &&
            RaisingAgrees(int32, s => NullableModel("value", s, int32, OptionalInt32(x)), () => Literals.Int32((int)Runtime(x)!));
        bool Ok64(long? x) =>
            RaisingAgrees(int64, s => NullableModel("value", s, int64, OptionalInt64(x)), () => Literals.Int64(Runtime(x)!.Value)) &&
            RaisingAgrees(int64, s => NullableModel("value", s, int64, OptionalInt64(x)), () => Literals.Int64((long)Runtime(x)!));
        KernelThread.Run(() =>
        {
            Assert.All(NullableInt32Boundaries, x => Assert.True(Ok32(x), $"({(object?)x ?? "null"}).Value"));
            Assert.All(NullableInt64Boundaries, x => Assert.True(Ok64(x), $"({(object?)x ?? "null"}L).Value"));
            Pbt.Check(Prop.ForAll(NullableInt32s, Ok32), Cases);
            Pbt.Check(Prop.ForAll(NullableInt64s, Ok64), Cases);
        });
    }

    /// <summary>The non-null unwrap (KTD5): a null reference used where a non-null one is required, here as a receiver.</summary>
    [Fact]
    public void NonNullUnwrapAgrees()
    {
        var int64 = Literals.Type(VirPrimitive.Int64);
        bool Ok(long? x)
        {
            var box = Runtime(x is { } v ? new Box(v) : null);
            return RaisingAgrees(int64, s => NullableModel("nonNull", s, int64, OptionalInt64(x)), () => Literals.Int64(box!.V));
        }
        KernelThread.Run(() =>
        {
            Assert.All(NullableInt64Boundaries, x => Assert.True(Ok(x), $"box({(object?)x ?? "null"}).V"));
            Pbt.Check(Prop.ForAll(NullableInt64s, Ok), Cases);
        });
    }

    [Fact]
    public void CoalesceAndGetValueOrDefaultAgree()
    {
        var int32 = Literals.Type(VirPrimitive.Int32);
        var int64 = Literals.Type(VirPrimitive.Int64);
        bool Ok32((int? X, int D) p) =>
            AgreesInt32(Coalesce(int32, OptionalInt32(p.X), Literals.Int32(p.D)), Runtime(p.X) ?? p.D) &&
            AgreesInt32(Coalesce(int32, OptionalInt32(p.X), Literals.Int32(p.D)), Runtime(p.X).GetValueOrDefault(p.D)) &&
            AgreesInt32(Coalesce(int32, OptionalInt32(p.X), Literals.Int32(0)), Runtime(p.X).GetValueOrDefault());
        bool Ok64((long? X, long D) p) =>
            AgreesInt64(Coalesce(int64, OptionalInt64(p.X), Literals.Int64(p.D)), Runtime(p.X) ?? p.D) &&
            AgreesInt64(Coalesce(int64, OptionalInt64(p.X), Literals.Int64(p.D)), Runtime(p.X).GetValueOrDefault(p.D)) &&
            AgreesInt64(Coalesce(int64, OptionalInt64(p.X), Literals.Int64(0)), Runtime(p.X).GetValueOrDefault());
        KernelThread.Run(() =>
        {
            Assert.All(from x in NullableInt32Boundaries from d in Generators.Int32Boundaries select (x, d),
                p => Assert.True(Ok32(p), $"{(object?)p.x ?? "null"} ?? {p.d}"));
            Assert.All(from x in NullableInt64Boundaries from d in Generators.Int64Boundaries select (x, d),
                p => Assert.True(Ok64(p), $"{(object?)p.x ?? "null"}L ?? {p.d}L"));
            Pbt.Check(Prop.ForAll(Arb.From(NullableInt32s.Generator.SelectMany(x => Generators.Int32Values.Select(d => (x, d)))), Ok32), Cases);
            Pbt.Check(Prop.ForAll(Arb.From(NullableInt64s.Generator.SelectMany(x => Generators.Int64Values.Select(d => (x, d)))), Ok64), Cases);
        });
    }

    [Fact]
    public void ANullValueRaisesInvalidOperationAndANullReceiverNullReference() => KernelThread.Run(() =>
    {
        int? none = Runtime<int?>(null);
        Assert.Throws<InvalidOperationException>(() => none!.Value);
        Assert.Throws<InvalidOperationException>(() => (int)none!);
        Assert.Throws<NullReferenceException>(() => Runtime<Box?>(null)!.V);

        var int32 = Literals.Type(VirPrimitive.Int32);
        var value = RunFromAnyWorld(int32, s => NullableModel("value", s, int32, OptionalInt32(null)));
        var nonNull = RunFromAnyWorld(int32, s => NullableModel("nonNull", s, int32, OptionalInt32(null)));
        var tc = new TypeChecker(env);
        Assert.True(tc.IsDefEq(value, Outcome(int32, () => Literals.Int32(Runtime<int?>(null)!.Value))), "null.Value raises invalidOperation");
        Assert.False(tc.IsDefEq(value, Outcome(int32, () => Literals.Int32((int)Runtime<Box?>(null)!.V))), "null.Value is not nullReference");
        Assert.True(tc.IsDefEq(nonNull, Outcome(int32, () => Literals.Int32((int)Runtime<Box?>(null)!.V))), "a null receiver raises nullReference");
        Assert.False(tc.IsDefEq(nonNull, Outcome(int32, () => Literals.Int32(Runtime<int?>(null)!.Value))), "a null receiver is not invalidOperation");
    });

    // ------------------------------------------------------------------ Math on int and long (M6 U16, KTD23)

    [Fact]
    public void MathMinAndMaxAgree()
    {
        Expr Call(string type, string op, Expr a, Expr b) => Expr.App(Expr.Const(Name.Parse($"Warrant.{type}.{op}")), a, b);
        bool Ok32((int A, int B) p) =>
            AgreesInt32(Call("Int32", "min", Literals.Int32(p.A), Literals.Int32(p.B)), Math.Min(p.A, p.B)) &&
            AgreesInt32(Call("Int32", "max", Literals.Int32(p.A), Literals.Int32(p.B)), Math.Max(p.A, p.B));
        bool Ok64((long A, long B) p) =>
            AgreesInt64(Call("Int64", "min", Literals.Int64(p.A), Literals.Int64(p.B)), Math.Min(p.A, p.B)) &&
            AgreesInt64(Call("Int64", "max", Literals.Int64(p.A), Literals.Int64(p.B)), Math.Max(p.A, p.B));
        KernelThread.Run(() =>
        {
            Assert.All(Generators.Int32BoundaryPairs(), p => Assert.True(Ok32(p), $"Math.Min/Max({p.Item1}, {p.Item2})"));
            Assert.All(Generators.Int64BoundaryPairs(), p => Assert.True(Ok64(p), $"Math.Min/Max({p.Item1}L, {p.Item2}L)"));
            Pbt.Check(Prop.ForAll(Generators.Int32Pairs, Ok32), Cases);
            Pbt.Check(Prop.ForAll(Generators.Int64Pairs, Ok64), Cases);
        });
    }

    [Fact]
    public void MathAbsAgrees()
    {
        bool Ok32(int x) => RaisingAgrees(VirPrimitive.Int32,
            s => Model("Int32", "abs", s, Literals.Int32(x)), () => Literals.Int32(Math.Abs(Runtime(x))));
        bool Ok64(long x) => RaisingAgrees(VirPrimitive.Int64,
            s => Model("Int64", "abs", s, Literals.Int64(x)), () => Literals.Int64(Math.Abs(Runtime(x))));
        Assert.Throws<OverflowException>(() => unchecked(Math.Abs(Runtime(int.MinValue))));
        Assert.Throws<OverflowException>(() => unchecked(Math.Abs(Runtime(long.MinValue))));
        KernelThread.Run(() =>
        {
            Assert.True(Ok32(int.MinValue), "Math.Abs(int.MinValue) raises overflow");
            Assert.True(Ok64(long.MinValue), "Math.Abs(long.MinValue) raises overflow");
            Assert.All(Generators.Int32Boundaries, x => Assert.True(Ok32(x), $"Math.Abs({x})"));
            Assert.All(Generators.Int64Boundaries, x => Assert.True(Ok64(x), $"Math.Abs({x}L)"));
            Pbt.Check(Prop.ForAll(Generators.Int32s, Ok32), Cases);
            Pbt.Check(Prop.ForAll(Generators.Int64s, Ok64), Cases);
        });
    }

    // ------------------------------------------------------------------ decimal (M6 U4, KTD7)

    // Every expected value below is the CLR's own decimal arithmetic on the same operands (#117), compared with the model
    // by representation: sign, mantissa and scale, so 1.0m and 1.00m, and 0m and negative zero, are different results.

    private static readonly Expr DecimalT = Expr.Const(Name.Parse("Warrant.Decimal"));

    private static Expr Dec(decimal value) => Literals.Decimal(DecimalLitExpr.Of(value));

    private static Expr DecimalOp(string op, params Expr[] args) => Expr.App(Expr.Const(Name.Parse($"Warrant.Decimal.{op}")), args);

    /// <summary>A decimal for a failure message: its value, scale and sign bit.</summary>
    private static string Show(decimal d) => $"{d}m (scale {d.Scale}{(decimal.IsNegative(d) ? ", negative" : "")})";

    private bool AgreesDecimal(Expr term, decimal clr) => Agrees(term, Dec(clr), DecimalT);

    /// <summary><c>a + b</c> or <c>a - b</c> on the model, run from any world, against the CLR's result or exception.</summary>
    private bool SumAgrees(string op, decimal a, decimal b) =>
        RaisingAgrees(DecimalT, s => DecimalOp(op, s, Dec(a), Dec(b)), () => Dec(op == "add" ? Runtime(a) + b : Runtime(a) - b));

    /// <summary>A projection of a literal, reduced by the kernel.</summary>
    private Expr Field(string field, Expr literal)
    {
        var tc = new TypeChecker(env);
        return tc.Whnf(DecimalOp(field, literal));
    }

    [Fact]
    public void DecimalLiteralsRoundTripAtEveryScale() => KernelThread.Run(() =>
    {
        var tc = new TypeChecker(env);
        var limit = DecimalLitExpr.MantissaLimit;
        var random = new Random(7);
        for (int scale = 0; scale <= DecimalLitExpr.MaxScale; scale++)
        {
            var random96 = new BigInteger(random.NextInt64()) * new BigInteger(random.NextInt64()) % limit;
            foreach (var mantissa in new[] { BigInteger.Zero, BigInteger.One, new BigInteger(12345), BigInteger.Abs(random96), limit - 1 })
            {
                foreach (var negative in new[] { false, true })
                {
                    var literal = new DecimalLitExpr(negative, mantissa, scale);
                    var value = literal.ToDecimal();
                    Assert.Equal(literal, DecimalLitExpr.Of(value));
                    var term = Literals.Decimal(literal);
                    Assert.True(tc.IsDefEq(tc.Check(term), DecimalT), $"{literal} is a Warrant.Decimal");
                    Assert.Equal(Literals.Bool(negative), Field("negative", term));
                    Assert.Equal(Expr.NatLit(mantissa), Field("mantissa", term));
                    Assert.Equal(Expr.NatLit(scale), Field("scale", term));
                }
            }
        }
    });

    [Fact]
    public void ADecimalLiteralOutOfRangeIsRejected() => KernelThread.Run(() =>
    {
        Assert.Throws<TranslationException>(() => Literals.Decimal(new DecimalLitExpr(false, DecimalLitExpr.MantissaLimit, 0)));
        Assert.Throws<TranslationException>(() => Literals.Decimal(new DecimalLitExpr(false, BigInteger.One, 29)));

        // The kernel checks the bounds itself: the same term with an out-of-range mantissa or scale does not type-check.
        var refl = Expr.App(Expr.Const(Name.Parse("Eq.refl"), Level.One), Literals.Type(VirPrimitive.Bool), Literals.Bool(true));
        foreach (var (mantissa, scale) in new[] { (DecimalLitExpr.MantissaLimit, 0), (BigInteger.One, 29) })
        {
            var term = DecimalOp("lit", Literals.Bool(false), Expr.NatLit(mantissa), Expr.NatLit(scale), refl, refl);
            Assert.ThrowsAny<KernelException>(() => new TypeChecker(env).Check(term));
        }
    });

    [Fact]
    public void DecimalAdditionAndSubtractionAgree() => KernelThread.Run(() =>
    {
        foreach (var op in new[] { "add", "sub" })
        {
            Assert.All(Generators.DecimalBoundaryPairs(), p => Assert.True(SumAgrees(op, p.Item1, p.Item2), $"{Show(p.Item1)} {op} {Show(p.Item2)}"));
            Pbt.Check(Prop.ForAll(Generators.DecimalPairs, p => SumAgrees(op, p.Item1, p.Item2)), Cases);
        }
    });

    /// <summary>The named cases of KTD7 and U4, each pinned on the CLR first so the expected outcome is not assumed.</summary>
    [Fact]
    public void NamedDecimalCasesAgree()
    {
        decimal max = Runtime(decimal.MaxValue);
        Assert.Throws<OverflowException>(() => max + 1m);
        Assert.Throws<OverflowException>(() => max + 0.5m);
        Assert.Equal((decimal.MaxValue, 0), Bits(max + 0.4m));
        Assert.Equal((decimal.MaxValue, 0), Bits(max - 0.4m));
        Assert.Equal((79228162514264337593543950334m, 0), Bits(max - 0.5m));
        Assert.Equal((9m, 27), Bits(Runtime(9m) + 0.0000000000000000000000000001m));
        Assert.Equal((79228162514264337593543950331m, 0), Bits(Runtime(79228162514264337593543950331m) + 0.46m));
        Assert.Equal((79228162514264337593543950330m, 0), Bits(Runtime(79228162514264337593543950330m) + 0.5m));
        Assert.Equal((79228162514264337593543950332m, 0), Bits(Runtime(79228162514264337593543950331m) + 0.5m));
        Assert.Equal((0.3m, 1), Bits(Runtime(0.1m) + 0.2m));
        Assert.True(Runtime(0.1m) + 0.2m == 0.3m);
        KernelThread.Run(() =>
        {
            Assert.True(SumAgrees("add", decimal.MaxValue, 1m), "decimal.MaxValue + 1m raises overflow");
            Assert.True(SumAgrees("add", 9m, 0.0000000000000000000000000001m), "9m + 1e-28m rounds to 9 at scale 27");
            Assert.True(SumAgrees("sub", decimal.MaxValue, 0.5m), "decimal.MaxValue - 0.5m rounds to ...334");
            Assert.True(SumAgrees("add", decimal.MaxValue, 0.4m), "decimal.MaxValue + 0.4m is decimal.MaxValue");
            Assert.True(SumAgrees("add", decimal.MaxValue, 0.5m), "decimal.MaxValue + 0.5m raises overflow");
            Assert.True(SumAgrees("sub", decimal.MaxValue, 0.4m), "decimal.MaxValue - 0.4m is decimal.MaxValue, so a - b < a needs exactness");
            Assert.True(SumAgrees("add", 79228162514264337593543950331m, 0.46m), "...331m + 0.46m rounds once, to ...331");
            Assert.True(SumAgrees("add", 79228162514264337593543950330m, 0.5m), "...330m + 0.5m ties to even, ...330");
            Assert.True(SumAgrees("add", 79228162514264337593543950331m, 0.5m), "...331m + 0.5m ties to even, ...332");
            Assert.True(SumAgrees("add", 0.1m, 0.2m), "0.1m + 0.2m is 0.3m at scale 1");
            // The model's sum is the CLR's 0.3m (above), which equals 0.3m and 0.30m by value.
            Assert.True(Decide("eq", Dec(Runtime(0.1m) + 0.2m), Dec(0.3m), true), "0.1m + 0.2m == 0.3m");
            Assert.True(Decide("eq", Dec(Runtime(0.1m) + 0.2m), Dec(0.30m), true), "0.1m + 0.2m == 0.30m");
        });
    }

    private static (decimal Value, int Scale) Bits(decimal d) => (d, d.Scale);

    [Fact]
    public void DecimalNegationAgrees()
    {
        bool Ok(decimal x) => AgreesDecimal(DecimalOp("neg", Dec(x)), -Runtime(x));
        Assert.True(decimal.IsNegative(-Runtime(0m)), "-0m is negative zero on the CLR");
        KernelThread.Run(() =>
        {
            Assert.All(Generators.DecimalBoundaries, x => Assert.True(Ok(x), $"-{Show(x)}"));
            Pbt.Check(Prop.ForAll(Generators.Decimals, Ok), Cases);
        });
    }

    /// <summary><c>decide</c> of a decimal comparison: <c>eq</c>, <c>&lt;</c> or <c>&lt;=</c>, against the CLR's answer.</summary>
    private bool Decide(string relation, Expr a, Expr b, bool clr)
    {
        var (prop, inst) = relation switch
        {
            "eq" => (DecimalOp("eq", a, b), DecimalOp("decEq", a, b)),
            "lt" => (Expr.App(Expr.Const(Name.Parse("LT.lt"), Level.Zero), DecimalT, Expr.Const(Name.Parse("Warrant.Decimal.instLT")), a, b), DecimalOp("decLt", a, b)),
            "le" => (Expr.App(Expr.Const(Name.Parse("LE.le"), Level.Zero), DecimalT, Expr.Const(Name.Parse("Warrant.Decimal.instLE")), a, b), DecimalOp("decLe", a, b)),
            _ => throw new ArgumentOutOfRangeException(nameof(relation)),
        };
        return AgreesBool(Expr.App(Expr.Const(Name.Parse("Decidable.decide")), prop, inst), clr);
    }

    [Fact]
    public void DecimalComparisonsAgree()
    {
        bool Ok((decimal A, decimal B) p)
        {
            Expr a = Dec(p.A), b = Dec(p.B);
            return Decide("eq", a, b, p.A == p.B) && Decide("eq", a, b, !(p.A != p.B))
                && Decide("lt", a, b, p.A < p.B) && Decide("le", a, b, p.A <= p.B)
                && Decide("lt", b, a, p.A > p.B) && Decide("le", b, a, p.A >= p.B);
        }
        KernelThread.Run(() =>
        {
            Assert.All(Generators.DecimalBoundaryPairs(), p => Assert.True(Ok(p), $"{Show(p.Item1)} vs {Show(p.Item2)}"));
            Pbt.Check(Prop.ForAll(Generators.DecimalPairs, Ok), Cases);
        });
    }

    private sealed record Priced(decimal Amount);

    [Fact]
    public void EqualValuesAtDifferentScalesAreEqual()
    {
        Assert.True(Runtime(1.0m) == 1.00m);
        Assert.Equal(new Priced(Runtime(1.0m)), new Priced(1.00m));
        Assert.True(Runtime(0m) == -Runtime(0m));
        KernelThread.Run(() =>
        {
            Assert.True(Decide("eq", Dec(1.0m), Dec(1.00m), true), "1.0m == 1.00m");
            Assert.True(Decide("eq", Dec(0m), Dec(-Runtime(0m)), true), "0m == -0m");
            Assert.True(Decide("lt", Dec(1.0m), Dec(1.00m), false), "!(1.0m < 1.00m)");
            var tc = new TypeChecker(env);
            Assert.False(tc.IsDefEq(Dec(1.0m), Dec(1.00m)), "1.0m and 1.00m are different representations");
        });
    }

    [Fact]
    public void MathOnDecimalAgrees()
    {
        bool Ok((decimal A, decimal B) p) =>
            AgreesDecimal(DecimalOp("min", Dec(p.A), Dec(p.B)), Math.Min(Runtime(p.A), p.B)) &&
            AgreesDecimal(DecimalOp("max", Dec(p.A), Dec(p.B)), Math.Max(Runtime(p.A), p.B)) &&
            AgreesDecimal(DecimalOp("abs", Dec(p.A)), Math.Abs(Runtime(p.A)));
        Assert.Equal((1.00m, 2), Bits(Math.Min(Runtime(1.0m), 1.00m)));
        Assert.Equal((1.0m, 1), Bits(Math.Max(Runtime(1.0m), 1.00m)));
        KernelThread.Run(() =>
        {
            Assert.True(AgreesDecimal(DecimalOp("min", Dec(1.0m), Dec(1.00m)), 1.00m), "Math.Min(1.0m, 1.00m) is 1.00m");
            Assert.True(AgreesDecimal(DecimalOp("max", Dec(1.0m), Dec(1.00m)), 1.0m), "Math.Max(1.0m, 1.00m) is 1.0m");
            Assert.False(AgreesDecimal(DecimalOp("min", Dec(1.0m), Dec(1.00m)), 1.0m), "Math.Min(1.0m, 1.00m) is not 1.0m");
            Assert.All(Generators.DecimalBoundaryPairs(), p => Assert.True(Ok(p), $"Math.Min/Max/Abs({Show(p.Item1)}, {Show(p.Item2)})"));
            Pbt.Check(Prop.ForAll(Generators.DecimalPairs, Ok), Cases);
        });
    }

    [Fact]
    public void TheDecimalOracleComparesRepresentations() => KernelThread.Run(() =>
    {
        var tc = new TypeChecker(env);
        var sum = RunFromAnyWorld(DecimalT, s => DecimalOp("add", s, Dec(0.1m), Dec(0.2m)));
        Assert.True(tc.IsDefEq(sum, Outcome(DecimalT, () => Dec(0.3m))), "0.1m + 0.2m is 0.3m");
        Assert.False(tc.IsDefEq(sum, Outcome(DecimalT, () => Dec(0.30m))), "0.1m + 0.2m is not 0.30m");
        var zero = RunFromAnyWorld(DecimalT, s => DecimalOp("add", s, Dec(-1.0m), Dec(1.00m)));
        Assert.True(tc.IsDefEq(zero, Outcome(DecimalT, () => Dec(Runtime(-1.0m) + 1.00m))), "-1.0m + 1.00m");
        Assert.False(tc.IsDefEq(zero, Outcome(DecimalT, () => Dec(0.00m))), "-1.0m + 1.00m is negative zero, not 0.00m");
    });

    // ------------------------------------------------------------------ CLR-side pins (no model half in M4)

    /// <summary>Hides a value from constant folding by the C# compiler and the JIT.</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static T Runtime<T>(T value) => value;

    [Fact]
    public void MinValueDividedByMinusOneThrows()
    {
        int min = Runtime(int.MinValue), minusOne = Runtime(-1);
        Assert.Throws<OverflowException>(() => unchecked(min / minusOne));
        Assert.Throws<OverflowException>(() => unchecked(min % minusOne));
    }

    [Fact]
    public void DivisionByZeroThrows()
    {
        int x = Runtime(7), zero = Runtime(0);
        long lx = Runtime(7L), lzero = Runtime(0L);
        Assert.Throws<DivideByZeroException>(() => x / zero);
        Assert.Throws<DivideByZeroException>(() => x % zero);
        Assert.Throws<DivideByZeroException>(() => lx / lzero);
        Assert.Throws<DivideByZeroException>(() => lx % lzero);
    }

    [Fact]
    public void ShiftsMaskTheCountAndShiftLogically()
    {
        int one = Runtime(1), minusEight = Runtime(-8), count33 = Runtime(33), count1 = Runtime(1);
        Assert.Equal(2, one << count33);
        Assert.Equal(-4, minusEight >> count33);
        Assert.Equal(2147483644, minusEight >>> count1);
    }
}
