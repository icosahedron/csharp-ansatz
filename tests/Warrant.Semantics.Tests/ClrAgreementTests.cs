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
        _ => throw new InvalidOperationException($"no ClrExn models {e.GetType()}"),
    }));

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
        catch (Exception e) when (e is OverflowException or DivideByZeroException)
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
    private bool RaisingAgrees(VirPrimitive result, Func<Expr, Expr> program, Func<Expr> clr)
    {
        var resultT = Literals.Type(result);
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
