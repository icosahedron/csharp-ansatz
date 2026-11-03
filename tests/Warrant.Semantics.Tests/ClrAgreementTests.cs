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
/// of boundary and random operands, is definitionally equal in the kernel to the literal of the result C# computes
/// (unchecked). The literal encoder is checked on its own against the CLR's bit patterns, because both sides of every
/// other comparison go through it. The operations M4 rejects have their CLR behaviour pinned on the CLR side only.
/// </summary>
public sealed class ClrAgreementTests(SemanticsBundleFixture bundle) : IClassFixture<SemanticsBundleFixture>
{
    private static readonly Config Runs = Config.QuickThrowOnFailure.WithMaxTest(150);

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
            Prop.ForAll(Generators.Int32Pairs, Ok).Check(Runs);
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
            Prop.ForAll(Generators.Int64Pairs, Ok).Check(Runs);
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
            Prop.ForAll(Generators.Int32s, Ok32).Check(Runs);
            Prop.ForAll(Generators.Int64s, Ok64).Check(Runs);
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
            Prop.ForAll(Generators.Int32Pairs, Ok).Check(Runs);
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
            Prop.ForAll(Generators.Int64Pairs, Ok).Check(Runs);
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
            Prop.ForAll(Generators.Int32s, Widen).Check(Runs);
            Prop.ForAll(Generators.Int64s, Narrow).Check(Runs);
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
        Prop.ForAll(Generators.Int32s, Int32BitsAgree).Check(Runs);
        Prop.ForAll(Generators.Int64s, Int64BitsAgree).Check(Runs);
    });

    [Fact]
    public void TheBitPatternOracleRejectsAWrongPattern() => KernelThread.Run(() =>
    {
        Assert.False(BitPatternAgrees(Int32ToBitVec, 32, Literals.Int32(-1), uint.MaxValue - 1));
        Assert.False(BitPatternAgrees(Int32ToBitVec, 32, Literals.Int32(int.MinValue), 1u << 30));
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
