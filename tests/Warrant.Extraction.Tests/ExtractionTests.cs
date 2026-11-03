using Microsoft.CodeAnalysis.CSharp;
using Warrant.Extraction;
using Warrant.Vir;
using static Warrant.Extraction.Tests.Inline;

namespace Warrant.Extraction.Tests;

/// <summary>Extraction rules exercised on small sources (plan U6, test scenarios).</summary>
public class ExtractionTests
{
    [Fact]
    public void CompileErrorsGiveNoUnitsAndReportTheErrors()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int Ok(int x) => x;
                [Verified] public static int Broken(int x) => y;
            }
            """);
        Assert.True(result.HasCompileErrors);
        Assert.Empty(result.Units);
        var error = Assert.Single(result.Diagnostics);
        Assert.Equal("CS0103", error.Id);
        Assert.Equal(ExtractionSeverity.Error, error.Severity);
        Assert.Null(error.Construct);
        Assert.Equal(new VirSpan("Test.cs", 5, 51, 5, 52), error.Location);
    }

    [Fact]
    public void MutualRecursionIsRejectedAndSoAreItsCallers()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int A(int n) => n <= 0 ? 0 : B(n - 1);
                [Verified] public static int B(int n) => n <= 0 ? 1 : A(n - 1);
                [Verified] public static int Caller(int n) => A(n);
                [Verified] public static int Unrelated(int n) => n;
            }
            """);
        Assert.Equal("WRT0002 | recursion", Only(result, "M:C.A(System.Int32)"));
        Assert.Equal("WRT0002 | recursion", Only(result, "M:C.B(System.Int32)"));
        Assert.Equal("WRT0002 | depends on a rejected unit", Only(result, "M:C.Caller(System.Int32)"));
        Assert.Empty(result.DiagnosticsFor("M:C.Unrelated(System.Int32)"));
        Assert.Equal(["M:C.Unrelated(System.Int32)"], result.Units.Select(u => u.Key));
    }

    [Fact]
    public void ASwitchSectionMixingDefaultWithCaseLabelsIsRejected()
    {
        var result = Extract("""
            public static class C
            {
                [Verified]
                public static int Mixed(int n)
                {
                    switch (n)
                    {
                        case 1:
                        default:
                            return 0;
                        case 2:
                            return 5;
                    }
                }

                [Verified]
                public static int Separate(int n)
                {
                    switch (n)
                    {
                        case 2:
                            return 5;
                        default:
                            return 0;
                    }
                }
            }
            """);
        Assert.Equal("WRT0002 | switch section mixing default with case labels", Only(result, "M:C.Mixed(System.Int32)"));
        Assert.Empty(result.DiagnosticsFor("M:C.Separate(System.Int32)"));
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void OverflowCheckingRejectsAdditionButNotWidening(bool checkOverflow)
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int Add(int a, int b) => a + b;
                [Verified] public static long Widen(int a) => (long)a;
            }
            """, checkOverflow);
        if (checkOverflow)
        {
            Assert.Equal("WRT0002 | checked arithmetic", Only(result, "M:C.Add(System.Int32,System.Int32)"));
        }
        else
        {
            Assert.Empty(result.DiagnosticsFor("M:C.Add(System.Int32,System.Int32)"));
        }
        var widen = Unit(result, "M:C.Widen(System.Int32)");
        Assert.Equal(new ConvertExpr(VirType.Int32, VirType.Int64, VirOverflow.Wrap, new ParamExpr(VirType.Int32, 0)), widen.Body);
        Assert.Equal(checkOverflow ? VirOverflow.Checked : VirOverflow.Wrap, widen.Facts.Overflow);
    }

    [Fact]
    public void FoldedConstantIsTheLiteralTheCompilerProduced()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int F() => unchecked(int.MinValue / -1);
            }
            """);
        Assert.Equal(LitExpr.Int32(int.MinValue), Unit(result, "M:C.F").Body);
    }

    [Theory]
    [InlineData("public class K { public static K A { get; } = new(); private K() { } }", "not sealed")]
    [InlineData("public sealed class K { public static K A { get; } = new(); internal K() { } }", "constructor that is not private")]
    [InlineData("public sealed class K(int x) { public static K A { get; } = new(1); }", "constructor that is not private")]
    [InlineData("public sealed class K { public static K A { get; } = new(); }", "constructor that is not private")]
    [InlineData("public sealed class K { public static K A => new(); private K() { } }", "static instance that is not an initialised get-only auto-property or readonly field")]
    [InlineData("public sealed class K { public static K A { get { return new(); } } private K() { } }", "static instance that is not an initialised get-only auto-property or readonly field")]
    [InlineData("public sealed class K { public static K A = new(); private K() { } }", "static instance that is not an initialised get-only auto-property or readonly field")]
    [InlineData("public sealed class K { public static K A { get; } = new(); public static K B { get; } = A; private K() { } }", "static instance that is not an initialised get-only auto-property or readonly field")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } public static K Make() => new(); }", "constructor called outside the static instances")]
    [InlineData("public sealed class K { private K() { } }", "no static instances")]
    public void ClosedClassFailingAStepIsWrt0009NamingIt(string declaration, string step)
    {
        var result = Extract("[Closed]\n" + declaration);
        Assert.Equal("WRT0009 | " + step, Only(result, "T:K"));
        Assert.Equal(ExtractionSeverity.Error, Assert.Single(result.Diagnostics).Severity);
    }

    [Fact]
    public void ClosedClassWithBaseEqualityIsAcceptedWithAnIdentityAssumption()
    {
        var result = Extract("""
            public abstract class Named
            {
                protected Named(string name) => Name = name;
                public string Name { get; }
                public override bool Equals(object? obj) => obj is Named n && n.Name == Name;
                public override int GetHashCode() => Name.Length;
            }

            [Closed]
            public sealed class Level : Named
            {
                public static Level Low { get; } = new("Low");
                public static readonly Level High = new("High");
                private Level(string name) : base(name) { }
            }

            public static class C
            {
                [Verified] public static bool IsLow(Level l) => l == Level.Low;
            }
            """);
        Assert.Empty(result.Diagnostics);
        var type = Unit(result, "T:Level");
        Assert.Equal(new ClosedDefinition(VirList.Of(new VirClosedMember("Low", null), new VirClosedMember("High", null))), type.Definition);
        Assert.Contains(new VirAssumption(VirAssumptionKind.ClosedEquality, "T:Level"), type.Assumptions);
        var member = Unit(result, "M:C.IsLow(Level)");
        Assert.Equal(
            [
                new VirAssumption(VirAssumptionKind.NonNull, "l"),
                new VirAssumption(VirAssumptionKind.Closed, "T:Level"),
                new VirAssumption(VirAssumptionKind.ClosedEquality, "T:Level"),
            ],
            member.Assumptions);
    }

    [Fact]
    public void ClosedClassWithoutItsOwnEqualityHasNoIdentityAssumption()
    {
        var result = Extract("""
            [Closed]
            public sealed class Level
            {
                public static Level Low { get; } = new();
                private Level() { }
            }

            public static class C
            {
                [Verified] public static bool IsLow(Level l) => l == Level.Low;
            }
            """);
        var type = Unit(result, "T:Level");
        Assert.Equal([new VirAssumption(VirAssumptionKind.Closed, "T:Level")], type.Assumptions);
    }

    [Theory]
    [InlineData("public sealed record R(int X) { public int Extra { get; init; } }", "record with other instance state")]
    [InlineData("public sealed record R(int X) { private readonly int _y = 1; }", "record with other instance state")]
    [InlineData("public sealed record R(int X) { public int casesOn() => 1; }", "reserved member name")]
    [InlineData("public sealed record R(int X) { public bool Equals(R? other) => true; public override int GetHashCode() => 0; }", "record with its own equality")]
    [InlineData("public record R(int X);", "unsealed record")]
    [InlineData("public sealed record R { public int X { get; init; } }", "record that is not positional")]
    [InlineData("public sealed record R(string X);", "string")]
    public void RecordShapeIsChecked(string declaration, string construct)
    {
        var result = Extract(declaration + """

            public static class C
            {
                [Verified] public static R Same(R r) => r;
            }
            """);
        Assert.Equal("WRT0002 | " + construct, Only(result, "T:R"));
        Assert.Equal("WRT0002 | depends on a rejected unit", Only(result, "M:C.Same(R)"));
    }

    [Fact]
    public void RecordWithAComputedPropertyIsAccepted()
    {
        var result = Extract("""
            public sealed record R(int X)
            {
                public bool IsLarge => X > 1000;
            }

            public static class C
            {
                [Verified] public static int Get(R r) => r.X;
            }
            """);
        Assert.Empty(result.Diagnostics);
        Assert.Equal(new RecordDefinition(VirList.Of(new VirField("X", VirType.Int32))), Unit(result, "T:R").Definition);
    }

    [Fact]
    public void ReservedNameOnAClosedEnumIsRejected()
    {
        var result = Extract("""
            [Closed] public enum E { rec, Other }
            public static class C { [Verified] public static bool F(E e) => e == E.Other; }
            """);
        Assert.Equal("WRT0002 | reserved member name", Only(result, "T:E"));
    }

    [Fact]
    public void ClosedEnumCastsAndUnboxingWarnAnywhere()
    {
        var result = Extract("""
            [Closed] public enum Phase { Draft, Open }
            [Closed] public enum NoZero { One = 1 }
            public static class C
            {
                public static Phase Cast(int x) => (Phase)x;
                public static Phase Unbox(object o) => (Phase)o;
                public static System.Func<int, Phase> InLambda() => x => (Phase)x;
                public static Phase Named() => Phase.Open;
            }
            """);
        Assert.Equal("WRT0008 | integer cast to a closed enum", Only(result, "M:C.Cast(System.Int32)"));
        Assert.Equal("WRT0008 | unboxing to a closed enum", Only(result, "M:C.Unbox(System.Object)"));
        Assert.Equal("WRT0008 | integer cast to a closed enum", Only(result, "M:C.InLambda"));
        Assert.Equal("WRT0008 | closed enum without a member valued 0", Only(result, "T:NoZero"));
        Assert.Empty(result.DiagnosticsFor("M:C.Named"));
        Assert.All(result.Diagnostics, d => Assert.Equal(ExtractionSeverity.Warning, d.Severity));
    }

    [Fact]
    public void ClosedEnumConstantsAreRejectedInVerifiedCode()
    {
        var result = Extract("""
            [Closed] public enum Phase { Draft, Open, Closed }
            public static class C
            {
                [Verified] public static Phase Five() => (Phase)5;
                [Verified] public static Phase One() => (Phase)1;
                [Verified] public static Phase Default() => default(Phase);
            }
            """);
        Assert.Contains(result.DiagnosticsFor("M:C.Five"), d => d.Id == "WRT0002" && d.Construct == "integer cast to a closed enum");
        Assert.Contains(result.DiagnosticsFor("M:C.One"), d => d.Id == "WRT0002" && d.Construct == "integer cast to a closed enum");
        Assert.Equal("WRT0002 | default of a closed enum", Only(result, "M:C.Default"));
    }

    [Fact]
    public void RecordValuesAndTheirFieldsAreAssumedNonNull()
    {
        var result = Extract("""
            public enum Status { Pending, Paid }
            public sealed record Payment(int Id, int Amount, Status Status);
            [Closed] public sealed class Outcome { public static Outcome Matched { get; } = new(); private Outcome() { } }
            public sealed record Inner(Payment Payment, int N);
            public sealed record Outer(Inner Inner, Outcome Outcome)
            {
                [Verified] public int Amount => Inner.Payment.Amount;
            }

            public static class C
            {
                [Verified] public static int Validate(Payment p) => p.Amount;
                [Verified] public static int Deep(Outer o, int n) => o.Inner.N + n;
                [Verified] public static int Maybe(Payment? p) => 0;
            }
            """);
        Assert.Equal(["p"], NonNull(Unit(result, "M:C.Validate(Payment)")));
        Assert.Equal(["o", "o.Inner", "o.Inner.Payment", "o.Outcome"], NonNull(Unit(result, "M:C.Deep(Outer,System.Int32)")));
        Assert.Equal(["this.Inner", "this.Inner.Payment", "this.Outcome"], NonNull(Unit(result, "P:Outer.Amount")));
        Assert.Equal("WRT0002 | nullable type", Only(result, "M:C.Maybe(Payment)"));
    }

    [Fact]
    public void EnumConstantsBecomeMembersOrLiteralsOfTheEnumType()
    {
        var result = Extract("""
            [Closed] public enum ClaimStatus { Open, Paid }
            public enum PaymentStatus { Pending, Processed, Failed }
            public static class C
            {
                [Verified] public static ClaimStatus Open() => ClaimStatus.Open;
                [Verified] public static PaymentStatus Seven() => (PaymentStatus)7;
                [Verified] public static PaymentStatus One() => (PaymentStatus)1;
            }
            """);
        var claim = VirType.Ref("T:ClaimStatus");
        var payment = VirType.Ref("T:PaymentStatus");
        Assert.Equal(new MemberExpr(claim, "Open"), Unit(result, "M:C.Open").Body);
        Assert.Equal(new LitExpr(payment, 7), Unit(result, "M:C.Seven").Body);
        Assert.Equal(new MemberExpr(payment, "Processed"), Unit(result, "M:C.One").Body);
    }

    [Fact]
    public void SpecImpliesIsAnImplicationInATheoremStatement()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static bool Pos(int x) => x > 0;
                [Theorem] static Proof T() => Prove.That(Spec.Implies(Pos(1), Pos(2)));
            }
            """);
        var call = (int n) => new CallExpr(VirType.Bool, "M:C.Pos(System.Int32)", VirList.Of<VirExpr>(LitExpr.Int32(n)));
        var theorem = Unit(result, "M:C.T");
        Assert.Equal(VirUnitKind.Theorem, theorem.Kind);
        Assert.Equal(new ImpliesExpr(call(1), call(2)), theorem.Statement);
        Assert.Equal(["M:C.Pos(System.Int32)"], theorem.Deps);
    }

    [Fact]
    public void ClosedAttributeOnAMethodDoesNotCompile()
    {
        var result = Extract("""
            public static class C
            {
                [Closed] public static int F() => 0;
            }
            """);
        Assert.True(result.HasCompileErrors);
        Assert.Contains(result.Diagnostics, d => d.Id == "CS0592");
    }

    [Fact]
    public void PayoutMatchesTheGoldenVir()
    {
        var unit = Corpus.Extract("accepted").Find("M:Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)");
        Assert.NotNull(unit);
        var golden = File.ReadAllBytes(Path.Combine(AppContext.BaseDirectory, "golden", "payout.json"));
        Assert.Equal(golden, VirWriter.Write(unit.Unit));
    }

    [Fact]
    public void SpansAreKeptBesideTheUnit()
    {
        var unit = Corpus.Extract("accepted").Find("M:Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)")!;
        var nodes = VirTree.PreOrder(unit.Unit);
        int sub = nodes.ToList().FindIndex(n => n is BinaryExpr { Op: BinaryOp.Sub });
        Assert.True(unit.Spans.TryGetSpan(sub, out var span));

        Assert.Equal(new VirSpan("accepted/PayoutRules.cs", 12, 23, 12, 40), span);
        Assert.Equal(nodes.Count, unit.Spans.Count);
        Assert.Equal(new VirSpan("accepted/PayoutRules.cs", 9, 23, 9, 29), unit.Location);
        Assert.Equal("Payouts.PayoutRules.Payout(int, int, int)", unit.DisplayName);
    }

    [Fact]
    public void ExtractingTwiceGivesIdenticalVir()
    {
        foreach (var name in Corpus.CompilationNames)
        {
            var first = Extractor.Extract(Corpus.Compile(name));
            var second = Extractor.Extract(Corpus.Compile(name));
            Assert.Equal(first.Units.Select(u => u.Key), second.Units.Select(u => u.Key));
            for (int i = 0; i < first.Units.Count; i++)
            {
                Assert.Equal(VirWriter.Write(first.Units[i].Unit), VirWriter.Write(second.Units[i].Unit));
            }
            Assert.Equal(first.Diagnostics, second.Diagnostics);
        }
    }

    [Fact]
    public void FactsRecordTheLanguageExtractorAndRoslyn()
    {
        var unit = Corpus.Extract("accepted").Units[0].Unit;
        Assert.Equal("14", unit.Facts.Language);
        Assert.Equal(Extractor.Version, unit.Facts.Extractor);
        var v = typeof(CSharpCompilation).Assembly.GetName().Version!;
        Assert.Equal($"{v.Major}.{v.Minor}.{v.Build}", unit.Facts.Roslyn);
        Assert.Equal("7.3", Extractor.LanguageText(LanguageVersion.CSharp7_3));
    }

    [Fact]
    public void SwitchExpressionOverAClosedEnumCoveringEveryMemberIsAccepted()
    {
        var result = Extract("""
            [Closed] public enum Phase { Draft, Open }
            public enum Light { Red, Green }
            public static class C
            {
                [Verified] public static int Full(Phase p) => p switch { Phase.Draft => 0, Phase.Open => 1 };
                [Verified] public static int Partial(Phase p) => p switch { Phase.Draft => 0 };
                [Verified] public static int Open(Light l) => l switch { Light.Red => 0, Light.Green => 1 };
            }
            """);
        Assert.Empty(result.DiagnosticsFor("M:C.Full(Phase)"));
        Assert.Equal("WRT0002 | non-exhaustive switch expression", Only(result, "M:C.Partial(Phase)"));
        Assert.Equal("WRT0002 | non-exhaustive switch over an open enum", Only(result, "M:C.Open(Light)"));
    }
}
