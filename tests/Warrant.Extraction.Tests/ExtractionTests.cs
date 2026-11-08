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
        Assert.Equal("WRT0002 | mutual recursion", Only(result, "M:C.A(System.Int32)"));
        Assert.Equal("WRT0002 | mutual recursion", Only(result, "M:C.B(System.Int32)"));
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
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } public K Copy() => (K)MemberwiseClone(); }", "instance created or changed without a constructor call")]
    [InlineData("public sealed class K : B<K> { public static K A { get; } = new(); private K() { } } public abstract class B<T> { public T Copy() => (T)MemberwiseClone(); }", "instance created or changed without a constructor call")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } } public static class H { [System.Runtime.CompilerServices.UnsafeAccessor(System.Runtime.CompilerServices.UnsafeAccessorKind.Constructor)] public static extern K Make(); }", "instance created or changed without a constructor call")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } } public static class H { [System.Runtime.CompilerServices.UnsafeAccessor(System.Runtime.CompilerServices.UnsafeAccessorKind.Constructor)] public static extern object Make(); }", "instance created or changed without a constructor call")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } } public static class H { [System.Runtime.CompilerServices.UnsafeAccessor(System.Runtime.CompilerServices.UnsafeAccessorKind.Method, Name = \"MemberwiseClone\")] public static extern object Clone(object o); }", "instance created or changed without a constructor call")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } static K Twin() { [System.Runtime.CompilerServices.UnsafeAccessor(System.Runtime.CompilerServices.UnsafeAccessorKind.Constructor)] static extern K Make(); return Make(); } }", "instance created or changed without a constructor call")]
    // The review's silent passes (#55): a method group, base. on a class whose base is object, a type-parameter receiver
    // in a base class, a with expression, a dynamic constructor accessor and a static-field accessor that aliases instances.
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } public K Copy() { System.Func<object> f = MemberwiseClone; return (K)f(); } }", "instance created or changed without a constructor call")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } public K Copy() => (K)base.MemberwiseClone(); }", "instance created or changed without a constructor call")]
    [InlineData("public sealed class K : B { public static K A { get; } = new(); private K() { } } public abstract class B { public static object Dup<T>(T t) where T : B => t.MemberwiseClone(); }", "instance created or changed without a constructor call")]
    [InlineData("public sealed record K { public static K A { get; } = new(); private K() { } public int X { get; init; } } public static class H { public static K Make() => K.A with { X = 3 }; }", "instance created or changed without a constructor call")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } } public static class H { [System.Runtime.CompilerServices.UnsafeAccessor(System.Runtime.CompilerServices.UnsafeAccessorKind.Constructor)] public static extern dynamic Make(); }", "instance created or changed without a constructor call")]
    [InlineData("public sealed class K { public static readonly K A = new(); public static readonly K B = new(); private K() { } } public static class H { [System.Runtime.CompilerServices.UnsafeAccessor(System.Runtime.CompilerServices.UnsafeAccessorKind.StaticField, Name = \"A\")] public static extern ref K RefA(K k); }", "instance created or changed without a constructor call")]
    [InlineData("public sealed class K { private K() { } }", "no static instances")]
    [InlineData("public sealed class K { public static readonly K A = new(); public static readonly K B = new(); static K() { B = A; } private K() { } }", "static constructor")]
    [InlineData("public sealed class K { public static K A { get; } = new(); static K() { } private K() { } }", "static constructor")]
    [InlineData("public sealed class K { public static K A { get; } = new(0); private K(int x) { if (x == 0) throw new System.Exception(); } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(0); private K(int x) => Ratio = 10 / x; public int Ratio { get; } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(\"a\"); private K(string s) => Length = s.Length; public int Length { get; } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } private readonly int _x = int.Parse(\"x\"); }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } private static readonly int Bad = int.Parse(\"x\"); }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(int.Parse(\"1\")); private K(int x) => X = x; public int X { get; } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new() { X = 1 }; private K() { } public int X { get; init; } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(1); private K(int x) : this(x.ToString()) { } private K(string s) { } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(1); private K(int x) => X = x; private int _x; public int X { get => _x; set => _x = 100 / value; } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : B { public static K A { get; } = new(); private K() { } } public abstract class B { protected B() => throw new System.Exception(); }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : B { public static K A { get; } = new(); private K() { } } public abstract class B { static B() { } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : System.Collections.ArrayList { public static K A { get; } = new(); private K() { } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } private static readonly System.Index Start = -1; }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(1); private K(S s) { } } public struct S { public static implicit operator S(int x) => throw new System.Exception(); }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } public int P { get; } = int.Parse(\"1\"); }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(1L); private K(long x) => X = (int)x; public int X { get; } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : B { public static K A { get; } = new(); private K() : base(0) { } } public abstract class B(int y) : A0(100 / y) { } public abstract class A0 { protected A0(int x) { } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : B { public static K A { get; } = new(0); private K(int p) : base(p) { } public override int X { get => 0; set => _ = 100 / value; } } public abstract class B { protected B(int p) { X = p; } public virtual int X { get; set; } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : B { public static K A { get; } = new(); private K() { } } public abstract class B { private readonly int _x = int.Parse(\"x\"); }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : B { public static K A { get; } = new(); private K() { F = 1; } } public abstract class B { protected int F; }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } private readonly object _boxed = 5; }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : G<int> { public static K A { get; } = new(); private K() : base(0) { } } public abstract class G<T>(int y) : A0(100 / y) { } public abstract class A0 { protected A0(int x) { } }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : G<int> { public static K A { get; } = new(); private K() : base(0) { } } public abstract class G<T>(int y) { public int R { get; } = 100 / y; }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : B { public static K A { get; } = new(1); private K(int x) : base(x) { } } public abstract class B(int x) { private readonly S _s = x; } public struct S { public static implicit operator S(int x) => throw new System.Exception(); }", "constructor or initialiser that could throw")]
    [InlineData("public sealed class K : G<int> { public static K A { get; } = new(0); private K(int p) : base(p) { } public override int X { get => 0; set => _ = 100 / value; } } public abstract class G<T> { protected G(int p) { X = p; } public virtual int X { get; set; } }", "constructor or initialiser that could throw")]
    // Skipping a base's static initialisers relies on a base with a static constructor being rejected, including one
    // declared in another partial part of a generic base the class instantiates.
    [InlineData("public sealed class K : G<K> { public static K A { get; } = new(); private K() { } } public abstract partial class G<T> { private static readonly int Bad = int.Parse(\"x\"); } public abstract partial class G<T> { static G() { } }", "constructor or initialiser that could throw")]
    public void ClosedClassFailingAStepIsWrt0009NamingIt(string declaration, string step)
    {
        var result = Extract("[Closed]\n" + declaration);
        Assert.Equal("WRT0009 | " + step, Only(result, "T:K"));
        Assert.Equal(ExtractionSeverity.Error, Assert.Single(result.Diagnostics).Severity);
    }

    [Theory]
    [InlineData("public sealed class K { public static K A { get; } = new(\"a\", 1); public static readonly K B = new(null, 2); private K(string? name, long rank) { Name = name; _rank = rank; } public string? Name { get; } private readonly long _rank; }")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() : this(\"a\", 1 + 2) { } private K(string name, int rank) => Rank = rank; public int Rank { get; } private const int Max = 10; private static readonly int Limit = Max * 2; private readonly string _label = \"x\"; }")]
    [InlineData("public sealed class K : B { public static K A { get; } = new(3); private K(int r) : base(r) => _rank = r; private readonly long _rank; } public abstract class B(int y) : A0(y) { } public abstract class A0 { protected A0(int x) { Rank = x; } public int Rank { get; } }")]
    // #55: an [UnsafeAccessor] that constructs another type or reaches its field, and a MemberwiseClone of another type.
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } } public sealed class O { private int _x; } public static class H { [System.Runtime.CompilerServices.UnsafeAccessor(System.Runtime.CompilerServices.UnsafeAccessorKind.Field, Name = \"_x\")] public static extern ref int X(O o); }")]
    [InlineData("public sealed class K { public static K A { get; } = new(); private K() { } } public sealed class O { private O() { } public O Copy() => (O)MemberwiseClone(); } public static class H { [System.Runtime.CompilerServices.UnsafeAccessor(System.Runtime.CompilerServices.UnsafeAccessorKind.Constructor)] public static extern O Make(); }")]
    // #47: a primary-constructor parameter in an instance initialiser, a base class's non-constant static initialisers
    // (beforefieldinit: they run on first static-field access, not on construction), and generic base classes.
    [InlineData("public sealed class K : B { public static K A { get; } = new(1); private K(int x) : base(x) { } } public abstract class B(int x) { public int X { get; } = x; private readonly int _y = x; }")]
    [InlineData("public sealed class K : B { public static K A { get; } = new(); private K() { } } public abstract class B { private static readonly int Parsed = int.Parse(\"x\"); public static System.Lazy<int> L { get; } = new(() => 1); }")]
    [InlineData("""
        public sealed class K : StringSet<K>
        {
            public static K Low { get; } = new();
            public static K High { get; } = new();
            private K([System.Runtime.CompilerServices.CallerMemberName] string name = "") : base(name) { }
        }
        public abstract class StringSet<T>(string value) : SetBase<T, string>(value) where T : StringSet<T>
        {
            private static readonly System.Lazy<System.Collections.Generic.Dictionary<string, T>> ByName = new(() => new());
        }
        public abstract class SetBase<T, TValue>(TValue value) : System.IEquatable<T> where T : SetBase<T, TValue>
        {
            private static readonly System.Lazy<System.Collections.Generic.List<T>> All = new(() => new());
            public TValue Value { get; } = value;
            public bool Equals(T? other) => other is not null && System.Collections.Generic.EqualityComparer<TValue>.Default.Equals(Value, other.Value);
            public override bool Equals(object? o) => o is T t && Equals(t);
            public override int GetHashCode() => Value!.GetHashCode();
        }
        """)]
    public void ClosedClassWhoseConstructionCannotThrowIsAccepted(string declaration)
    {
        var result = Extract("[Closed]\n" + declaration + "\npublic static class C { [Verified] public static bool Same(K a, K b) => a == b; }");
        Assert.Empty(result.Diagnostics);
        Assert.Contains("T:K", result.Units.Select(u => u.Key));
    }

    [Fact]
    public void RecordFieldOfAClosedClassWithItsOwnEqualityIsRejected()
    {
        var result = Extract("""
            [Closed]
            public sealed class Level
            {
                public static Level Low { get; } = new(1);
                public static Level High { get; } = new(1);
                private Level(int rank) => Rank = rank;
                public int Rank { get; }
                public override bool Equals(object? obj) => obj is Level l && l.Rank == Rank;
                public override int GetHashCode() => Rank;
            }

            public sealed record Tagged(Level Level, int X);
            public sealed record MaybeTagged(Level? Level);

            public static class C
            {
                [Verified] public static bool Same(Tagged a, Tagged b) => a == b;
                [Verified] public static bool Same(MaybeTagged a, MaybeTagged b) => a == b;
            }
            """);
        Assert.Equal("WRT0002 | record field of a closed class with its own equality", Only(result, "T:Tagged"));
        Assert.Equal("WRT0002 | record field of a closed class with its own equality", Only(result, "T:MaybeTagged"));
        Assert.Equal("WRT0002 | depends on a rejected unit", Only(result, "M:C.Same(Tagged,Tagged)"));
        Assert.Empty(result.DiagnosticsFor("T:Level"));
    }

    [Fact]
    public void RecordFieldOfAClosedClassThatInheritsItsEqualityIsRejected()
    {
        var result = Extract("""
            public abstract class Ranked
            {
                protected Ranked(int rank) => Rank = rank;
                public int Rank { get; }
                public override bool Equals(object? obj) => obj is Ranked r && r.Rank == Rank;
                public override int GetHashCode() => Rank;
            }

            [Closed]
            public sealed class Level : Ranked
            {
                public static Level Low { get; } = new(1);
                private Level(int rank) : base(rank) { }
            }

            public sealed record Tagged(Level Level);

            public static class C
            {
                [Verified] public static bool Same(Tagged a, Tagged b) => a == b;
            }
            """);
        Assert.Equal("WRT0002 | record field of a closed class with its own equality", Only(result, "T:Tagged"));
    }

    [Fact]
    public void RecordEqualityOverAClosedClassFieldComparesItByInstance()
    {
        var result = Extract("""
            [Closed]
            public sealed class Level
            {
                public static Level Low { get; } = new();
                public static Level High { get; } = new();
                private Level() { }
            }

            public sealed record Tagged(Level Level, int X);

            public static class C
            {
                [Verified] public static bool Same(Tagged a, Tagged b) => a == b;
            }
            """);
        Assert.Empty(result.Diagnostics);
        var fields = Assert.IsType<RecordDefinition>(Unit(result, "T:Tagged").Definition).Fields;
        Assert.Equal(["Level", "X"], fields.Select(f => f.Name));
        Assert.Contains("T:Level", Unit(result, "T:Tagged").Deps);
        Assert.Equal(CompareKind.Record, Assert.IsType<CompareExpr>(Unit(result, "M:C.Same(Tagged,Tagged)").Body).Kind);
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
    [InlineData("public sealed record R(int X) { private R(R original) { X = original.X + 100; } }", "record with its own copy constructor")]
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
                public static Phase Add(Phase p) => p + 1;
                public static Phase Or(Phase p) => p | Phase.Open;
                public static Phase Complement(Phase p) => ~p;
                public static Phase Increment(Phase p) { p++; return p; }
                public static Phase Compound(Phase p) { p += 1; return p; }
                public static int Difference(Phase a, Phase b) => a - b;
                public static bool Compare(Phase a, Phase b) => a < b;
            }
            """);
        Assert.Equal("WRT0008 | integer cast to a closed enum", Only(result, "M:C.Cast(System.Int32)"));
        Assert.Equal("WRT0008 | unboxing to a closed enum", Only(result, "M:C.Unbox(System.Object)"));
        Assert.Equal("WRT0008 | integer cast to a closed enum", Only(result, "M:C.InLambda"));
        Assert.Equal("WRT0008 | closed enum without a member valued 0", Only(result, "T:NoZero"));
        Assert.Empty(result.DiagnosticsFor("M:C.Named"));
        foreach (var key in new[] { "M:C.Add(Phase)", "M:C.Or(Phase)", "M:C.Complement(Phase)", "M:C.Increment(Phase)", "M:C.Compound(Phase)" })
        {
            Assert.Equal("WRT0008 | arithmetic on a closed enum", Only(result, key));
        }
        Assert.Empty(result.DiagnosticsFor("M:C.Difference(Phase,Phase)"));
        Assert.Empty(result.DiagnosticsFor("M:C.Compare(Phase,Phase)"));
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
        // The golden file records Roslyn 5.0.0, the compiler it was written with; the Roslyn version is provenance.
        Assert.Equal(golden, VirWriter.Write(unit.Unit with { Facts = unit.Unit.Facts with { Roslyn = "5.0.0" } }));
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

    [Fact]
    public void EnumsWithValuesBeyondLongAreRejectedNotCrashed()
    {
        var result = Extract("""
            [Closed] public enum Big : ulong { Zero = 0, Max = ulong.MaxValue }
            public enum Huge : ulong { Max = ulong.MaxValue }
            public static class C
            {
                [Verified] public static Huge Get() => Huge.Max;
            }
            """);
        Assert.Equal("WRT0002 | enum with an underlying type other than int or long", Only(result, "T:Big"));
        Assert.Equal("WRT0002 | enum with an underlying type other than int or long", Only(result, "T:Huge"));
        Assert.Equal("WRT0002 | depends on a rejected unit", Only(result, "M:C.Get"));
        Assert.Empty(result.Units);
    }

    [Fact]
    public void CodeThatDiffersBetweenBuildsIsRejectedAndSoAreItsUsers()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int Plain(int x) => x;

                [Verified]
                public static int F()
                {
            #if DEBUG
                    return 1;
            #else
                    return 2;
            #endif
                }

                [Theorem] static Proof IsTwo() => Prove.That(F() == 2);
            }
            """);
        Assert.Equal("WRT0002 | preprocessor conditional", Only(result, "M:C.F"));
        Assert.Equal("WRT0002 | depends on a rejected unit", Only(result, "M:C.IsTwo"));
        Assert.Equal(["M:C.Plain(System.Int32)"], result.Units.Select(u => u.Key));
    }

    [Fact]
    public void AnOverloadUnderIfThatChangesACallRejectsTheCaller()
    {
        // G(5) calls G(int) when DEBUG is defined and G(long) otherwise, though Caller has no #if of its own.
        var result = Extract("""
            public static class C
            {
            #if DEBUG
                [Verified] public static int G(int x) => 1;
            #endif
                [Verified] public static int G(long x) => 2;

                [Verified] public static int Caller() => G(5);
            }
            """);
        Assert.Equal("WRT0002 | preprocessor conditional", Only(result, "M:C.Caller"));
        Assert.Empty(result.DiagnosticsFor("M:C.G(System.Int64)"));
        Assert.Equal(["M:C.G(System.Int64)"], result.Units.Select(u => u.Key));
    }

    [Fact]
    public void AnIfThatTheVerifiedCodeDoesNotReachChangesNothing()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int F(int x) => x + 1;

            #if DEBUG
                public static void Log(string message) => System.Console.WriteLine(message);
            #endif
            }
            """);
        Assert.Empty(result.Diagnostics);
        Assert.Equal(["M:C.F(System.Int32)"], result.Units.Select(u => u.Key));
    }

    [Fact]
    public void BuildsThatDoNotCompileAreNotCompared()
    {
        // Without MODERN the file does not compile, so only the MODERN build is real.
        var result = Extract("""
            public static class C
            {
                [Verified] public static int F(int x) => x + 1;

            #if !MODERN
                public static int Old() => Missing();
            #endif
            }
            """);
        Assert.False(result.HasCompileErrors);
        Assert.Empty(result.Diagnostics);
        Assert.Equal(["M:C.F(System.Int32)"], result.Units.Select(u => u.Key));
    }

    [Fact]
    public void NoBuildCompilingReportsTheFirstBuildsErrors()
    {
        var result = Extract("""
            public static class C
            {
            #if DEBUG
                public static int A() => Missing();
            #else
                public static int B() => Missing();
            #endif
            }
            """);
        Assert.True(result.HasCompileErrors);
        Assert.Equal("CS0103", Assert.Single(result.Diagnostics).Id);
    }

    [Fact]
    public void AClosedEnumWarningFromAnyBuildIsReported()
    {
        var result = Extract("""
            [Closed] public enum Phase { Draft, Open }
            public static class C
            {
                [Verified] public static bool IsOpen(Phase p) => p == Phase.Open;
            #if DEBUG
                public static Phase Cast(int x) => (Phase)x;
            #endif
            }
            """);
        Assert.Equal("WRT0008 | integer cast to a closed enum", Only(result, "M:C.Cast(System.Int32)"));
        Assert.NotNull(result.Find("M:C.IsOpen(Phase)"));
    }

    [Fact]
    public void MoreThanSixSymbolsAreNotCombined()
    {
        var result = Extract("""
            public static class C
            {
                [Verified] public static int F(int x) => x;
            #if A || B || C1 || D || E || F1 || G
                public static int H() => 0;
            #endif
            }
            """);
        Assert.Empty(result.Units);
        var error = Assert.Single(result.Diagnostics);
        Assert.Equal(("WRT0002", "preprocessor conditional"), (error.Id, error.Construct));
        Assert.Equal(5, error.Location!.StartLine); // the #if, after Inline's using line
    }

    // Each of these is unsound to ignore: the model would drop the guard or the write.
    [Theory]
    [InlineData("public static int F(int n) { switch (n) { case 1 when n > 0: return 1; default: return 0; } }", "case guard")]
    [InlineData("public static int F(int n) { switch (n) { case > 1 when n < 5: return 1; default: return 0; } }", "case guard")]
    [InlineData("public static int F(int n) => n switch { > 0 when n < 5 => 1, _ => 0 };", "switch arm guard")]
    [InlineData("public static int F(int n) { n = 1; return n; }", "assignment to a parameter")]
    [InlineData("public static int F(int n) { n += 1; return n; }", "assignment to a parameter")]
    [InlineData("public static int F(int n) { n++; return n; }", "assignment to a parameter")]
    public void SoundnessCriticalConstructsAreRejected(string member, string construct)
    {
        var result = Extract("public static class C { [Verified] " + member + " }");
        Assert.Equal("WRT0002 | " + construct, Only(result, "M:C.F(System.Int32)"));
    }
}
