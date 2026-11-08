using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Frontend;
using Warrant.Vir;

namespace Warrant.Extraction.Tests;

/// <summary>
/// A <c>[Closed]</c> class defined in a referenced project (#32): with that project's compilation it is checked from its
/// source like a class of the compilation itself, and the units that use it assume the referenced assembly was built
/// from that source; without it, it is still rejected.
/// </summary>
public sealed class ReferencedClosedClassTests
{
    private const string Colors = """
        namespace Lib;

        [Closed]
        public sealed class Color
        {
            private Color() { }
            public static Color Red { get; } = new();
            public static Color Blue { get; } = new();
        }
        """;

    private const string UsesColor = """
        public static class C
        {
            [Verified]
            public static int F(Lib.Color c) => c == Lib.Color.Red ? 1 : 0;
        }
        """;

    /// <summary>A smart enum whose value-comparing <c>==</c> is inherited from a generic base class.</summary>
    private const string Filters = """
        namespace Lib;

        public abstract class SetBase<T>(string value) where T : SetBase<T>
        {
            public string Value { get; } = value;
            public override bool Equals(object? o) => o is SetBase<T> s && s.Value == Value;
            public override int GetHashCode() => Value.GetHashCode();
            public static bool operator ==(SetBase<T>? left, SetBase<T>? right) => left?.Value == right?.Value;
            public static bool operator !=(SetBase<T>? left, SetBase<T>? right) => !(left == right);
        }

        [Closed]
        public sealed class Filter : SetBase<Filter>
        {
            private Filter(string value) : base(value) { }
            public static Filter Both { get; } = new("Both");
            public static Filter CatOnly { get; } = new("CatOnly");
        }
        """;

    private const string UsesFilter = """
        public static class C
        {
            [Verified]
            public static int F(Lib.Filter f) => f == Lib.Filter.CatOnly ? 8 : 0;

            [Verified]
            public static bool G(Lib.Filter f) => f != Lib.Filter.Both;
        }
        """;

    private static CSharpCompilation Library(string source, string name = "Lib") =>
        CompilationFactory.Create([new SourceFile("Lib.cs", "using Warrant;\n" + source)], checkOverflow: false, assemblyName: name);

    /// <summary>The consuming compilation, which sees the library only as metadata, as a project reference does.</summary>
    private static CSharpCompilation Consumer(CSharpCompilation library, string source)
    {
        using var image = new MemoryStream();
        var emitted = library.Emit(image);
        Assert.True(emitted.Success, string.Join("\n", emitted.Diagnostics));
        var reference = MetadataReference.CreateFromImage(image.ToArray());
        return CompilationFactory.Create([new SourceFile("Test.cs", "using Warrant;\n" + source)], checkOverflow: false)
            .AddReferences(reference);
    }

    private static ExtractionResult Extract(CSharpCompilation consumer, params CSharpCompilation[] sources) =>
        Extractor.Extract(consumer, new ExtractionOptions
        {
            ReferencedSource = name => sources.FirstOrDefault(c => c.AssemblyName == name),
        });

    private static string Diagnostics(ExtractionResult result) =>
        string.Join("\n", result.Diagnostics.Select(d => $"{d.Id} {d.MemberKey} {d.Construct}: {d.Message}"));

    [Fact]
    public void AReferencedClosedClassIsCheckedFromItsSourceAndAssumedBuiltFromIt()
    {
        var library = Library(Colors);
        var result = Extract(Consumer(library, UsesColor), library);

        Assert.True(result.Diagnostics.Count == 0, Diagnostics(result));
        var type = Inline.Unit(result, "T:Lib.Color");
        var definition = Assert.IsType<ClosedDefinition>(type.Definition);
        Assert.Equal(["Red", "Blue"], definition.Members.Select(m => m.Name));
        var member = Inline.Unit(result, "M:C.F(Lib.Color)");
        Assert.Contains(new VirAssumption(VirAssumptionKind.Closed, "T:Lib.Color"), member.Assumptions);
        Assert.Contains(new VirAssumption(VirAssumptionKind.ReferencedSource, "T:Lib.Color"), member.Assumptions);
        Assert.Contains(new VirAssumption(VirAssumptionKind.ReferencedSource, "T:Lib.Color"), type.Assumptions);
        Assert.DoesNotContain(member.Assumptions, a => a.Kind == VirAssumptionKind.ClosedEquality);
    }

    [Fact]
    public void AClosedClassOfTheCompilationItselfHasNoReferencedSourceAssumption()
    {
        // The file-scoped namespace puts C in Lib too.
        var result = Inline.Extract(Colors + "\n" + UsesColor);

        var member = Inline.Unit(result, "M:Lib.C.F(Lib.Color)");
        Assert.DoesNotContain(member.Assumptions, a => a.Kind == VirAssumptionKind.ReferencedSource);
    }

    [Fact]
    public void AnEqualityInheritedFromAGenericBaseIsModelledByIdentityUnderTheEqualityAssumption()
    {
        var library = Library(Filters);
        var result = Extract(Consumer(library, UsesFilter), library);

        Assert.True(result.Diagnostics.Count == 0, Diagnostics(result));
        foreach (var key in new[] { "M:C.F(Lib.Filter)", "M:C.G(Lib.Filter)" })
        {
            var member = Inline.Unit(result, key);
            Assert.Contains(new VirAssumption(VirAssumptionKind.ClosedEquality, "T:Lib.Filter"), member.Assumptions);
            Assert.Contains(new VirAssumption(VirAssumptionKind.ReferencedSource, "T:Lib.Filter"), member.Assumptions);
        }
    }

    [Fact]
    public void AnEqualityInheritedFromABaseIsAlsoAcceptedInTheDefiningCompilation()
    {
        var result = Inline.Extract(Filters + "\n" + UsesFilter);

        Assert.True(result.Diagnostics.Count == 0, Diagnostics(result));
        Assert.Contains(new VirAssumption(VirAssumptionKind.ClosedEquality, "T:Lib.Filter"), Inline.Unit(result, "M:Lib.C.F(Lib.Filter)").Assumptions);
    }

    [Fact]
    public void WithoutTheReferencedSourceTheClassIsStillRejected()
    {
        var library = Library(Colors);
        var result = Extract(Consumer(library, UsesColor));

        var d = Assert.Single(result.DiagnosticsFor("M:C.F(Lib.Color)"));
        Assert.Equal(("WRT0002", "type defined outside the compilation"), (d.Id, d.Construct));
        Assert.Contains("no recorded source for Lib that it can use; its project must import Warrant.Build", d.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ASourceOfTheSameNameButAnotherVersionIsNotUsed()
    {
        // The lookup is by name; only the identity check stops a source of another version standing for the reference.
        var library = Library(Colors);
        var otherVersion = Library("[assembly: System.Reflection.AssemblyVersion(\"2.0.0.0\")]\n" + Colors);
        Assert.Equal(library.AssemblyName, otherVersion.AssemblyName);
        var result = Extract(Consumer(library, UsesColor), otherVersion);

        Assert.Equal("WRT0002 | type defined outside the compilation", Inline.Only(result, "M:C.F(Lib.Color)"));
    }

    [Fact]
    public void AMultiTargetedProjectDoesNotUseAReferencedSource()
    {
        // The source is one target framework's build of the library; the other frameworks' builds of it may differ.
        var library = Library(Colors);
        var result = Extractor.Extract(Consumer(library, UsesColor), new ExtractionOptions
        {
            BuildDefines = true,
            KeepConditionalCheck = true,
            ReferencedSource = name => name == "Lib" ? library : null,
        });

        Assert.Equal("WRT0002 | type defined outside the compilation", Inline.Only(result, "M:C.F(Lib.Color)"));
    }

    [Fact]
    public void AReferencedClassWhoseFullNameTheCompilationAlsoDeclaresIsNotUsed()
    {
        // Type units are keyed by documentation-comment ID, which does not name the assembly.
        var library = Library(Colors);
        using var image = new MemoryStream();
        Assert.True(library.Emit(image).Success);
        var consumer = CompilationFactory.Create(
            [new SourceFile("Test.cs", """
                extern alias L;
                using Warrant;
                namespace Lib { public sealed class Color { } }
                public static class C
                {
                    [Verified]
                    public static int F(L::Lib.Color c) => c == L::Lib.Color.Red ? 1 : 0;
                }
                """)],
            checkOverflow: false).AddReferences(MetadataReference.CreateFromImage(image.ToArray()).WithAliases(["L"]));
        Assert.Empty(consumer.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error));

        var result = Extract(consumer, library);

        Assert.Equal("WRT0002 | type defined outside the compilation", Inline.Only(result, "M:C.F(Lib.Color)"));
    }

    /// <summary>Two closed classes sharing a non-generic base whose <c>==</c> compares values.</summary>
    private const string Shared = """
        public abstract class Named(string name)
        {
            public string Name { get; } = name;
            public override bool Equals(object? o) => o is Named n && n.Name == Name;
            public override int GetHashCode() => Name.GetHashCode();
            public static bool operator ==(Named? left, Named? right) => left?.Name == right?.Name;
            public static bool operator !=(Named? left, Named? right) => !(left == right);
        }

        [Closed]
        public sealed class A : Named
        {
            private A(string name) : base(name) { }
            public static A X { get; } = new("X");
        }

        [Closed]
        public sealed class B : Named
        {
            private B(string name) : base(name) { }
            public static B X { get; } = new("X");
        }
        """;

    [Theory]
    [InlineData("a == B.X")]
    [InlineData("a == (Named)A.X")]
    [InlineData("(Named)a != A.X")]
    public void AnInheritedEqualityIsModelledOnlyBetweenInstancesOfOneClosedClass(string comparison)
    {
        // A.X == B.X is true at runtime (both named "X"), so identity would be wrong; each class's own closed-equality
        // assumption says nothing about comparing it with another class.
        var result = Inline.Extract(Shared + $$"""

            public static class C
            {
                [Verified]
                public static bool F(A a) => {{comparison}};
            }
            """);

        Assert.Equal("WRT0002 | user-defined operator", Inline.Only(result, "M:C.F(A)"));
    }

    [Fact]
    public void AnInheritedEqualityBetweenInstancesOfOneClosedClassIsModelled()
    {
        var result = Inline.Extract(Shared + """

            public static class C
            {
                [Verified]
                public static bool F(A a) => a == A.X;
            }
            """);

        Assert.True(result.Diagnostics.Count == 0, Diagnostics(result));
        Assert.Contains(new VirAssumption(VirAssumptionKind.ClosedEquality, "T:A"), Inline.Unit(result, "M:C.F(A)").Assumptions);
    }

    [Theory]
    [InlineData("private Color() { _ = 1 / Zero(); } static int Zero() => 0;", "WRT0009", "constructor or initialiser that could throw")]
    [InlineData("private Color() { } public static Color Make() => new();", "WRT0009", "constructor called outside the static instances")]
    [InlineData("public Color() { }", "WRT0009", "constructor that is not private")]
    public void AReferencedClosedClassGetsTheSameShapeChecks(string constructor, string id, string construct)
    {
        var library = Library($$"""
            namespace Lib;

            [Closed]
            public sealed class Color
            {
                {{constructor}}
                public static Color Red { get; } = new();
            }
            """);
        var result = Extract(Consumer(library, UsesColor), library);

        Assert.Equal($"{id} | {construct}", Inline.Only(result, "T:Lib.Color"));
        Assert.Equal("WRT0002 | depends on a rejected unit", Inline.Only(result, "M:C.F(Lib.Color)"));
    }

    [Fact]
    public void AReferencedRecordIsStillRejected()
    {
        var library = Library("namespace Lib; public sealed record P(int X);");
        var result = Extract(Consumer(library, "public static class C { [Verified] public static int F(Lib.P p) => p.X; }"), library);

        Assert.Equal("WRT0002 | type defined outside the compilation", Inline.Only(result, "M:C.F(Lib.P)"));
    }

    [Fact]
    public void TheAnalyzerLeavesAReferencedClosedClassToTheBuild()
    {
        var library = Library(Colors);
        var consumer = Consumer(library, UsesColor);
        var diagnoser = new Diagnoser(consumer);

        var member = Assert.Single(diagnoser.Members());
        Assert.Empty(diagnoser.Member(member));
    }
}
