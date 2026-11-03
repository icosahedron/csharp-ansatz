using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Frontend;

namespace Warrant.Extraction.Tests;

/// <summary>The compilation factory (docs/m4/03, "Building the compilation").</summary>
public class FrontendTests
{
    public static TheoryData<string> AcceptedAndRefutedFiles =>
        new(Corpus.Files("accepted").Concat(Corpus.Files("refuted")));

    [Theory]
    [MemberData(nameof(AcceptedAndRefutedFiles))]
    public void CorpusFileCompilesWithTheFactory(string file)
    {
        // Accepted files share types across files, so each is compiled with its whole compilation.
        var name = file.Split('/')[0];
        var compilation = CompilationFactory.FromFiles(Corpus.Root, Corpus.Files(name), checkOverflow: false);
        Assert.Contains(compilation.SyntaxTrees, t => t.FilePath == file);
        Assert.Empty(compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error));
    }

    [Fact]
    public void WarrantIsReferencedFromTheEmbeddedImage()
    {
        var reference = Assert.IsAssignableFrom<PortableExecutableReference>(CompilationFactory.WarrantReference);
        Assert.Equal("Warrant.dll", reference.FilePath);
        Assert.Contains("Warrant.dll", typeof(CompilationFactory).Assembly.GetManifestResourceNames());

        var compilation = Corpus.Compile("accepted");
        Assert.Contains(CompilationFactory.WarrantReference, compilation.References);
        var warrant = Assert.IsAssignableFrom<IAssemblySymbol>(compilation.GetAssemblyOrModuleSymbol(CompilationFactory.WarrantReference));
        Assert.Equal("Warrant", warrant.Identity.Name);
        Assert.NotNull(warrant.GetTypeByMetadataName("Warrant.VerifiedAttribute"));
    }

    [Fact]
    public void OptionsAreTheCorpusSettings()
    {
        var compilation = CompilationFactory.Create([new SourceFile("A.cs", "class A { }")], checkOverflow: true);
        Assert.Equal(LanguageVersion.CSharp14, compilation.LanguageVersion);
        Assert.Equal(NullableContextOptions.Enable, compilation.Options.NullableContextOptions);
        Assert.True(compilation.Options.Deterministic);
        Assert.True(compilation.Options.CheckOverflow);
        Assert.False(CompilationFactory.Create([], checkOverflow: false).Options.CheckOverflow);
    }

    [Fact]
    public void SourcesAreOrderedByRelativePath()
    {
        var compilation = CompilationFactory.Create(
            [new SourceFile("b\\Two.cs", "class Two { }"), new SourceFile("a/One.cs", "class One { }"), new SourceFile("B.cs", "class B { }")],
            checkOverflow: false);
        Assert.Equal(["B.cs", "a/One.cs", "b/Two.cs"], compilation.SyntaxTrees.Select(t => t.FilePath));
    }
}
