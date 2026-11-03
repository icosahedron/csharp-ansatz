using Basic.Reference.Assemblies;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Frontend;
using Warrant.Vir;
using static Warrant.Extraction.Tests.Inline;

namespace Warrant.Extraction.Tests;

/// <summary>
/// Compilations from the compiler's own arguments (plan M5a U12, KTD21; docs/m5a/07, "Reproducing the compilation").
/// <c>cscargs/sample.csc.args</c> is <c>@(CscCommandLineArgs)</c> from a <c>dotnet build</c> of a net10.0 library, with
/// the reference pack's paths replaced by <c>refs\</c>, <c>obj\Debug\net10.0\</c> by <c>generated\</c>, a reference to
/// <c>refs\Warrant.dll</c> added, and the SDK's analyzers and global analyzer config removed.
/// </summary>
public sealed class CscArgsTests : IDisposable
{
    private readonly string project = Path.Combine(Path.GetTempPath(), "warrant-cscargs-" + Guid.NewGuid().ToString("N"));

    public CscArgsTests()
    {
        var fixture = Path.Combine(AppContext.BaseDirectory, "cscargs");
        foreach (var file in Directory.EnumerateFiles(fixture, "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(project, Path.GetRelativePath(fixture, file));
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(file, target);
        }
        var refs = Directory.CreateDirectory(Path.Combine(project, "refs")).FullName;
        foreach (var info in Net100.ReferenceInfos.All)
        {
            File.WriteAllBytes(Path.Combine(refs, info.FileName), info.ImageBytes);
        }
        File.Copy(typeof(VerifiedAttribute).Assembly.Location, Path.Combine(refs, "Warrant.dll"));
    }

    public void Dispose() => Directory.Delete(project, recursive: true);

    private string ArgsFile => Path.Combine(project, "sample.csc.args");

    private CSharpCompilation Compile(string source)
    {
        Directory.CreateDirectory(Path.Combine(project, "src"));
        File.WriteAllText(Path.Combine(project, "src", "C.cs"), "using Warrant;\n" + source);
        return CompilationFactory.FromCscArgs(ArgsFile, project);
    }

    [Fact]
    public void TheCompilationHasTheCompilersOptions()
    {
        var compilation = Compile("public static class C { }");
        Assert.Equal("Sample", compilation.AssemblyName);
        Assert.Equal(OutputKind.DynamicallyLinkedLibrary, compilation.Options.OutputKind);
        Assert.True(compilation.Options.CheckOverflow);
        Assert.False(compilation.Options.AllowUnsafe);
        Assert.Equal(NullableContextOptions.Enable, compilation.Options.NullableContextOptions);
        Assert.Equal(LanguageVersion.CSharp14, compilation.LanguageVersion);
        var options = (CSharpParseOptions)compilation.SyntaxTrees[0].Options;
        Assert.Contains("DEBUG", options.PreprocessorSymbolNames);
        Assert.Contains("NET10_0", options.PreprocessorSymbolNames);
        Assert.Equal("Microsoft.Extensions.Validation.Generated", options.Features["InterceptorsNamespaces"].Split(';')[1]);
        Assert.Equal(["src/C.cs", "generated/.NETCoreApp,Version=v10.0.AssemblyAttributes.cs", "generated/Sample.AssemblyInfo.cs"], compilation.SyntaxTrees.Select(t => t.FilePath));
        Assert.Contains(compilation.References, r => Path.GetFileName(r.Display) == "Warrant.dll");
        Assert.NotNull(compilation.Options.SyntaxTreeOptionsProvider);
        Assert.Null(CompilationFactory.Failure(compilation));
    }

    [Fact]
    public void AnIfDebugMethodTranslatesUnderTheBuildsDefines()
    {
        var compilation = Compile("""
            public static class C
            {
                [Verified]
                public static int F() =>
            #if DEBUG
                    1;
            #else
                    2;
            #endif
            }
            """);
        var result = Extractor.Extract(compilation, new ExtractionOptions { BuildDefines = true });
        Assert.Empty(result.Diagnostics);
        Assert.Equal(LitExpr.Int32(1), Unit(result, "M:C.F").Body);

        // Without the build's defines flag, the same compilation still gets M4's combination check.
        Assert.Equal("WRT0002 | preprocessor conditional", Only(Extractor.Extract(compilation), "M:C.F"));
    }

    [Fact]
    public void ACSharp14FeatureInUnverifiedCodeCompiles()
    {
        var compilation = Compile("""
            public static class Extensions
            {
                extension(int x)
                {
                    public int Doubled => x * 2;
                }
            }
            public static class C
            {
                [Verified] public static int F(int x) => x;
                public static int G(int x) => x.Doubled;
            }
            """);
        Assert.Null(CompilationFactory.Failure(compilation));
        var result = Extractor.Extract(compilation, new ExtractionOptions { BuildDefines = true });
        Assert.Empty(result.Diagnostics);
        Assert.NotNull(result.Find("M:C.F(System.Int32)"));

        // The version is the argument's: under /langversion:13 the extension block is an error.
        File.WriteAllText(ArgsFile, File.ReadAllText(ArgsFile).Replace("/langversion:14", "/langversion:13", StringComparison.Ordinal));
        var older = CompilationFactory.FromCscArgs(ArgsFile, project);
        Assert.Equal(LanguageVersion.CSharp13, older.LanguageVersion);
        Assert.NotNull(CompilationFactory.Failure(older));
    }

    [Fact]
    public void KeepingTheConditionalCheckRejectsAMethodThatDiffersUnderNet8()
    {
        var compilation = Compile("""
            public static class C
            {
                [Verified] public static int Plain(int x) => x;

                [Verified]
                public static int F()
                {
            #if NET8_0
                    return 8;
            #else
                    return 10;
            #endif
                }
            }
            """);
        var result = Extractor.Extract(compilation, new ExtractionOptions { BuildDefines = true, KeepConditionalCheck = true });
        Assert.Equal("WRT0002 | preprocessor conditional", Only(result, "M:C.F"));
        Assert.Equal(["M:C.Plain(System.Int32)"], result.Units.Select(u => u.Key));
    }

    [Fact]
    public void ASourceThatNeedsAGeneratedTypeDoesNotCompileAndNamesIt()
    {
        var compilation = Compile("""
            public static class C
            {
                [Verified] public static int F(int x) => x;
                public static object Settings() => new GeneratedSettings();
            }
            """);
        var failure = CompilationFactory.Failure(compilation);
        Assert.NotNull(failure);
        Assert.Equal("WRT0012", CompilationFailure.Code);
        Assert.Equal(["GeneratedSettings"], failure.MissingSymbols);
        Assert.Contains(failure.Errors, d => d.Id == "CS0246");
        Assert.Contains("GeneratedSettings", failure.Message, StringComparison.Ordinal);
    }
}
