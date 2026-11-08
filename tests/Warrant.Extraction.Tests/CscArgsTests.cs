using Basic.Reference.Assemblies;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Warrant.Frontend;
using Warrant.TestSupport;
using Warrant.Vir;
using static Warrant.Extraction.Tests.Inline;

namespace Warrant.Extraction.Tests;

/// <summary>
/// Compilations from the compiler's own arguments (plan M5a U12, KTD21; docs/m5a/07, "Reproducing the compilation").
/// <c>cscargs/sample.csc.args</c> is <c>@(CscCommandLineArgs)</c> from a <c>dotnet build</c> of a net10.0 library, with
/// the reference pack's paths replaced by <c>refs/</c>, <c>obj/Debug/net10.0/</c> by <c>generated/</c>, a reference to
/// <c>refs/Warrant.dll</c> added, paths written with forward slashes so the file works on every OS, and the SDK's analyzers and global analyzer config removed.
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

    /// <summary>The sample's arguments plus <c>/analyzer:</c> for a generator built from <paramref name="generator"/>.</summary>
    private (CSharpCompilation Compilation, IReadOnlyList<string> Problems) CompileWithGenerator(string generator, string source) =>
        CompileWithArgs(source, "/analyzer:" + SourceGeneratorAssemblies.Build(Path.Combine(project, "analyzers"), "TestGenerator", generator));

    /// <summary>The sample's arguments plus <paramref name="extra"/>, over <c>src/C.cs</c> holding <paramref name="source"/>.</summary>
    private (CSharpCompilation Compilation, IReadOnlyList<string> Problems) CompileWithArgs(string source, params string[] extra)
    {
        Directory.CreateDirectory(Path.Combine(project, "src"));
        File.WriteAllText(Path.Combine(project, "src", "C.cs"), "using Warrant;\n" + source);
        var args = Path.Combine(project, "generated.csc.args");
        File.WriteAllLines(args, File.ReadAllLines(ArgsFile).Concat(extra));
        var compilation = CompilationFactory.FromCscArgs(args, project, out var problems);
        return (compilation, problems);
    }

    private const string Compiles = "public static class C { [Verified] public static int F(int x) => x; }";

    [Fact]
    public void AGeneratorBuiltForANewerCompilerFailsEvenThoughTheCodeCompiles()
    {
        // Csc on a newer SDK would run it, and its output (an interceptor, a closer overload) could change what F means.
        var generator = SourceGeneratorAssemblies.BuildForNewerCompiler(Path.Combine(project, "analyzers"), generator: true);
        var (compilation, problems) = CompileWithArgs(Compiles, "/analyzer:" + generator);
        Assert.Contains(problems, p => p.Contains("ReferencesNewerCompiler", StringComparison.Ordinal));
        var failure = CompilationFactory.Failure(compilation, problems);
        Assert.NotNull(failure);
        Assert.Empty(failure.Errors);
        Assert.StartsWith("A source generator did not run", failure.Message, StringComparison.Ordinal);
        Assert.Contains("NewerGenerator.dll", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AnAnalyzerWithoutAGeneratorThatFailsToLoadDoesNotFailTheCompilation()
    {
        var analyzer = SourceGeneratorAssemblies.BuildForNewerCompiler(Path.Combine(project, "analyzers"), generator: false);
        var (compilation, problems) = CompileWithArgs(Compiles, "/analyzer:" + analyzer);
        Assert.Empty(problems);
        Assert.Null(CompilationFactory.Failure(compilation, problems));
    }

    [Fact]
    public void AnAnalyzerFileThatIsNotAnAssemblyFailsClosed()
    {
        var path = Path.Combine(project, "analyzers", "NotAnAssembly.dll");
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, "not a PE file");
        var (compilation, problems) = CompileWithArgs(Compiles, "/analyzer:" + path);
        Assert.Contains(problems, p => p.Contains("NotAnAssembly.dll", StringComparison.Ordinal));
        Assert.NotNull(CompilationFactory.Failure(compilation, problems));
    }

    [Fact]
    public void AGeneratorThatThrowsFailsEvenThoughTheCodeCompiles()
    {
        var (compilation, problems) = CompileWithGenerator(SourceGeneratorAssemblies.Throwing, Compiles);
        var failure = CompilationFactory.Failure(compilation, problems);
        Assert.NotNull(failure);
        Assert.Empty(failure.Errors);
        Assert.Contains("generator failed on purpose", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GeneratorsSeeTheAdditionalFilesAndTheAnalyzerConfig()
    {
        File.WriteAllText(Path.Combine(project, "input.txt"), "from-the-file");
        File.WriteAllText(Path.Combine(project, "global.editorconfig"), "is_global = true\nbuild_property.WarrantTest = from-the-config\n");
        var analyzer = SourceGeneratorAssemblies.Build(Path.Combine(project, "analyzers"), "TestGenerator", SourceGeneratorAssemblies.ReadingInputs);
        var (compilation, problems) = CompileWithArgs(Compiles, "/analyzer:" + analyzer, "/additionalfile:input.txt", "/analyzerconfig:global.editorconfig");
        Assert.Empty(problems);
        Assert.Null(CompilationFactory.Failure(compilation, problems));
        var inputs = compilation.GetTypeByMetadataName("FromInputs");
        Assert.NotNull(inputs);
        Assert.Equal("from-the-file", inputs.GetMembers("Text").OfType<IFieldSymbol>().Single().ConstantValue);
        Assert.Equal("from-the-config", inputs.GetMembers("Option").OfType<IFieldSymbol>().Single().ConstantValue);
    }

    [Fact]
    public void AGeneratorInTheArgumentsRunsAndTheCodeThatNeedsItsOutputCompiles()
    {
        var (compilation, problems) = CompileWithGenerator(
            SourceGeneratorAssemblies.Adding("public sealed class GeneratedSettings { }"),
            """
            public static class C
            {
                [Verified] public static int F(int x) => x;
                public static object Settings() => new GeneratedSettings();
            }
            """);
        Assert.Empty(problems);
        Assert.Null(CompilationFactory.Failure(compilation, problems));
        Assert.NotNull(compilation.GetTypeByMetadataName("GeneratedSettings"));
        Assert.Contains(compilation.SyntaxTrees, t => t.FilePath.EndsWith("Added.g.cs", StringComparison.Ordinal));
    }

    [Fact]
    public void AGeneratorThatThrowsIsNamedInTheFailure()
    {
        var (compilation, problems) = CompileWithGenerator(
            SourceGeneratorAssemblies.Throwing,
            "public static class C { public static object Settings() => new GeneratedSettings(); }");
        var failure = CompilationFactory.Failure(compilation, problems);
        Assert.NotNull(failure);
        Assert.Equal(["GeneratedSettings"], failure.MissingSymbols);
        Assert.Contains("A source generator did not run", failure.Message, StringComparison.Ordinal);
        Assert.Contains("generator failed on purpose", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AnInterceptedCallIsFoundInVerifiedCodeOnly()
    {
        var (compilation, problems) = CompileWithGenerator(
            SourceGeneratorAssemblies.Intercepting,
            """
            public static class C
            {
                public static int Original() => 0;
                [Verified] public static int F() => Original();
                public static int G() => Original();
            }
            """);
        Assert.Empty(problems);
        Assert.Null(CompilationFactory.Failure(compilation, problems));
        var intercepted = CompilationFactory.InterceptedCalls(compilation);
        var (location, interceptor) = Assert.Single(intercepted);
        Assert.Equal(4, location.GetLineSpan().StartLinePosition.Line); // line 5 of C.cs: F, after the added using
        Assert.Equal("Replacement", interceptor.Name);
    }

    [Fact]
    public void AnInterceptedCallIsFoundInATheoremAPropertyALambdaAndALocalFunction()
    {
        var (compilation, problems) = CompileWithGenerator(
            SourceGeneratorAssemblies.Intercepting,
            """
            public static class C
            {
                public static int Original() => 0;
                [Theorem] static Proof T() => Prove.That(Original() == 1);
                [Verified] public static int P => Original();
                [Verified] public static int Q { get { return Original(); } }
                [Verified] public static int L() { System.Func<int> f = () => Original(); return f(); }
                [Verified] public static int Local() { int G() => Original(); return G(); }
                public static int Unverified => Original();
            }
            """);
        Assert.Empty(problems);
        var lines = CompilationFactory.InterceptedCalls(compilation).Select(c => c.Location.GetLineSpan().StartLinePosition.Line + 1).Order();
        Assert.Equal([5, 6, 7, 8, 9], lines); // C.cs lines, after the added using; line 10 is unverified
    }

    [Fact]
    public void WithoutAnalyzersNoCallIsIntercepted()
    {
        var compilation = Compile("public static class C { public static int Original() => 0; [Verified] public static int F() => Original(); }");
        Assert.Empty(CompilationFactory.InterceptedCalls(compilation));
    }

    /// <summary>
    /// A source record as Warrant.Build writes it (#32, #51): every file in the project, references and generators
    /// included, hashed now, so the record covers what the arguments read.
    /// </summary>
    private string Record(string assembly = "Sample", string? args = null)
    {
        var lines = new List<string> { "warrant-source 1", $"assembly={assembly}", $"args={args ?? ArgsFile}", $"project={project}" };
        foreach (var file in Directory.EnumerateFiles(project, "*", SearchOption.AllDirectories))
        {
            using var stream = File.OpenRead(file);
            lines.Add($"file={Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(stream)).ToLowerInvariant()}|{file}");
        }
        var record = Path.Combine(project, "warrant.source");
        File.WriteAllLines(record, lines);
        return record;
    }

    [Fact]
    public void ARecordedSourceLoadsOnceWithPathsRelativeToTheVerifiedProject()
    {
        Compile("[Closed] public sealed class Color { private Color() { } public static Color Red { get; } = new(); }");
        var source = ReferencedSource.Open(Record());
        var consumer = Path.Combine(project, "app");

        var compilation = source.Load(consumer);

        Assert.Equal("Sample", source.AssemblyName);
        Assert.Contains("../src/C.cs", compilation.SyntaxTrees.Select(t => t.FilePath));
        Assert.NotNull(compilation.GetTypeByMetadataName("Color"));
        Assert.Same(compilation, source.Load(consumer));
    }

    [Fact]
    public void ASourceFileEditedAfterTheRecordIsDeclined()
    {
        Compile("public static class C { }");
        var source = ReferencedSource.Open(Record());
        File.AppendAllText(Path.Combine(project, "src", "C.cs"), "// edited" + Environment.NewLine);

        var e = Assert.Throws<InvalidDataException>(() => source.Load(project));
        Assert.Contains("C.cs changed since Sample was compiled; build Sample again", e.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ASourceFileTheRecordDoesNotCoverIsDeclined()
    {
        Compile("public static class C { }");
        var record = Record();
        File.WriteAllLines(record, File.ReadAllLines(record).Where(l => !l.EndsWith("C.cs", StringComparison.Ordinal)));

        var e = Assert.Throws<InvalidDataException>(() => ReferencedSource.Open(record).Load(project));
        Assert.Contains("C.cs, which Sample is compiled from, is not in the record", e.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AReferenceChangedAfterTheRecordIsDeclined()
    {
        // #51: a referenced assembly decides what the source means (a base class, a constant), so it is hashed too.
        Compile("public static class C { }");
        var source = ReferencedSource.Open(Record());
        File.AppendAllBytes(Path.Combine(project, "refs", "Warrant.dll"), [0]);

        var e = Assert.Throws<InvalidDataException>(() => source.Load(project));
        Assert.Contains("Warrant.dll changed since Sample was compiled; build Sample again", e.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AReferenceTheRecordDoesNotCoverIsDeclined()
    {
        Compile("public static class C { }");
        var record = Record();
        File.WriteAllLines(record, File.ReadAllLines(record).Where(l => !l.EndsWith("System.Runtime.dll", StringComparison.Ordinal)));

        var e = Assert.Throws<InvalidDataException>(() => ReferencedSource.Open(record).Load(project));
        Assert.Contains("System.Runtime.dll, which Sample is compiled from, is not in the record", e.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AGeneratorChangedAfterTheRecordIsDeclined()
    {
        // #51: a generator can add a partial part or a constructor to a closed class, so its assembly is hashed too.
        var (_, problems) = CompileWithGenerator(SourceGeneratorAssemblies.Intercepting, "public static class C { }");
        Assert.Empty(problems);
        var source = ReferencedSource.Open(Record(args: Path.Combine(project, "generated.csc.args")));
        var generator = Directory.GetFiles(Path.Combine(project, "analyzers"), "TestGenerator.dll", SearchOption.AllDirectories).Single();
        File.AppendAllBytes(generator, [0]);

        var e = Assert.Throws<InvalidDataException>(() => source.Load(project));
        Assert.Contains("TestGenerator.dll changed since Sample was compiled; build Sample again", e.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AnEditedArgumentFileIsDeclined()
    {
        Compile("public static class C { }");
        var source = ReferencedSource.Open(Record());
        File.AppendAllText(ArgsFile, Environment.NewLine + "/define:EXTRA" + Environment.NewLine);

        var e = Assert.Throws<InvalidDataException>(() => source.Load(project));
        Assert.Contains("sample.csc.args changed since Sample was compiled", e.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ARecordNamingAnotherAssemblyIsDeclined()
    {
        Compile("public static class C { }");
        var e = Assert.Throws<InvalidDataException>(() => ReferencedSource.Open(Record("Other")).Load(project));
        Assert.Contains("the arguments compile 'Sample', not 'Other'", e.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ARecordedSourceThatDoesNotCompileIsDeclined()
    {
        Compile("public static class C { int F() => missing; }");
        var e = Assert.Throws<InvalidDataException>(() => ReferencedSource.Open(Record()).Load(project));
        Assert.Contains("Sample's recorded source does not compile", e.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AWarningMadeAnErrorDoesNotFailTheCompilation()
    {
        // Csc may have suppressed it with a DiagnosticSuppressor, which Warrant does not run.
        var (compilation, problems) = CompileWithArgs("public class C { public string S { get; set; } }", "/warnaserror+:Nullable");
        Assert.Contains(compilation.GetDiagnostics(), d => d.IsWarningAsError);
        Assert.Null(CompilationFactory.Failure(compilation, problems));
    }

    [Fact]
    public void AWarningMadeAnErrorDoesNotStopExtraction()
    {
        var (compilation, _) = CompileWithArgs(
            "public class C { public string S { get; set; } [Verified] public static int F(int x) => x; }", "/warnaserror+:Nullable");

        var result = Extractor.Extract(compilation, new ExtractionOptions { BuildDefines = true });

        Assert.False(result.HasCompileErrors);
        Assert.NotNull(result.Find("M:C.F(System.Int32)"));
    }

    [Fact]
    public void AFileThatIsNotARecordIsDeclined()
    {
        var notARecord = Path.Combine(project, "warrant.source");
        File.WriteAllText(notARecord, "something else" + Environment.NewLine);
        var e = Assert.Throws<InvalidDataException>(() => ReferencedSource.Open(notARecord));
        Assert.Contains("not a Warrant source record", e.Message, StringComparison.Ordinal);
    }
}
