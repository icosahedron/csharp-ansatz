using Basic.Reference.Assemblies;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace Warrant.TestSupport;

/// <summary>
/// Source generator assemblies built for a test, as a project's <c>/analyzer:</c> arguments name them
/// (docs/m5a/07, "Source generators"). Also compiled into Warrant.Cli.Tests, which does not reference this project.
/// </summary>
public static class SourceGeneratorAssemblies
{
    /// <summary>An incremental generator that adds <paramref name="source"/> as <c>Added.g.cs</c>.</summary>
    /// <param name="source">The C# the generator adds, as a verbatim string's contents.</param>
    /// <returns>The generator's C# source.</returns>
    public static string Adding(string source) => $$""""
        using Microsoft.CodeAnalysis;
        [Generator]
        public sealed class AddingGenerator : IIncrementalGenerator
        {
            public void Initialize(IncrementalGeneratorInitializationContext context) =>
                context.RegisterPostInitializationOutput(c => c.AddSource("Added.g.cs", """
        {{source}}
        """));
        }
        """";

    /// <summary>An incremental generator that throws.</summary>
    public const string Throwing = """
        using Microsoft.CodeAnalysis;
        [Generator]
        public sealed class ThrowingGenerator : IIncrementalGenerator
        {
            public void Initialize(IncrementalGeneratorInitializationContext context) =>
                context.RegisterPostInitializationOutput(c => throw new System.InvalidOperationException("generator failed on purpose"));
        }
        """;

    /// <summary>
    /// An incremental generator that intercepts every call to a method named <c>Original</c> with
    /// <c>Microsoft.Extensions.Validation.Generated.Interceptors.Replacement</c>, which returns 1. The namespace must be in
    /// the compilation's <c>InterceptorsNamespaces</c> feature.
    /// </summary>
    public const string Intercepting = """"
        using System.Linq;
        using Microsoft.CodeAnalysis;
        using Microsoft.CodeAnalysis.CSharp;
        using Microsoft.CodeAnalysis.CSharp.Syntax;
        [Generator]
        public sealed class InterceptingGenerator : IIncrementalGenerator
        {
            public void Initialize(IncrementalGeneratorInitializationContext context)
            {
                var calls = context.SyntaxProvider.CreateSyntaxProvider(
                    (node, _) => node is InvocationExpressionSyntax { Expression: IdentifierNameSyntax { Identifier.Text: "Original" } },
                    (c, _) => c.SemanticModel.GetInterceptableLocation((InvocationExpressionSyntax)c.Node)!.GetInterceptsLocationAttributeSyntax());
                context.RegisterSourceOutput(calls.Collect(), (c, attributes) =>
                {
                    if (attributes.Length == 0) return;
                    c.AddSource("Interceptors.g.cs", $$"""
                        namespace System.Runtime.CompilerServices
                        {
                            [System.AttributeUsage(System.AttributeTargets.Method, AllowMultiple = true)]
                            file sealed class InterceptsLocationAttribute(int version, string data) : System.Attribute { }
                        }
                        namespace Microsoft.Extensions.Validation.Generated
                        {
                            static file class Interceptors
                            {
                                {{string.Join("\n", attributes)}}
                                public static int Replacement() => 1;
                            }
                        }
                        """);
                });
            }
        }
        """";

    /// <summary>Compiles a generator's source to <c>&lt;directory&gt;/&lt;name&gt;.dll</c> against this process's Roslyn.</summary>
    /// <param name="directory">The directory to write the assembly to.</param>
    /// <param name="name">The assembly name.</param>
    /// <param name="source">The generator's source.</param>
    /// <returns>The assembly's full path.</returns>
    public static string Build(string directory, string name, string source)
    {
        var references = Net100.References.All
            .Append(MetadataReference.CreateFromFile(typeof(ISourceGenerator).Assembly.Location))
            .Append(MetadataReference.CreateFromFile(typeof(CSharpCompilation).Assembly.Location));
        var compilation = CSharpCompilation.Create(
            name,
            [CSharpSyntaxTree.ParseText(source, new CSharpParseOptions(LanguageVersion.CSharp14))],
            references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, nullableContextOptions: NullableContextOptions.Disable));
        Directory.CreateDirectory(directory);
        var path = Path.Combine(directory, name + ".dll");
        var emitted = compilation.Emit(path);
        if (!emitted.Success)
        {
            throw new InvalidOperationException(
                "the test generator does not compile: " + string.Join("; ", emitted.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
        }
        return path;
    }
}
