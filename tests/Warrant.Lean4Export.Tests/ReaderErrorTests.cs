using System.Text;
using Warrant.Cic;

namespace Warrant.Lean4Export.Tests;

/// <summary>The reader must reject malformed input with the offending line number.</summary>
public class ReaderErrorTests
{
    private const string Meta31 = """{"meta":{"exporter":{"name":"test","version":"1"},"format":{"version":"3.1.0"},"lean":{"githash":"","version":""}}}""";
    private const string Meta30 = """{"meta":{"exporter":{"name":"test","version":"1"},"format":{"version":"3.0.0"},"lean":{"githash":"","version":""}}}""";

    private static List<Declaration> ReadAll(params string[] lines)
    {
        var bytes = Encoding.UTF8.GetBytes(string.Join("\n", lines) + "\n");
        using var reader = new Lean4ExportReader(new MemoryStream(bytes));
        return reader.ReadDeclarations().ToList();
    }

    private static Lean4ExportFormatException Fails(params string[] lines) =>
        Assert.Throws<Lean4ExportFormatException>(() => ReadAll(lines));

    [Fact]
    public void AcceptsMinimalFile()
    {
        var decls = ReadAll(Meta31, """{"in":1,"str":{"pre":0,"str":"A"}}""", """{"ie":0,"sort":0}""",
            """{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}""");
        var axiom = Assert.IsType<AxiomInfo>(Assert.IsType<ConstantDeclaration>(Assert.Single(decls)).Constant);
        Assert.Equal(Name.Parse("A"), axiom.Name);
    }

    [Fact]
    public void ToleratesBlankLinesAndCrLf()
    {
        var bytes = Encoding.UTF8.GetBytes(Meta31 + "\r\n\r\n" + """{"in":1,"str":{"pre":0,"str":"A"}}""" + "\r\n" + """{"ie":0,"sort":0}""" + "\r\n   \r\n"
            + """{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}""");
        using var reader = new Lean4ExportReader(new MemoryStream(bytes));
        Assert.Single(reader.ReadDeclarations());
    }

    [Fact]
    public void RejectsEmptyFile() =>
        Assert.Throws<Lean4ExportFormatException>(() => new Lean4ExportReader(new MemoryStream()));

    [Fact]
    public void RejectsUnsupportedVersion()
    {
        var ex = Fails(Meta31.Replace("3.1.0", "4.0.0", StringComparison.Ordinal));
        Assert.Equal(1, ex.LineNumber);
        Assert.Contains("unsupported export format version '4.0.0'", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RejectsUndefinedReference()
    {
        var ex = Fails(Meta31, """{"ie":0,"sort":5}""");
        Assert.Equal(2, ex.LineNumber);
        Assert.Contains("undefined level index 5", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RejectsForwardReference()
    {
        var ex = Fails(Meta31, """{"app":{"arg":1,"fn":1},"ie":0}""", """{"ie":1,"sort":0}""");
        Assert.Equal(2, ex.LineNumber);
        Assert.Contains("undefined expression index 1", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RejectsRedefinedIndex()
    {
        var ex = Fails(Meta31, """{"ie":0,"sort":0}""", """{"ie":0,"sort":0}""");
        Assert.Equal(3, ex.LineNumber);
        Assert.Contains("defined more than once", ex.Message, StringComparison.Ordinal);
        Assert.Contains("defined more than once", Fails(Meta31, """{"in":0,"str":{"pre":0,"str":"A"}}""").Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RejectsUnknownAndMissingFields()
    {
        Assert.Contains("unexpected field 'extra'", Fails(Meta31, """{"ie":0,"sort":0}""", """{"ie":1,"app":{"fn":0,"arg":0,"extra":1}}""").Message, StringComparison.Ordinal);
        Assert.Contains("missing field 'arg'", Fails(Meta31, """{"ie":0,"sort":0}""", """{"ie":1,"app":{"fn":0}}""").Message, StringComparison.Ordinal);
        Assert.Contains("unexpected key", Fails(Meta31, """{"ie":0,"sort":0,"bvar":1}""").Message, StringComparison.Ordinal);
        Assert.Contains("unknown expression kind 'mvar'", Fails(Meta31, """{"ie":0,"mvar":0}""").Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RejectsMalformedJsonWithLineNumber()
    {
        var ex = Fails(Meta31, """{"in":1,"str":{"pre":0,"str":"A"}}""", """{"ie":0,"sort":""");
        Assert.Equal(3, ex.LineNumber);
        Assert.Contains("invalid JSON", ex.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RejectsInvalidValues()
    {
        Assert.Contains("non-negative", Fails(Meta31, """{"ie":0,"bvar":-1}""").Message, StringComparison.Ordinal);
        Assert.Contains("invalid natural-number literal", Fails(Meta31, """{"ie":0,"natVal":"-3"}""").Message, StringComparison.Ordinal);
        Assert.Contains("invalid natural-number literal", Fails(Meta31, """{"ie":0,"natVal":"1e3"}""").Message, StringComparison.Ordinal);
        Assert.Contains("unknown binder info", Fails(Meta31, """{"ie":0,"sort":0}""", """{"ie":1,"lam":{"binderInfo":"weird","body":0,"name":0,"type":0}}""").Message, StringComparison.Ordinal);
    }

    [Fact]
    public void KeysAreCheckedAgainstTheDeclaredFormatVersion()
    {
        // 3.0.0 spellings are rejected in a 3.1.0 file and vice versa.
        Assert.Contains("unknown declaration kind 'axiomInfo'",
            Fails(Meta31, """{"ie":0,"sort":0}""", """{"axiomInfo":{"isUnsafe":false,"levelParams":[],"name":0,"type":0}}""").Message, StringComparison.Ordinal);
        Assert.Contains("unknown declaration kind 'axiom'",
            Fails(Meta30, """{"ie":0,"sort":0}""", """{"axiom":{"isUnsafe":false,"levelParams":[],"name":0,"type":0}}""").Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Format300MutualArraysSplitIntoDefinitionsAndOpaques()
    {
        var decls = ReadAll(Meta30,
            """{"in":1,"str":{"pre":0,"str":"f"}}""", """{"in":2,"str":{"pre":0,"str":"g"}}""", """{"ie":0,"sort":0}""",
            """{"def":[{"all":[1,2],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":0,"value":0},{"all":[1,2],"isUnsafe":true,"levelParams":[],"name":2,"type":0,"value":0}]}""");
        Assert.Equal(2, decls.Count);
        var f = Assert.IsType<DefinitionInfo>(((ConstantDeclaration)decls[0]).Constant);
        var g = Assert.IsType<OpaqueInfo>(((ConstantDeclaration)decls[1]).Constant);
        Assert.Equal([Name.Parse("f"), Name.Parse("g")], f.All);
        Assert.True(g.IsUnsafe);
    }
}
