using System.Text;

namespace Warrant.Vir.Tests;

public class EncodingTests
{
    private const string Tail = """`assumptions`:[],`facts`:{`overflow`:`wrap`,`language`:`14`,`extractor`:`0.1.0`,`roslyn`:`5.0.0`},`deps`:[]}""";

    /// <summary>Expected JSON is written with backticks for quotes, to keep it readable.</summary>
    private static string J(string text) => text.Replace('`', '"');

    [Fact]
    public void PayoutMatchesTheGoldenFile()
    {
        var golden = File.ReadAllBytes(Path.Combine(AppContext.BaseDirectory, "golden", "payout.json"));
        Assert.Equal(Encoding.UTF8.GetString(golden), VirWriter.WriteString(Samples.Payout()));
        Assert.Equal(golden, VirWriter.Write(Samples.Payout()));
    }

    [Fact]
    public void StringsAreEscapedByTheFixedRule()
    {
        // Only '"' and '\' get a backslash; control characters (Unicode Cc) become \u00XX;
        // '+', '<', '>', '&', '\'' and non-ASCII characters are written as themselves, in UTF-8.
        var expected = J(
            """{`vir`:1,`key`:`T:N.R<T>+\`q\`\\`,`kind`:`type`,`definition`:{`record`:[{`name`:`""" +
            "café名" +
            """`,`type`:`int32`},{`name`:`a\u0000b\u0009c\u000Ad\u001Fe\u007Ff\u009Fg>&'h`,`type`:`int32`},{`name`:`""" +
            "😀" +
            """`,`type`:`int32`}]},""" + Tail);

        var bytes = VirWriter.Write(Samples.Escapes());

        Assert.Equal(expected, VirWriter.WriteString(Samples.Escapes()));
        // Non-ASCII is raw UTF-8 (e-acute is C3 A9, U+540D is E5 90 8D, U+1F600 is F0 9F 98 80), with no byte-order mark.
        Assert.Equal(new UTF8Encoding(false).GetBytes(expected), bytes);
        Assert.Equal((byte)'{', bytes[0]);
    }

    [Fact]
    public void SixtyFourBitLiteralsAreDecimalStrings()
    {
        var json = VirWriter.WriteString(Samples.Everything());

        Assert.Contains(J("""{`lit`:{`type`:`int64`,`value`:`-9223372036854775808`}}"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`lit`:{`type`:`int64`,`value`:`9223372036854775807`}}"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`lit`:{`type`:`bool`,`value`:`true`}}"""), json, StringComparison.Ordinal);
    }

    [Fact]
    public void TypeUnitsAndTheoremsHaveTheDocumentedShape()
    {
        Assert.Equal(
            J("""{`vir`:1,`key`:`T:Payouts.Outcome`,`kind`:`type`,`definition`:{`closed`:[{`name`:`Matched`},{`name`:`Missed`}]},""" + Tail),
            VirWriter.WriteString(Samples.ClosedClassType()));
        Assert.Equal(
            J("""{`vir`:1,`key`:`T:Payouts.Status`,`kind`:`type`,`definition`:{`enum`:{`underlying`:`int32`,`members`:[{`name`:`Open`,`value`:`0`},{`name`:`Closed`,`value`:`-1`}]}},""" + Tail),
            VirWriter.WriteString(Samples.EnumType()));
        Assert.Equal(
            J("""{`vir`:1,`key`:`M:Payouts.PayoutRules.CappedAtTheLimit`,`kind`:`theorem`,`params`:[],`statement`:{`compare`:{`type`:`bool`,`op`:`eq`,`kind`:`int`,`l`:{`call`:{`type`:`int32`,`target`:`M:Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)`,`args`:[{`lit`:{`type`:`int32`,`value`:`5000`}},{`lit`:{`type`:`int32`,`value`:`500`}},{`lit`:{`type`:`int32`,`value`:`1000`}}]}},`r`:{`lit`:{`type`:`int32`,`value`:`1000`}}}},`assumptions`:[],`facts`:{`overflow`:`wrap`,`language`:`14`,`extractor`:`0.1.0`,`roslyn`:`5.0.0`},`deps`:[`M:Payouts.PayoutRules.Payout(System.Int32,System.Int32,System.Int32)`]}"""),
            VirWriter.WriteString(Samples.Capped()));
    }

    [Fact]
    public void SelfRefTypesAndDepsHaveTheDocumentedShape()
    {
        var json = VirWriter.WriteString(Samples.Everything());

        Assert.StartsWith(J("""{`vir`:1,`key`:`M:Payouts.Payment.Everything(System.Int32)`,`kind`:`function`,`self`:`T:Payouts.Payment`,`params`:"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`self`:{`type`:{`ref`:`T:Payouts.Payment`}}}"""), json, StringComparison.Ordinal);
        // Deps are sorted ordinally whatever order they were given in.
        Assert.EndsWith(J("""`deps`:[`M:Payouts.Payment.IsLarge`,`T:Payouts.Payment`,`T:Payouts.Status`]}"""), json, StringComparison.Ordinal);
    }
}
