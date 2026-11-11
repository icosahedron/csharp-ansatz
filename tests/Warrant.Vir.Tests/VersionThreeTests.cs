using System.Numerics;
using System.Text;

namespace Warrant.Vir.Tests;

/// <summary>VIR version 3 (plan M6 U6, KTD19): the new forms' encoding, exact decimal literals, the version check and contract deps.</summary>
public class VersionThreeTests
{
    private static string J(string text) => text.Replace('`', '"');

    [Fact]
    public void TheNewFormsHaveTheDocumentedShape()
    {
        var json = VirWriter.WriteString(Samples.Effectful());

        // dependencies follow params, and their member keys are in deps although the unit was given only the record's key.
        Assert.Contains(
            J("""`params`:[{`name`:`x`,`type`:{`nullable`:`int32`}},{`name`:`payment`,`type`:{`nullable`:{`ref`:`T:Payouts.Payment`}}}],"""
                + """`dependencies`:[{`name`:`store`,`interface`:`T:Payments.IStore`,`members`:[`M:Payments.IStore.Get(System.Int32)`,`M:Payments.IStore.Save(System.Decimal)`]}],"""
                + """`returns`:{`task`:`int32`},"""),
            json,
            StringComparison.Ordinal);
        Assert.EndsWith(
            J("""`deps`:[`M:Payments.IStore.Get(System.Int32)`,`M:Payments.IStore.Save(System.Decimal)`,`T:Payouts.Payment`]}"""),
            json,
            StringComparison.Ordinal);
        Assert.Contains(J("""{`decimal`:{`type`:`decimal`,`negative`:`false`,`mantissa`:`1`,`scale`:`28`}}"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`decimal`:{`type`:`decimal`,`negative`:`true`,`mantissa`:`150`,`scale`:`2`}}"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`coalesce`:{`type`:`int32`,`l`:{`param`:{`type`:{`nullable`:`int32`},`index`:0}},`r`:{`throw`:{`type`:`int32`,`exception`:`T:System.ArgumentNullException`}}}}"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`unwrap`:{`type`:`int32`,`kind`:`value`,`operand`:"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`unwrap`:{`type`:{`ref`:`T:Payouts.Payment`},`kind`:`non-null`,`operand`:"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`eval`:{`await`:{`type`:`unit`,`operand`:{`external`:{`type`:{`task`:`unit`},`dependency`:0,`member`:`M:Payments.IStore.Save(System.Decimal)`,`args`:[{`local`:{`type`:`decimal`,`id`:2}}]}}}}}"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`requires`:{`not`:{`type`:`bool`,`operand`:{`isnull`:{`type`:`bool`,`operand`:"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`ensures`:{`local`:5,`name`:`r`,`c`:{`compare`:"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`assert`:{`c`:{`lit`:{`type`:`bool`,`value`:`true`}},`script`:[]}}"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`binary`:{`type`:`int32`,`op`:`rem`,`overflow`:`checked`,"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`throw`:{`exception`:`T:System.InvalidOperationException`}}"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`return`:{`modelled`:{`type`:`int32`,`member`:`M:System.Math.Max(System.Int32,System.Int32)`,`args`:["""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`null`:{`type`:{`nullable`:{`ref`:`T:Payouts.Payment`}}}}"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`kind`:`external-contract`,`subject`:`M:Payments.IStore.Get(System.Int32)`},{`kind`:`callee-contract`,"""), json, StringComparison.Ordinal);
        Assert.Contains(J("""{`kind`:`may-throw`,`subject`:`T:System.InvalidOperationException`},{`kind`:`caller-precondition`,"""), json, StringComparison.Ordinal);

        Assert.StartsWith(J("""{`vir`:3,`key`:`M:Payments.IStore.Save(System.Decimal)`,`kind`:`contract`,`params`:[{`name`:`amount`,`type`:`decimal`}],`returns`:{`task`:`unit`},`body`:{`block`:[{`ensures`:{`c`:"""), VirWriter.WriteString(Samples.SaveContract()), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("0.0000000000000000000000000001")]
    [InlineData("7.9228162514264337593543950335")]
    [InlineData("-79228162514264337593543950335")]
    [InlineData("1.0")]
    [InlineData("1.00")]
    [InlineData("-0.00")]
    public void ADecimalLiteralRoundTripsExactly(string text)
    {
        var value = decimal.Parse(text, System.Globalization.CultureInfo.InvariantCulture);
        var literal = DecimalLitExpr.Of(value);
        var unit = Samples.Payout() with { Body = literal };

        var read = (DecimalLitExpr)VirReader.Read(VirWriter.Write(unit)).Body!;

        Assert.Equal(literal, read);
        // decimal's == ignores scale and the sign of zero; the bits do not.
        Assert.Equal(decimal.GetBits(value), decimal.GetBits(read.ToDecimal()));
    }

    [Fact]
    public void EqualDecimalsWithDifferentScalesAreDifferentLiterals()
    {
        Assert.NotEqual(DecimalLitExpr.Of(1.0m), DecimalLitExpr.Of(1.00m));
        Assert.Equal(new DecimalLitExpr(false, 100, 2), DecimalLitExpr.Of(1.00m));
        Assert.Equal(28, DecimalLitExpr.Of(Samples.Tiny).Scale);
        Assert.True(DecimalLitExpr.Of(-0.00m).Negative);
    }

    [Theory]
    [InlineData(false, "79228162514264337593543950336", 0)]
    [InlineData(false, "1", 29)]
    [InlineData(false, "-1", 0)]
    public void AnOutOfRangeDecimalIsNeitherWrittenNorRead(bool negative, string mantissa, int scale)
    {
        var literal = new DecimalLitExpr(negative, BigInteger.Parse(mantissa, System.Globalization.CultureInfo.InvariantCulture), scale);
        var unit = Samples.Payout() with { Body = literal };
        Assert.Throws<ArgumentException>(() => VirWriter.Write(unit));

        var valid = VirWriter.WriteString(Samples.Payout() with { Body = new DecimalLitExpr(false, 1, 0) });
        var forged = valid.Replace(J("`mantissa`:`1`,`scale`:`0`"), J($"`mantissa`:`{mantissa}`,`scale`:`{scale}`"), StringComparison.Ordinal);
        Assert.NotEqual(valid, forged);
        Assert.Throws<FormatException>(() => VirReader.Read(Encoding.UTF8.GetBytes(forged)));
    }

    [Fact]
    public void AnEnsuresBindsALocalAndANameOrNeither()
    {
        var unit = Samples.SaveContract() with { Body = new BlockStmt(VirList.Of<VirStmt>(new EnsuresStmt(0, null, LitExpr.Bool(true)))) };
        Assert.Throws<ArgumentException>(() => VirWriter.Write(unit));

        var forged = VirWriter.WriteString(Samples.SaveContract()).Replace(J("{`ensures`:{`c`:"), J("{`ensures`:{`local`:0,`c`:"), StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => VirReader.Read(Encoding.UTF8.GetBytes(forged)));
    }

    [Fact]
    public void AVersionFourUnitIsRejectedNamingTheVersion()
    {
        var bytes = VirWriter.Write(Samples.Payout() with { Vir = 4 });

        var e = Assert.Throws<FormatException>(() => VirReader.Read(bytes));

        Assert.Equal("VIR version 4 is newer than this reader's version 3.", e.Message);
        Assert.Equal(3, VirReader.Read(VirWriter.Write(Samples.Payout())).Vir);
        Assert.Equal(2, VirReader.Read(VirWriter.Write(Samples.Payout() with { Vir = 2 })).Vir);
    }

    [Fact]
    public void ADependencysMembersAreAlwaysAmongTheDeps()
    {
        var unit = Samples.Effectful();
        Assert.Contains(Samples.GetKey, unit.Deps);
        Assert.Contains(Samples.SaveKey, unit.Deps);

        // Replacing the deps keeps the members; adding a dependency adds its members.
        Assert.Contains(Samples.GetKey, (unit with { Deps = VirList<string>.Empty }).Deps);
        var other = Samples.Payout() with { Dependencies = VirList.Of(new VirDependency("clock", "T:IClock", VirList.Of("M:IClock.Now"))) };
        Assert.Equal(["M:IClock.Now"], other.Deps);
        Assert.Equal(other, VirReader.Read(VirWriter.Write(other)));
    }

    [Fact]
    public void ChangingAContractsEnsuresChangesTheClosureHashOfItsUsersAndTheirCallers()
    {
        var caller = VirUnit.Function(
            "M:Payments.Service.Run",
            VirList<VirParam>.Empty,
            VirType.Task(VirType.Int32),
            new CallExpr(VirType.Task(VirType.Int32), Samples.ProcessKey, VirList.Of<VirExpr>(new NullExpr(VirType.Nullable(VirType.Int32)), new NullExpr(VirType.Nullable(VirType.Ref(Samples.PaymentKey))))),
            VirList<VirAssumption>.Empty,
            Samples.Facts,
            VirList.Of(Samples.ProcessKey));
        VirUnit[] Set(int floor) => [Samples.GetContract(floor), Samples.SaveContract(), Samples.Effectful(), Samples.RecordType(), Samples.EnumType(), caller];

        var before = VirHash.Closures(Set(0));
        var after = VirHash.Closures(Set(1));

        Assert.NotEqual(VirHash.OfUnit(Samples.GetContract(0)), VirHash.OfUnit(Samples.GetContract(1)));
        Assert.Equal(VirHash.OfUnit(Samples.Effectful()), VirHash.OfUnit(Samples.Effectful()));
        Assert.NotEqual(before[Samples.ProcessKey], after[Samples.ProcessKey]);
        Assert.NotEqual(before["M:Payments.Service.Run"], after["M:Payments.Service.Run"]);
        Assert.Equal(before[Samples.SaveKey], after[Samples.SaveKey]);
    }
}
