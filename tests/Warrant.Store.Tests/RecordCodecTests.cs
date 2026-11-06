using System.Numerics;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Store.Tests;

/// <summary>A record holds one declaration exactly (M5b U11, KTD17), and a malformed one is an error, never a different declaration.</summary>
public sealed class RecordCodecTests
{
    [Fact]
    public void EveryDeclarationOfTheSemanticsBundleRoundTripsToAnEqualDeclaration()
    {
        Assert.NotEmpty(Stores.Bundle);
        foreach (var declaration in Stores.Bundle)
        {
            var record = RecordCodec.Encode(declaration);
            var decoded = RecordCodec.Decode(record);

            Assert.Equal(declaration.GetType(), decoded.GetType());
            Assert.Equal(declaration.Constants.Count, decoded.Constants.Count);
            foreach (var (original, read) in declaration.Constants.Zip(decoded.Constants))
            {
                Assert.True(ExportChecker.ConstantsMatch(original, read), $"{original.Name} does not match after the round trip");
                // Binder names and annotations too: the record keeps the declaration exactly.
                Assert.Equal(original, read);
            }
            Assert.Equal(record, RecordCodec.Encode(decoded));
        }
    }

    [Fact]
    public void RareShapesRoundTrip()
    {
        var name = Name.Num(Name.Str(Name.Str(Name.Anonymous, "ünï"), ""), 18_446_744_073_709_551_615UL);
        var big = BigInteger.Pow(2, 200) + 7;
        var value = Expr.MData(
            new KVMap(EquatableArray.Create(new KVMapEntry("key", "value"), new KVMapEntry("", "∀"))),
            Expr.Let(Name.From("x"), Expr.Const(Name.From("Nat")), Expr.NatLit(big),
                Expr.Proj(Name.From("Prod"), 1, Expr.App(Expr.BVar(0), Expr.StrLit("a\0b\n"))), nonDependent: true));
        var levels = Level.IMax(Level.Max(Level.Param(Name.From("u")), Level.Succ(Level.Zero)), Level.Param(Name.From("v")));
        var definition = new DefinitionInfo(name, EquatableArray.Create(Name.From("u"), Name.From("v")),
            Expr.Forall(Name.From("α"), Expr.Sort(levels), Expr.BVar(0), BinderInfo.StrictImplicit),
            value, ReducibilityHints.Regular(uint.MaxValue), DefinitionSafety.Partial, EquatableArray.Create(name));
        var declaration = new ConstantDeclaration(definition);

        Assert.Equal(declaration, RecordCodec.Decode(RecordCodec.Encode(declaration)));
    }

    [Fact]
    public void FreeVariablesAndMetavariablesCannotBeStored()
    {
        var withFVar = new ConstantDeclaration(new AxiomInfo(Name.From("a"), EquatableArray<Name>.Empty, Expr.FVar(new FVarId(Name.From("x"))), false));
        var withMVar = new ConstantDeclaration(new AxiomInfo(Name.From("b"), EquatableArray<Name>.Empty, Expr.MVar(new MVarId(Name.From("m"))), false));

        Assert.Throws<ArgumentException>(() => RecordCodec.Encode(withFVar));
        Assert.Throws<ArgumentException>(() => RecordCodec.Encode(withMVar));
    }

    [Fact]
    public void EveryTruncationOfARecordAndTrailingBytesAreRejected()
    {
        // The largest records of the bundle, cut at every length.
        foreach (var declaration in Stores.Bundle.OrderByDescending(d => RecordCodec.Encode(d).Length).Take(3).Append(Stores.Bundle[0]))
        {
            var record = RecordCodec.Encode(declaration);
            for (int length = 0; length < record.Length; length += Math.Max(1, record.Length / 500))
            {
                var error = Assert.Throws<StoreFormatException>(() => RecordCodec.Decode(record.AsSpan(0, length), path: "decls.bin", offset: 40));
                Assert.StartsWith("decls.bin: the record at byte 40 is malformed", error.Message, StringComparison.Ordinal);
            }
            Assert.Throws<StoreFormatException>(() => RecordCodec.Decode([.. record, 0]));
        }
    }

    [Fact]
    public void ForwardAndOutOfRangeReferencesAreRejected()
    {
        // One constant record, no names, no levels, one expression that applies itself: a forward reference.
        byte[] selfApplication = [0, 0, 0, 1, (byte)ExprKind.App, 0, 0];
        var error = Assert.Throws<StoreFormatException>(() => RecordCodec.Decode(selfApplication));
        Assert.Contains("expression index 0 is not below 0", error.Message, StringComparison.Ordinal);

        // An axiom whose type names expression 5 of a table of one.
        byte[] outOfRange = [0, 0, 0, 1, (byte)ExprKind.BVar, 0, (byte)ConstantKind.Axiom, 0, 0, 5, 0];
        error = Assert.Throws<StoreFormatException>(() => RecordCodec.Decode(outOfRange));
        Assert.Contains("expression index 5 is not below 1", error.Message, StringComparison.Ordinal);

        // A boolean that is neither 0 nor 1.
        byte[] badBool = [0, 0, 0, 1, (byte)ExprKind.BVar, 0, (byte)ConstantKind.Axiom, 0, 0, 0, 2];
        error = Assert.Throws<StoreFormatException>(() => RecordCodec.Decode(badBool));
        Assert.Contains("2 is not a boolean", error.Message, StringComparison.Ordinal);
    }
}
