using System.Buffers.Binary;
using Warrant.Cic;

namespace Warrant.Store.Tests;

/// <summary>
/// The store's files (M5b U11, KTD17): versions that are written once and replaced whole, readers that keep the version
/// they opened, and a header check that rejects any file this Warrant does not read before reading a record of it.
/// </summary>
public sealed class StoreTests : IDisposable
{
    private readonly TempDirectory _temp = new();

    public void Dispose() => _temp.Dispose();

    [Fact]
    public void EveryConstantWrittenIsFoundByNameAndReadBackAndOthersAreNot()
    {
        var store = _temp.Sub("s");
        var version = Stores.Write(store, Stores.Bundle);

        using var reader = StoreReader.Open(store);
        Assert.Equal(version, reader.Version);
        Assert.Equal(Stores.Bundle.Sum(d => d.Constants.Count), reader.ConstantCount);
        Assert.Equal(Stores.Bundle.Count, reader.Manifest.Declarations);
        Assert.True(reader.Manifest.QuotientsInitialized);
        foreach (var declaration in Stores.Bundle)
        {
            foreach (var constant in declaration.Constants)
            {
                Assert.True(reader.TryFind(constant.Name, out var kind, out var location), $"{constant.Name} is not in the index");
                Assert.Equal(constant.Kind, kind);
                Assert.Equal(declaration, reader.Read(location));
            }
        }
        Assert.Equal(Stores.Bundle, reader.ReadAll());
        Assert.False(reader.TryFind(Name.From("No", "such", "constant"), out _, out _));
        Assert.False(reader.TryFind(Name.Anonymous, out _, out _));
        Assert.False(reader.TryFind(Name.Num(Name.From("Nat"), 0), out _, out _));
    }

    [Fact]
    public void WritingTheSameInputTwiceMakesByteIdenticalVersions()
    {
        var first = Stores.Write(_temp.Sub("a"), Stores.Bundle);
        var second = Stores.Write(_temp.Sub("b"), Stores.Bundle);

        Assert.Equal(first, second);
        foreach (var file in new[] { "manifest.json", "names.idx", "decls.bin" })
        {
            Assert.Equal(File.ReadAllBytes(Path.Combine(_temp.Sub("a"), first, file)), File.ReadAllBytes(Path.Combine(_temp.Sub("b"), second, file)));
        }

        // Into the same store again: the version, which readers may hold, stays as it was.
        using var reader = StoreReader.Open(_temp.Sub("a"));
        Assert.Equal(first, Stores.Write(_temp.Sub("a"), Stores.Bundle));
        Assert.Single(Directory.GetDirectories(_temp.Sub("a")));
        Assert.True(reader.TryFind(Name.From("Nat"), out _, out var nat));
        Assert.IsType<InductiveDeclaration>(reader.Read(nat));
    }

    [Fact]
    public void AReaderKeepsItsVersionWhileAnotherIsWrittenAndTheOldOneCanBeDeletedOnceItIsClosed()
    {
        var store = _temp.Sub("s");
        var half = Stores.Bundle.Take(Stores.Bundle.Count / 2).ToList();
        var v1 = Stores.Write(store, half);
        var reader = StoreReader.Open(store);
        var later = Stores.Bundle[^1].Constants[0].Name;
        Assert.False(reader.TryFind(later, out _, out _));

        var v2 = Stores.Write(store, Stores.Bundle);

        Assert.NotEqual(v1, v2);
        Assert.Equal(v2 + "\n", File.ReadAllText(Path.Combine(store, "current")));
        using (var fresh = StoreReader.Open(store))
        {
            Assert.Equal(v2, fresh.Version);
            Assert.True(fresh.TryFind(later, out _, out _));
        }
        // The first reader still reads version 1, whole.
        Assert.Equal(v1, reader.Version);
        Assert.False(reader.TryFind(later, out _, out _));
        Assert.Equal(half, reader.ReadAll());
        reader.Dispose();

        // The import deleted version 1 if it could (Unix); otherwise it can be deleted now that nobody holds it.
        var old = Path.Combine(store, v1);
        if (Directory.Exists(old))
        {
            Directory.Delete(old, recursive: true);
        }
        Assert.Equal([v2], Directory.GetDirectories(store).Select(Path.GetFileName));
    }

    [Fact]
    public void ASecondWriterFailsWhileTheFirstHoldsTheStoreAndAnUncommittedOneChangesNothing()
    {
        var store = _temp.Sub("s");
        var v1 = Stores.Write(store, Stores.Bundle.Take(10));
        using (var writer = StoreWriter.Create(store))
        {
            var error = Assert.Throws<IOException>(() => StoreWriter.Create(store));
            Assert.Contains("another import is writing this store", error.Message, StringComparison.Ordinal);
            foreach (var d in Stores.Bundle)
            {
                writer.Add(d);
            }
            Assert.Throws<InvalidOperationException>(() => writer.Add(Stores.Bundle[0]));
        }

        using var reader = StoreReader.Open(store);
        Assert.Equal(v1, reader.Version);
        Assert.Equal([v1], Directory.GetDirectories(store).Select(Path.GetFileName));
    }

    [Theory]
    [InlineData("decls.bin", "truncated")]
    [InlineData("decls.bin", "magic")]
    [InlineData("decls.bin", "newer")]
    [InlineData("names.idx", "truncated")]
    [InlineData("names.idx", "magic")]
    [InlineData("names.idx", "newer")]
    public void AFileThisWarrantDoesNotReadIsRejectedNamingTheFile(string file, string damage)
    {
        var store = _temp.Sub("s");
        var version = Stores.Write(store, Stores.Bundle);
        var path = Path.Combine(store, version, file);
        var bytes = File.ReadAllBytes(path);
        switch (damage)
        {
            case "truncated":
                bytes = bytes[..^7];
                break;
            case "magic":
                bytes[0] = (byte)'X';
                break;
            default:
                BinaryPrimitives.WriteInt32LittleEndian(bytes.AsSpan(4), 2);
                break;
        }
        File.WriteAllBytes(path, bytes);

        var error = Assert.Throws<StoreFormatException>(() => StoreReader.Open(store));

        Assert.Equal(path, error.FilePath);
        Assert.StartsWith(path + ": ", error.Message, StringComparison.Ordinal);
        Assert.Contains(damage switch
        {
            "truncated" => "it is truncated",
            "magic" => "wrong magic number",
            _ => "format version 2 is newer than this Warrant reads (1)",
        }, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ANewerManifestAndABadCurrentAreRejected()
    {
        var store = _temp.Sub("s");
        var version = Stores.Write(store, Stores.Bundle.Take(5));
        var manifest = Path.Combine(store, version, "manifest.json");
        File.WriteAllText(manifest, File.ReadAllText(manifest).Replace("\"format\": 1", "\"format\": 2", StringComparison.Ordinal));
        Assert.Contains("format version 2 is newer", Assert.Throws<StoreFormatException>(() => StoreReader.Open(store)).Message, StringComparison.Ordinal);

        File.WriteAllText(Path.Combine(store, "current"), "../elsewhere\n");
        Assert.Contains("'../elsewhere' is not a store version", Assert.Throws<StoreFormatException>(() => StoreReader.Open(store)).Message, StringComparison.Ordinal);

        Assert.Contains("is not a Warrant store", Assert.Throws<IOException>(() => StoreReader.Open(_temp.Sub("empty"))).Message, StringComparison.Ordinal);
    }

    [Fact]
    public void TheManifestRecordsWhatTheStoreHolds()
    {
        var store = _temp.Sub("s");
        var version = Stores.Write(store, Stores.Bundle, Manifest.Verified);

        var text = File.ReadAllText(Path.Combine(store, version, "manifest.json"));
        var manifest = Manifest.Read(Path.Combine(store, version, "manifest.json"));

        Assert.Equal(1, manifest.Format);
        Assert.Equal("4.35.0", manifest.Lean);
        Assert.Equal("3.1.0", manifest.Lean4Export);
        Assert.Equal("verified", manifest.Mode);
        Assert.Equal("test", manifest.VerifiedBy);
        Assert.True(manifest.QuotientsInitialized);
        Assert.Equal(Stores.Bundle.Count, manifest.Declarations);
        Assert.Equal("bundle.ndjson.gz", Assert.Single(manifest.Sources).File);
        Assert.StartsWith("{\n  \"format\": 1,\n  \"lean\": \"4.35.0\",", text.ReplaceLineEndings("\n"), StringComparison.Ordinal);
    }
}
