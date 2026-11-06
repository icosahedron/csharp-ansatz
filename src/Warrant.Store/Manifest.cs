using System.Text.Json;
using System.Text.Json.Serialization;

namespace Warrant.Store;

/// <summary>One file a store was imported from.</summary>
/// <param name="File">The file's name (without its directory).</param>
/// <param name="Sha256">The SHA-256 of the file as it is on disk, compressed or not: for the semantics bundle, the value its attribute sidecar names.</param>
public sealed record ManifestSource(string File, string Sha256);

/// <summary>
/// A store version's <c>manifest.json</c> (KTD17, docs/m5b/05): what it was imported from, how, and what it holds. It is
/// written once with the version and never changes. Nothing trusts <see cref="VerifiedBy"/> automatically:
/// <c>check-store</c> re-checks a store whatever its manifest says.
/// </summary>
/// <param name="Format">The store format (<see cref="StoreFormat.Version"/>).</param>
/// <param name="Lean">The Lean version the sources were exported from.</param>
/// <param name="Lean4Export">The lean4export format version of the sources.</param>
/// <param name="Sources">The files, in import order.</param>
/// <param name="Mode"><c>trusted</c> (declarations stored as read) or <c>verified</c> (as the kernel admitted them).</param>
/// <param name="VerifiedBy">In verified mode, the toolchain identity that checked the declarations; else null.</param>
/// <param name="QuotientsInitialized">Whether the store holds the four quotient constants.</param>
/// <param name="Declarations">The number of records.</param>
/// <param name="Constants">The number of constants, which the index maps by name.</param>
public sealed record Manifest(
    int Format,
    string Lean,
    [property: JsonPropertyName("lean4export")] string Lean4Export,
    IReadOnlyList<ManifestSource> Sources,
    string Mode,
    string? VerifiedBy,
    bool QuotientsInitialized,
    int Declarations,
    int Constants)
{
    /// <summary>The trusted import mode.</summary>
    public const string Trusted = "trusted";

    /// <summary>The verified import mode.</summary>
    public const string Verified = "verified";

    private static readonly JsonSerializerOptions Options = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
        WriteIndented = true,
        DefaultIgnoreCondition = JsonIgnoreCondition.WhenWritingNull,
    };

    /// <summary>The manifest as the bytes of its file: UTF-8 JSON with a final newline, the same for the same manifest.</summary>
    public byte[] ToBytes()
    {
        var json = JsonSerializer.SerializeToUtf8Bytes(this, Options);
        return [.. json, (byte)'\n'];
    }

    /// <summary>Reads a manifest file.</summary>
    /// <exception cref="StoreFormatException">The file is not a manifest of this format.</exception>
    public static Manifest Read(string path)
    {
        Manifest? manifest;
        try
        {
            using var stream = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.Read | FileShare.Delete);
            manifest = JsonSerializer.Deserialize<Manifest>(stream, Options);
        }
        catch (JsonException ex)
        {
            throw new StoreFormatException(path, $"not a store manifest: {ex.Message}");
        }
        if (manifest is null || manifest.Sources is null || manifest.Mode is not (Trusted or Verified) || manifest.Lean is null || manifest.Lean4Export is null)
        {
            throw new StoreFormatException(path, "not a store manifest");
        }
        if (manifest.Format != StoreFormat.Version)
        {
            throw new StoreFormatException(path, manifest.Format > StoreFormat.Version
                ? $"format version {manifest.Format} is newer than this Warrant reads ({StoreFormat.Version})"
                : $"format version {manifest.Format} is not one this Warrant reads ({StoreFormat.Version})");
        }
        return manifest;
    }
}
