using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Lean4Export;

namespace Warrant.Engine.Service.Cache;

/// <summary>How an entry's budgets decide whether it applies to a run (M5b KTD13).</summary>
public enum BudgetMatch
{
    /// <summary>
    /// The outcome depends on the budgets (false with read-back values, not proved, out of fuel): the entry applies only
    /// when every budget is the one it ran with.
    /// </summary>
    Exact,

    /// <summary>
    /// A proof: the entry applies when every budget is at least what the proof needed, so a project that lowers its
    /// budgets below that sees the failure a cold build would.
    /// </summary>
    AtLeast,
}

/// <summary>
/// One result cache entry (M5b KTD14, docs/m5b/04): an outcome under the key of the inputs it was computed from, with the
/// budgets it holds under and the unit's certificate. Entries are immutable and named by key.
/// </summary>
/// <param name="Format">The entry format, <see cref="FormatVersion"/>.</param>
/// <param name="Toolchain">The toolchain identity that wrote it (<see cref="Service.Toolchain.Identity"/>).</param>
/// <param name="Key">The key, which names the entry's file.</param>
/// <param name="Inputs">The key's inputs.</param>
/// <param name="Match">How <see cref="Budgets"/> decide whether the entry applies.</param>
/// <param name="Budgets">
/// With <see cref="BudgetMatch.Exact"/>, the unit's effective budgets; with <see cref="BudgetMatch.AtLeast"/>, what its
/// proof needed: the kernel fuel and numeral size limit it ran with, the tactic fuel it used and the time it took.
/// </param>
/// <param name="Outcome">The outcome, with positions as VIR node IDs and the unit's assumptions.</param>
/// <param name="Certificate">The lean4export NDJSON of the declarations the unit admitted (<see cref="Certificates"/>); empty for none.</param>
public sealed record CacheEntry(
    int Format, string Toolchain, string Key, CacheKeyInputs Inputs, BudgetMatch Match, VerifyBudgets Budgets, OutcomeDto Outcome, string Certificate)
{
    /// <summary>The entry format this code writes and reads; a change invalidates every entry.</summary>
    public const int FormatVersion = 1;

    /// <summary>Whether the entry applies to a run of its unit with the given effective budgets.</summary>
    /// <param name="budgets">The unit's effective budgets now.</param>
    /// <returns>True when the cached outcome is the one a run with those budgets would give.</returns>
    public bool Admits(VerifyBudgets budgets)
    {
        ArgumentNullException.ThrowIfNull(budgets);
        return Match switch
        {
            BudgetMatch.Exact => budgets == Budgets,
            BudgetMatch.AtLeast => budgets.KernelFuel >= Budgets.KernelFuel
                && budgets.KernelMaxNatBytes >= Budgets.KernelMaxNatBytes
                && budgets.TacticFuel >= Budgets.TacticFuel
                && budgets.Timeout >= Budgets.Timeout,
            _ => false,
        };
    }

    /// <summary>The certificate's declarations, as the kernel admitted them.</summary>
    /// <returns>The declarations, in admission order.</returns>
    /// <exception cref="FormatException">The certificate is malformed or holds a declaration a cached unit never admits.</exception>
    public ImmutableArray<KernelDeclaration> Declarations()
    {
        if (Certificate.Length == 0)
        {
            return [];
        }
        try
        {
            using var stream = new MemoryStream(Encoding.UTF8.GetBytes(Certificate));
            return [.. Certificates.Read(stream).Select(Kernel)];
        }
        catch (Lean4ExportFormatException ex)
        {
            throw new FormatException($"The certificate of entry {Key} is malformed: {ex.Message}", ex);
        }

        static KernelDeclaration Kernel(Declaration declaration) => declaration switch
        {
            ConstantDeclaration { Constant: TheoremInfo theorem } => new TheoremDecl(theorem),
            ConstantDeclaration { Constant: DefinitionInfo definition } => new DefinitionDecl(definition),
            _ => throw new FormatException($"A certificate holds a {declaration.GetType().Name}, which no cached unit admits."),
        };
    }

    /// <summary>
    /// The entry's file: <c>{"sha256":"…","body":{…}}</c>, where the hash is the SHA-256 of the body's UTF-8 text exactly
    /// as it stands in the file.
    /// </summary>
    /// <returns>The file's bytes.</returns>
    public byte[] ToFile()
    {
        var body = JsonSerializer.SerializeToUtf8Bytes(this, CacheJsonContext.Default.CacheEntry);
        var head = Encoding.UTF8.GetBytes($"{{\"sha256\":\"{Convert.ToHexStringLower(SHA256.HashData(body))}\",\"body\":");
        return [.. head, .. body, (byte)'}'];
    }

    /// <summary>
    /// Reads an entry's file and checks it: its hash, its format, the toolchain that wrote it and the key it is under.
    /// </summary>
    /// <param name="bytes">The file's bytes.</param>
    /// <param name="key">The key the file is named by.</param>
    /// <param name="toolchain">This process's toolchain identity.</param>
    /// <returns>The entry.</returns>
    /// <exception cref="FormatException">The file is not a sound entry for this key and toolchain.</exception>
    public static CacheEntry FromFile(byte[] bytes, string key, string toolchain)
    {
        ArgumentNullException.ThrowIfNull(bytes);
        try
        {
            using var document = JsonDocument.Parse(bytes);
            var root = document.RootElement;
            var sha256 = root.GetProperty("sha256").GetString();
            var body = Encoding.UTF8.GetBytes(root.GetProperty("body").GetRawText());
            if (!string.Equals(sha256, Convert.ToHexStringLower(SHA256.HashData(body)), StringComparison.Ordinal))
            {
                throw new FormatException("The entry's body does not match its hash.");
            }
            var entry = JsonSerializer.Deserialize(body, CacheJsonContext.Default.CacheEntry);
            if (entry is null || !HasEveryField(entry))
            {
                throw new FormatException("The entry is missing a field.");
            }
            if (entry.Format != FormatVersion)
            {
                throw new FormatException($"The entry has format {entry.Format}; this toolchain reads {FormatVersion}.");
            }
            if (!string.Equals(entry.Toolchain, toolchain, StringComparison.Ordinal))
            {
                throw new FormatException("The entry was written by another toolchain.");
            }
            if (!string.Equals(entry.Key, key, StringComparison.Ordinal))
            {
                throw new FormatException("The entry is not for the key its file is named by.");
            }
            return entry;
        }
        catch (Exception ex) when (ex is JsonException or InvalidOperationException or KeyNotFoundException or ArgumentException or NotSupportedException)
        {
            throw new FormatException($"The entry is malformed: {ex.Message}", ex);
        }
    }

    /// <summary>
    /// Whether every field the entry is read through is present: JSON null, or an absent array, deserializes to a null
    /// reference or a default array, which a valid hash does not rule out.
    /// </summary>
    private static bool HasEveryField(CacheEntry entry) =>
        entry is
        {
            Toolchain: not null,
            Key: not null,
            Inputs: { Closure: not null, Bundle: not null, Sidecar: not null, Names.IsDefault: false } inputs,
            Budgets: not null,
            Outcome: { Key: not null, DisplayName: not null, Assumptions.IsDefault: false, Counterexample.IsDefault: false, Sides.IsDefault: false } outcome,
            Certificate: not null,
        }
        && inputs.Names.All(n => n is { Key: not null, DisplayName: not null })
        && outcome.Assumptions.All(a => a is { UnitKey: not null, Subject: not null })
        && outcome.Counterexample.All(c => c is { Parameter: not null, Value: not null })
        && outcome.Sides.All(s => s is { Text: not null });
}

/// <summary>The System.Text.Json contract of <see cref="CacheEntry"/>, generated at compile time.</summary>
[JsonSourceGenerationOptions(UseStringEnumConverter = true, PropertyNamingPolicy = JsonKnownNamingPolicy.CamelCase)]
[JsonSerializable(typeof(CacheEntry))]
public sealed partial class CacheJsonContext : JsonSerializerContext;
