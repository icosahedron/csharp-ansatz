using System.Collections.Concurrent;
using System.Diagnostics.CodeAnalysis;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Store;

/// <summary>
/// A store as the kernel's lazy base (KTD18): a constant is decoded the first time the kernel asks for it, with the rest
/// of its record, and remembered; names are shared across records. Thread-safe: concurrent lookups of one record decode
/// it once.
/// </summary>
/// <remarks>
/// The source trusts the store, as <c>ExportChecker(admitRejected: true)</c> trusts an export: what it returns, the kernel
/// believes. <c>warrant check-store</c> is how a store is checked. The one claim the kernel does not take from it is the
/// quotient flag, which <see cref="KernelEnvironment(IConstantSource)"/> checks against the constants it generates itself.
/// </remarks>
public sealed class StoreConstantSource : IConstantSource
{
    private readonly StoreReader _reader;
    private readonly NameInterner _interner;
    private readonly ConcurrentDictionary<Name, ConstantInfo> _constants = new();
    private readonly ConcurrentDictionary<long, Lazy<Declaration>> _records = new();

    /// <summary>Reads constants from <paramref name="reader"/>, which the caller keeps open while the source is used.</summary>
    /// <param name="reader">The store.</param>
    /// <param name="interner">Shares names with other records and sources; null for one of the source's own.</param>
    public StoreConstantSource(StoreReader reader, NameInterner? interner = null)
    {
        _reader = reader ?? throw new ArgumentNullException(nameof(reader));
        _interner = interner ?? new NameInterner();
    }

    /// <inheritdoc/>
    public int Count => _reader.ConstantCount;

    /// <inheritdoc/>
    public bool QuotientsInitialized => _reader.Manifest.QuotientsInitialized;

    /// <summary>The number of records decoded so far.</summary>
    public int MaterializedRecords => _records.Count(r => r.Value.IsValueCreated);

    /// <inheritdoc/>
    /// <exception cref="StoreFormatException">The record that holds the name is malformed or does not hold it.</exception>
    public bool TryGet(Name name, [NotNullWhen(true)] out ConstantInfo? constant)
    {
        ArgumentNullException.ThrowIfNull(name);
        if (_constants.TryGetValue(name, out constant))
        {
            return true;
        }
        if (!_reader.TryFind(name, out var kind, out var location))
        {
            constant = null;
            return false;
        }
        _ = _records.GetOrAdd(location.Offset, _ => new Lazy<Declaration>(() => Materialize(location))).Value;
        if (!_constants.TryGetValue(name, out constant) || constant.Kind != kind)
        {
            throw new StoreFormatException(_reader.VersionDirectory,
                $"the index maps '{name}' ({kind}) to the record at byte {location.Offset}, which does not hold it");
        }
        return true;
    }

    private Declaration Materialize(RecordLocation location)
    {
        var declaration = _reader.Read(location, _interner);
        foreach (var c in declaration.Constants)
        {
            _constants.TryAdd(c.Name, c);
        }
        return declaration;
    }
}
