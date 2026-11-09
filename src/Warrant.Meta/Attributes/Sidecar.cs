using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using Warrant.Cic;

namespace Warrant.Meta;

/// <summary>The sidecar's first line: what it was exported from and for.</summary>
/// <param name="Format">The sidecar format version (2: format 1 had no <c>spec</c> entries).</param>
/// <param name="LeanGithash">The githash of the Lean toolchain that exported it.</param>
/// <param name="BundleSha256">The SHA-256 (hex) of the bundle <c>.gz</c> file it describes.</param>
public sealed record SidecarHeader(int Format, string LeanGithash, string BundleSha256);

/// <summary>An entry of Lean's default <c>simp</c> set.</summary>
/// <param name="Name">The lemma.</param>
/// <param name="Priority">Its priority (Lean's default is 1000).</param>
/// <param name="Post">Whether it rewrites after visiting subterms (<c>↓</c> marks a pre lemma).</param>
/// <param name="Inverse">Whether it rewrites right to left (<c>←</c>).</param>
/// <param name="Module">The module that registered the entry.</param>
/// <param name="LeanKeys">Lean's discrimination-tree keys, printed; a test oracle only (KTD9).</param>
public sealed record SimpEntry(Name Name, int Priority, bool Post, bool Inverse, Name Module, ImmutableArray<string> LeanKeys);

/// <summary>A <c>@[congr]</c> lemma.</summary>
/// <param name="Name">The lemma.</param>
/// <param name="Function">The function it is a congruence lemma for.</param>
/// <param name="Priority">Its priority.</param>
/// <param name="Hypotheses">The positions of its congruence hypotheses (Lean's <c>hypothesesPos</c>).</param>
public sealed record CongrEntry(Name Name, Name Function, int Priority, ImmutableArray<int> Hypotheses);

/// <summary>A global instance.</summary>
/// <param name="Name">The instance.</param>
/// <param name="Class">The class it is an instance of (the head of its type's conclusion).</param>
/// <param name="Priority">Its priority (Lean's default is 1000).</param>
/// <param name="Order">Its declaration order; among equal priorities, the higher is the more recent and is tried first.</param>
public sealed record InstanceEntry(Name Name, Name Class, int Priority, int Order);

/// <summary>How a <c>@[spec]</c> lemma states its operation's behaviour (M6 KTD15).</summary>
public enum SpecForm
{
    /// <summary>A Hoare triple <c>⦃P⦄ x ⦃Q⦄</c>, from <c>mvcgen</c>'s spec map.</summary>
    Triple,

    /// <summary>An equation, from <c>mvcgen</c>'s simp set (<c>@[spec]</c> on an equational lemma).</summary>
    Equation,
}

/// <summary>A <c>@[spec]</c> lemma (M6 KTD15): how the VC walker learns what a model operation does.</summary>
/// <param name="Name">The lemma.</param>
/// <param name="Priority">Its priority (Lean's default is 1000).</param>
/// <param name="Form">A triple or an equation.</param>
/// <param name="Module">The module that registered it.</param>
public sealed record SpecEntry(Name Name, int Priority, SpecForm Form, Name Module);

/// <summary>A malformed sidecar, or one made for another bundle.</summary>
public sealed class SidecarFormatException : Exception
{
    /// <summary>Creates the exception for a problem on <paramref name="lineNumber"/> (1-based) of <paramref name="source"/>.</summary>
    public SidecarFormatException(string source, long lineNumber, string message, Exception? innerException = null)
        : base($"{source} line {lineNumber}: {message}", innerException) => LineNumber = lineNumber;

    /// <summary>Creates the exception.</summary>
    public SidecarFormatException()
    {
    }

    /// <summary>Creates the exception with a message.</summary>
    public SidecarFormatException(string message)
        : base(message)
    {
    }

    /// <summary>Creates the exception with a message and inner exception.</summary>
    public SidecarFormatException(string message, Exception innerException)
        : base(message, innerException)
    {
    }

    /// <summary>The 1-based line on which the problem was found (0 if unknown).</summary>
    public long LineNumber { get; }
}

/// <summary>
/// The Lean attributes of the bundle's constants, which lean4export does not carry: simp and congr
/// entries, instances, reducibility statuses, <c>@[defeq]</c> tags, matcher info and class
/// out-parameters (KTD9, docs/m5a/05 "The sidecar"). <c>tools/warrant-attrs/Main.lean</c> exports it
/// and documents each kind's fields.
/// </summary>
/// <remarks>
/// <para>
/// A loaded sidecar is frozen. Like <c>KernelEnvironment.Fork</c>, <see cref="Fork"/> gives an
/// overlay to which the engine adds the statuses and instances of translated declarations (open enums
/// reducible, recursive definitions irreducible, generated instances); the base and other forks never
/// see them.
/// </para>
/// <para>
/// The sidecar can only select which kernel-checked lemmas tactics try, never change what they say;
/// a wrong entry can make a proof fail but not a false claim pass.
/// </para>
/// </remarks>
public sealed class Sidecar
{
    /// <summary>The sidecar format this loader reads.</summary>
    public const int FormatVersion = 2;

    private const int DefaultPriority = 1000;

    private readonly Data _data;
    private readonly Sidecar? _parent;
    private readonly Dictionary<Name, ReducibilityStatus> _statuses = [];
    private readonly Dictionary<Name, List<InstanceEntry>> _instancesByClass = [];
    private readonly HashSet<Name> _instanceNames = [];
    private int _nextOrder;
    private bool _frozen;

    private Sidecar(Data data, Sidecar? parent)
    {
        _data = data;
        _parent = parent;
        _nextOrder = parent?._nextOrder ?? 0;
        Base = parent?.Base ?? this;
    }

    /// <summary>A frozen sidecar with no entries and no header: every constant is semireducible.</summary>
    public static Sidecar Empty { get; } = NewEmpty();

    /// <summary>The header, or <see langword="null"/> for <see cref="Empty"/> and its forks.</summary>
    public SidecarHeader? Header => _data.Header;

    /// <summary>Whether entries can no longer be added.</summary>
    public bool IsFrozen => _frozen;

    /// <summary>
    /// The sidecar this one was forked from, through every fork: the one that was loaded, or this one when it is not a
    /// fork. Forks share its simp, congruence and class entries, so caches built from those key on it (M5b KTD10).
    /// </summary>
    public Sidecar Base { get; }

    /// <summary>The default simp set's entries, in registration order (a lemma Lean split, or registered twice, has several).</summary>
    public IReadOnlyList<SimpEntry> SimpEntries => _data.Simp;

    /// <summary>The <c>@[congr]</c> lemmas, in registration order.</summary>
    public IReadOnlyList<CongrEntry> CongrEntries => _data.Congr;

    /// <summary>The <c>@[spec]</c> lemmas, in registration order: triples first, then equations (M6 KTD15).</summary>
    public IReadOnlyList<SpecEntry> SpecEntries => _data.Spec;

    /// <summary>Every instance, of every class, this sidecar's own last.</summary>
    public IEnumerable<InstanceEntry> Instances =>
        (_parent?.Instances ?? []).Concat(_instancesByClass.Values.SelectMany(l => l).OrderBy(i => i.Order));

    /// <summary>Grows whenever an instance is added, so Meta knows when to rebuild its instance index.</summary>
    internal int InstanceVersion => _nextOrder;

    /// <summary>Every constant whose status is not <see cref="ReducibilityStatus.Semireducible"/>, with its status.</summary>
    public IEnumerable<KeyValuePair<Name, ReducibilityStatus>> ReducibilityStatuses
    {
        get
        {
            var all = new Dictionary<Name, ReducibilityStatus>();
            Collect(this, all);
            return all.Where(kv => kv.Value != ReducibilityStatus.Semireducible);

            static void Collect(Sidecar s, Dictionary<Name, ReducibilityStatus> into)
            {
                if (s._parent is { } p)
                {
                    Collect(p, into);
                }
                foreach (var (name, status) in s._statuses)
                {
                    into[name] = status;
                }
            }
        }
    }

    /// <summary>The constants tagged <c>@[defeq]</c>.</summary>
    public IEnumerable<Name> DefEqNames => _data.DefEq;

    /// <summary>The matchers' info.</summary>
    public IEnumerable<MatcherInfo> Matchers => _data.Matchers.Values;

    /// <summary>The classes, with their out-parameter positions.</summary>
    public IEnumerable<KeyValuePair<Name, ImmutableArray<int>>> Classes => _data.Classes;

    /// <summary>Lean's <c>getReducibilityStatusCore</c>: <see cref="ReducibilityStatus.Semireducible"/> unless an entry says otherwise.</summary>
    public ReducibilityStatus GetReducibilityStatus(Name declName)
    {
        for (var s = this; s is not null; s = s._parent)
        {
            if (s._statuses.TryGetValue(declName, out var status))
            {
                return status;
            }
        }
        return ReducibilityStatus.Semireducible;
    }

    /// <summary>
    /// The instances of <paramref name="className"/> in the order Lean tries them: highest priority
    /// first, and the most recently declared first among equal priorities.
    /// </summary>
    public IReadOnlyList<InstanceEntry> GetInstances(Name className)
    {
        var all = new List<InstanceEntry>();
        for (var s = this; s is not null; s = s._parent)
        {
            if (s._instancesByClass.TryGetValue(className, out var own))
            {
                all.AddRange(own);
            }
        }
        all.Sort((a, b) => a.Priority != b.Priority ? b.Priority.CompareTo(a.Priority) : b.Order.CompareTo(a.Order));
        return all;
    }

    /// <summary>Lean's <c>isInstanceCore</c>: whether <paramref name="declName"/> is a global instance.</summary>
    public bool IsInstance(Name declName)
    {
        for (var s = this; s is not null; s = s._parent)
        {
            if (s._instanceNames.Contains(declName))
            {
                return true;
            }
        }
        return false;
    }

    /// <summary>Whether <paramref name="declName"/> is tagged <c>@[defeq]</c>.</summary>
    public bool HasDefEqAttribute(Name declName) => _data.DefEq.Contains(declName);

    /// <summary>Lean's <c>getMatcherInfo?</c>, or <see langword="null"/> if <paramref name="declName"/> is not a matcher.</summary>
    public MatcherInfo? GetMatcherInfo(Name declName) => _data.Matchers.GetValueOrDefault(declName);

    /// <summary>Lean's <c>isClass</c> on a constant name.</summary>
    public bool IsClass(Name declName) => _data.Classes.ContainsKey(declName);

    /// <summary>Lean's <c>getOutParamPositions?</c>: the class's out-parameter positions, or <see langword="null"/> if it is not a class.</summary>
    public ImmutableArray<int>? GetOutParams(Name className) =>
        _data.Classes.TryGetValue(className, out var positions) ? positions : null;

    /// <summary>Makes this sidecar read-only; permanent and idempotent.</summary>
    public void Freeze() => _frozen = true;

    /// <summary>An empty overlay on this frozen sidecar, to which entries for new declarations can be added.</summary>
    /// <exception cref="InvalidOperationException">This sidecar is not frozen.</exception>
    public Sidecar Fork()
    {
        if (!_frozen)
        {
            throw new InvalidOperationException("Only a frozen sidecar can be forked; call Freeze first.");
        }
        return new(_data, this);
    }

    /// <summary>Lean's <c>setReducibilityStatus</c>: sets the status of <paramref name="declName"/> in this overlay.</summary>
    /// <exception cref="InvalidOperationException">This sidecar is frozen.</exception>
    public void SetReducibilityStatus(Name declName, ReducibilityStatus status)
    {
        ArgumentNullException.ThrowIfNull(declName);
        ThrowIfFrozen();
        _statuses[declName] = status;
    }

    /// <summary>
    /// Lean's <c>addInstance</c>: registers <paramref name="declName"/> as an instance of
    /// <paramref name="className"/>, more recent than every instance already known. Like Lean's, it
    /// does not set the instance's reducibility; Lean's <c>instance</c> command also marks it
    /// <see cref="ReducibilityStatus.InstanceReducible"/>, which is <see cref="SetReducibilityStatus"/>.
    /// </summary>
    /// <exception cref="InvalidOperationException">This sidecar is frozen.</exception>
    public void AddInstance(Name declName, Name className, int priority = DefaultPriority)
    {
        ArgumentNullException.ThrowIfNull(declName);
        ArgumentNullException.ThrowIfNull(className);
        ThrowIfFrozen();
        AddInstanceEntry(new InstanceEntry(declName, className, priority, _nextOrder++));
    }

    /// <summary>Reads a sidecar file (gzip-compressed if its name ends in <c>.gz</c>) and freezes it.</summary>
    /// <param name="path">The file.</param>
    /// <param name="bundleSha256">The SHA-256 (hex) of the bundle file the sidecar must have been made for.</param>
    /// <exception cref="SidecarFormatException">The file is malformed or was made for another bundle.</exception>
    public static Sidecar Load(string path, string bundleSha256)
    {
        ArgumentNullException.ThrowIfNull(path);
        using var file = File.OpenRead(path);
        using var stream = path.EndsWith(".gz", StringComparison.OrdinalIgnoreCase)
            ? new GZipStream(file, CompressionMode.Decompress)
            : (Stream)file;
        return Read(stream, bundleSha256, Path.GetFileName(path));
    }

    /// <summary>Reads an uncompressed sidecar and freezes it.</summary>
    /// <param name="stream">The NDJSON text.</param>
    /// <param name="bundleSha256">The SHA-256 (hex) of the bundle file the sidecar must have been made for.</param>
    /// <param name="source">The name errors give the input.</param>
    /// <exception cref="SidecarFormatException">The input is malformed or was made for another bundle.</exception>
    public static Sidecar Read(Stream stream, string bundleSha256, string source = "sidecar")
    {
        ArgumentNullException.ThrowIfNull(stream);
        ArgumentNullException.ThrowIfNull(bundleSha256);
        ArgumentNullException.ThrowIfNull(source);
        var parser = new Parser(source, bundleSha256);
        using var reader = new StreamReader(stream);
        while (reader.ReadLine() is { } line)
        {
            parser.Line(line);
        }
        return parser.Finish();
    }

    private static Sidecar NewEmpty()
    {
        var s = new Sidecar(new Data(null, [], [], [], [], [], []), null);
        s.Freeze();
        return s;
    }

    private void AddInstanceEntry(InstanceEntry entry)
    {
        if (!_instancesByClass.TryGetValue(entry.Class, out var list))
        {
            _instancesByClass[entry.Class] = list = [];
        }
        list.Add(entry);
        _instanceNames.Add(entry.Name);
        _nextOrder = Math.Max(_nextOrder, entry.Order + 1);
    }

    private void ThrowIfFrozen()
    {
        if (_frozen)
        {
            throw new InvalidOperationException("The sidecar is frozen; add entries to a Fork of it.");
        }
    }

    /// <summary>The entries no overlay changes, shared by a sidecar and its forks.</summary>
    private sealed record Data(
        SidecarHeader? Header,
        ImmutableArray<SimpEntry> Simp,
        ImmutableArray<CongrEntry> Congr,
        ImmutableArray<SpecEntry> Spec,
        HashSet<Name> DefEq,
        Dictionary<Name, MatcherInfo> Matchers,
        Dictionary<Name, ImmutableArray<int>> Classes);

    /// <summary>The strict line parser: unknown kinds or fields, missing fields, wrong types and duplicates fail, naming the line.</summary>
    private sealed class Parser(string source, string bundleSha256)
    {
        private static readonly Dictionary<string, ReducibilityStatus> StatusNames = new(StringComparer.Ordinal)
        {
            ["reducible"] = ReducibilityStatus.Reducible,
            ["semireducible"] = ReducibilityStatus.Semireducible,
            ["irreducible"] = ReducibilityStatus.Irreducible,
            ["implicitReducible"] = ReducibilityStatus.ImplicitReducible,
            ["instanceReducible"] = ReducibilityStatus.InstanceReducible,
        };

        private readonly ImmutableArray<SimpEntry>.Builder _simp = ImmutableArray.CreateBuilder<SimpEntry>();
        private readonly ImmutableArray<CongrEntry>.Builder _congr = ImmutableArray.CreateBuilder<CongrEntry>();
        private readonly ImmutableArray<SpecEntry>.Builder _spec = ImmutableArray.CreateBuilder<SpecEntry>();
        private readonly HashSet<Name> _specNames = [];
        private readonly List<InstanceEntry> _instances = [];
        private readonly HashSet<Name> _instanceNames = [];
        private readonly Dictionary<Name, ReducibilityStatus> _statuses = [];
        private readonly HashSet<Name> _defEq = [];
        private readonly Dictionary<Name, MatcherInfo> _matchers = [];
        private readonly Dictionary<Name, ImmutableArray<int>> _classes = [];
        private SidecarHeader? _header;
        private long _lineNumber;

        public void Line(string line)
        {
            _lineNumber++;
            if (string.IsNullOrWhiteSpace(line))
            {
                return;
            }
            JsonDocument doc;
            try
            {
                doc = JsonDocument.Parse(line);
            }
            catch (JsonException ex)
            {
                throw Error($"invalid JSON: {ex.Message}", ex);
            }
            using (doc)
            {
                var root = doc.RootElement;
                if (root.ValueKind != JsonValueKind.Object)
                {
                    throw Error("expected a JSON object");
                }
                var kind = root.TryGetProperty("kind", out var k) && k.ValueKind == JsonValueKind.String
                    ? k.GetString()!
                    : throw Error("missing string field 'kind'");
                if (_header is null && kind != "header")
                {
                    throw Error($"expected a header line, found kind '{kind}'");
                }
                switch (kind)
                {
                    case "header": Header(root); break;
                    case "simp": Simp(root); break;
                    case "congr": Congr(root); break;
                    case "instance": Instance(root); break;
                    case "reducibility": Reducibility(root); break;
                    case "defeq": DefEq(root); break;
                    case "matcher": Matcher(root); break;
                    case "class": Class(root); break;
                    case "spec": Spec(root); break;
                    default: throw Error($"unknown kind '{kind}'");
                }
            }
        }

        public Sidecar Finish()
        {
            if (_header is null)
            {
                throw Error("empty input: expected a header line");
            }
            var data = new Data(_header, _simp.ToImmutable(), _congr.ToImmutable(), _spec.ToImmutable(), _defEq, _matchers, _classes);
            var sidecar = new Sidecar(data, null);
            foreach (var (name, status) in _statuses)
            {
                sidecar._statuses.Add(name, status);
            }
            foreach (var instance in _instances)
            {
                sidecar.AddInstanceEntry(instance);
            }
            sidecar.Freeze();
            return sidecar;
        }

        private void Header(JsonElement e)
        {
            Fields(e, "header", "format", "lean", "bundleSha256");
            if (_header is not null)
            {
                throw Error("a second header");
            }
            var format = Int(e, "format");
            if (format != FormatVersion)
            {
                throw Error($"unsupported sidecar format {format}; this loader reads format {FormatVersion}");
            }
            var sha = Str(e, "bundleSha256");
            if (!string.Equals(sha, bundleSha256, StringComparison.OrdinalIgnoreCase))
            {
                throw Error($"the sidecar was made for the bundle with SHA-256 {sha}, but the loaded bundle's SHA-256 is {bundleSha256}; regenerate it with scripts/export-attributes.sh");
            }
            _header = new SidecarHeader(format, Str(e, "lean"), sha);
        }

        private void Simp(JsonElement e)
        {
            Fields(e, "simp", "name", "prio", "post", "inv", "module", "leanKeys");
            _simp.Add(new SimpEntry(
                NameOf(e, "name"), Int(e, "prio"), Bool(e, "post"), Bool(e, "inv"), NameOf(e, "module"),
                [.. Array(e, "leanKeys").Select(k => k.ValueKind == JsonValueKind.String ? k.GetString()! : throw Error("'leanKeys' must hold strings"))]));
        }

        private void Spec(JsonElement e)
        {
            Fields(e, "spec", "name", "prio", "form", "module");
            var form = Str(e, "form") switch
            {
                "triple" => SpecForm.Triple,
                "equation" => SpecForm.Equation,
                var other => throw Error($"unknown spec form '{other}'"),
            };
            var entry = new SpecEntry(NameOf(e, "name"), Int(e, "prio"), form, NameOf(e, "module"));
            if (!_specNames.Add(entry.Name))
            {
                throw Error($"duplicate spec entry for '{entry.Name}'");
            }
            _spec.Add(entry);
        }

        private void Congr(JsonElement e)
        {
            Fields(e, "congr", "name", "fn", "prio", "hyps");
            _congr.Add(new CongrEntry(NameOf(e, "name"), NameOf(e, "fn"), Int(e, "prio"), Ints(e, "hyps")));
        }

        private void Instance(JsonElement e)
        {
            Fields(e, "instance", "name", "class", "prio", "order");
            var entry = new InstanceEntry(NameOf(e, "name"), NameOf(e, "class"), Int(e, "prio"), Int(e, "order"));
            if (!_instanceNames.Add(entry.Name))
            {
                throw Error($"duplicate instance '{entry.Name}'");
            }
            _instances.Add(entry);
        }

        private void Reducibility(JsonElement e)
        {
            Fields(e, "reducibility", "name", "status");
            var name = NameOf(e, "name");
            var text = Str(e, "status");
            var status = StatusNames.TryGetValue(text, out var s) ? s : throw Error($"unknown reducibility status '{text}'");
            if (!_statuses.TryAdd(name, status))
            {
                throw Error($"duplicate reducibility entry for '{name}'");
            }
        }

        private void DefEq(JsonElement e)
        {
            Fields(e, "defeq", "name");
            var name = NameOf(e, "name");
            if (!_defEq.Add(name))
            {
                throw Error($"duplicate defeq entry for '{name}'");
            }
        }

        private void Matcher(JsonElement e)
        {
            Fields(e, "matcher", "name", "numParams", "numDiscrs", "uElimPos", "discrNames", "alts", "overlaps");
            var name = NameOf(e, "name");
            var uElim = e.GetProperty("uElimPos");
            var info = new MatcherInfo(
                name,
                Int(e, "numParams"),
                Int(e, "numDiscrs"),
                [.. Array(e, "alts").Select(a =>
                {
                    Fields(a, null, "numFields", "numOverlaps", "unitThunk");
                    return new MatcherAltInfo(Int(a, "numFields"), Int(a, "numOverlaps"), Bool(a, "unitThunk"));
                })],
                uElim.ValueKind == JsonValueKind.Null ? null : Int(e, "uElimPos"),
                [.. Array(e, "discrNames").Select(d => d.ValueKind == JsonValueKind.Null ? null : ParseName(d, "discrNames"))],
                [.. Array(e, "overlaps").Select(p =>
                {
                    var pair = p.ValueKind == JsonValueKind.Array && p.GetArrayLength() == 2 ? p : throw Error("'overlaps' must hold pairs");
                    return (IntValue(pair[0], "overlaps"), IntValue(pair[1], "overlaps"));
                })]);
            if (!_matchers.TryAdd(name, info))
            {
                throw Error($"duplicate matcher entry for '{name}'");
            }
        }

        private void Class(JsonElement e)
        {
            Fields(e, "class", "name", "outParams");
            var name = NameOf(e, "name");
            if (!_classes.TryAdd(name, Ints(e, "outParams")))
            {
                throw Error($"duplicate class entry for '{name}'");
            }
        }

        /// <summary>Checks that <paramref name="e"/> has exactly <paramref name="fields"/> (plus <c>kind</c> on a line), each once.</summary>
        private void Fields(JsonElement e, string? kind, params ReadOnlySpan<string> fields)
        {
            if (e.ValueKind != JsonValueKind.Object)
            {
                throw Error("expected a JSON object");
            }
            var expected = new HashSet<string>(StringComparer.Ordinal);
            foreach (var f in fields)
            {
                expected.Add(f);
            }
            if (kind is not null)
            {
                expected.Add("kind");
            }
            var seen = new HashSet<string>(StringComparer.Ordinal);
            var what = kind is null ? "object" : $"{kind} entry";
            foreach (var p in e.EnumerateObject())
            {
                if (!expected.Contains(p.Name))
                {
                    throw Error($"unknown field '{p.Name}' in {what}");
                }
                if (!seen.Add(p.Name))
                {
                    throw Error($"duplicate field '{p.Name}' in {what}");
                }
            }
            foreach (var f in expected)
            {
                if (!seen.Contains(f))
                {
                    throw Error($"missing field '{f}' in {what}");
                }
            }
        }

        private string Str(JsonElement e, string field)
        {
            var v = e.GetProperty(field);
            return v.ValueKind == JsonValueKind.String ? v.GetString()! : throw Error($"'{field}' must be a string");
        }

        private int Int(JsonElement e, string field) => IntValue(e.GetProperty(field), field);

        private int IntValue(JsonElement v, string field) =>
            v.ValueKind == JsonValueKind.Number && v.TryGetInt32(out var i) && i >= 0
                ? i
                : throw Error($"'{field}' must be a natural number");

        private bool Bool(JsonElement e, string field)
        {
            var v = e.GetProperty(field);
            return v.ValueKind is JsonValueKind.True or JsonValueKind.False ? v.GetBoolean() : throw Error($"'{field}' must be a boolean");
        }

        private JsonElement.ArrayEnumerator Array(JsonElement e, string field)
        {
            var v = e.GetProperty(field);
            return v.ValueKind == JsonValueKind.Array ? v.EnumerateArray() : throw Error($"'{field}' must be an array");
        }

        private ImmutableArray<int> Ints(JsonElement e, string field) => [.. Array(e, field).Select(v => IntValue(v, field))];

        private Name NameOf(JsonElement e, string field) => ParseName(e.GetProperty(field), field);

        private Name ParseName(JsonElement v, string field)
        {
            if (v.ValueKind != JsonValueKind.String)
            {
                throw Error($"'{field}' must be a name string");
            }
            try
            {
                var name = Name.Parse(v.GetString()!);
                return name.IsAnonymous ? throw Error($"'{field}' is empty") : name;
            }
            catch (FormatException ex)
            {
                throw Error($"'{field}' is not a name: {ex.Message}", ex);
            }
        }

        private SidecarFormatException Error(string message, Exception? inner = null) => new(source, _lineNumber, message, inner);
    }
}
