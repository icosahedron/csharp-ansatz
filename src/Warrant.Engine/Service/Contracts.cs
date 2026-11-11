using System.Collections.Immutable;
using System.Globalization;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.Json.Serialization.Metadata;
using Warrant.Kernel;
using Warrant.Vir;

namespace Warrant.Engine.Service;

/// <summary>
/// A request to verify a compilation's units (M5b KTD6, docs/m5b/02). The client extracted the units; the service reads
/// their canonical VIR back with <see cref="VirReader"/> and never needs Roslyn. Spans and source text stay with the
/// client, which renders the outcomes.
/// </summary>
/// <param name="ProtocolVersion">The protocol the client speaks; <see cref="VerificationService.ProtocolVersion"/>.</param>
/// <param name="RequestId">An id the client chose, by which the request can be cancelled.</param>
/// <param name="ProjectDirectory">The project's directory, which names the project in the server's state.</param>
/// <param name="CacheDirectory">The project's result cache directory; null for no cache.</param>
/// <param name="Budgets">The project's budgets, which a theorem's <c>[Theorem(...)]</c> arguments override.</param>
/// <param name="Recheck">Whether every cached proof is to be checked by the kernel again (<c>WarrantRecheck</c>).</param>
/// <param name="Priority">Design §8.1's priority; kept in the protocol and unused until an IDE client exists.</param>
/// <param name="Units">The units, in extraction order, which the response keeps.</param>
public sealed record VerifyRequest(
    int ProtocolVersion,
    string RequestId,
    string ProjectDirectory,
    string? CacheDirectory,
    VerifyBudgets Budgets,
    bool Recheck,
    int Priority,
    ImmutableArray<RequestUnit> Units)
{
    /// <summary>
    /// What the service needs to build the run's assumption report, which it keeps per project directory for
    /// <c>report(project)</c> (M5b KTD25); null for no report.
    /// </summary>
    public VerifyReport? Report { get; init; }
}

/// <summary>
/// The parts of an assumption report only the client knows (M5b KTD25): the compilation's overflow setting, the bundle's
/// name as reports print it, and each theorem's claim as its source reads.
/// </summary>
/// <param name="CheckOverflow">Whether the compilation checks arithmetic for overflow.</param>
/// <param name="Bundle">The semantics bundle's name, as <see cref="Reports.ReportSettings.Bundle"/> has it.</param>
/// <param name="Claims">Each theorem's claim text and each contract member's Spec calls (M6 U20), by unit key; a unit without one has no entry.</param>
public sealed record VerifyReport(bool CheckOverflow, string Bundle, ImmutableDictionary<string, string> Claims);

/// <summary>A request to verify one unit with a trace of its proof script (M5b KTD24, <c>warrant explain</c>).</summary>
/// <param name="Request">The unit and its closure; its cache directory is ignored, since an explanation runs the tactics.</param>
/// <param name="UnitKey">The unit to trace.</param>
public sealed record ExplainRequest(VerifyRequest Request, string UnitKey);

/// <summary>The answer to an <see cref="ExplainRequest"/>.</summary>
/// <param name="Response">The verification of the request's units.</param>
/// <param name="Steps">The traced unit's proof script, step by step; empty when it has no script or it did not run.</param>
public sealed record ExplainResponse(VerifyResponse Response, ImmutableArray<TacticStep> Steps);

/// <summary>The answer to <c>export(request)</c> (M5b KTD25): the verification, and the certificate file of what it admitted.</summary>
/// <param name="Response">The verification of the request's units, without the cache.</param>
/// <param name="Certificates">
/// The semantics bundle and every declaration the run admitted, as lean4export NDJSON compressed with gzip: the file
/// <c>warrant verify --out</c> writes, which another kernel can check on its own.
/// </param>
/// <param name="Admitted">The number of declarations the run admitted.</param>
public sealed record ExportResponse(VerifyResponse Response, ReadOnlyMemory<byte> Certificates, int Admitted);

/// <summary>A project's budgets for each unit (M5a R13, M5b R5): every field of the kernel's and the tactics' limits.</summary>
/// <param name="KernelFuel">The kernel's fuel per unit.</param>
/// <param name="KernelMaxNatBytes">The kernel's limit on the size of a numeral, in bytes.</param>
/// <param name="TacticFuel">Meta's and the tactics' fuel per unit.</param>
/// <param name="Timeout">The wall-clock limit per unit, from when a worker starts it.</param>
public sealed record VerifyBudgets(long KernelFuel, long KernelMaxNatBytes, long TacticFuel, TimeSpan Timeout)
{
    /// <summary>The budgets of a set of engine options.</summary>
    /// <param name="options">The options.</param>
    /// <returns>The budgets.</returns>
    public static VerifyBudgets From(EngineOptions options)
    {
        ArgumentNullException.ThrowIfNull(options);
        return new(options.Kernel.Fuel, options.Kernel.MaxNatBytes, options.TacticFuel, options.Timeout);
    }
}

/// <summary>One unit of a request.</summary>
/// <param name="Key">The unit's documentation-comment ID, by which an unreadable unit is still reported.</param>
/// <param name="Kind">What the unit is.</param>
/// <param name="DisplayName">The C# display name (M4 KTD6); null to fall back to one derived from the key.</param>
/// <param name="Vir">The unit's canonical VIR encoding (<see cref="VirWriter.Write"/>).</param>
public sealed record RequestUnit(string Key, VirUnitKind Kind, string? DisplayName, ReadOnlyMemory<byte> Vir);

/// <summary>The answer to a <see cref="VerifyRequest"/>.</summary>
/// <param name="ProtocolVersion">The protocol the service speaks.</param>
/// <param name="RequestId">The request's id.</param>
/// <param name="Units">One result per unit, in the request's order, whatever order they finished in (M5b R7).</param>
/// <param name="Counters">Where the results came from.</param>
/// <param name="Elapsed">The time the service spent on the request.</param>
public sealed record VerifyResponse(
    int ProtocolVersion, string RequestId, ImmutableArray<UnitResult> Units, VerifyCounters Counters, TimeSpan Elapsed);

/// <summary>One unit's result.</summary>
/// <param name="Outcome">The outcome.</param>
/// <param name="FromCache">Whether the outcome came from the result cache rather than a run.</param>
/// <param name="Rechecked">Whether the kernel checked a cached proof again for it (<c>WarrantRecheck</c>).</param>
/// <param name="Elapsed">The time from when the unit started to its outcome; zero for a unit that never started.</param>
public sealed record UnitResult(OutcomeDto Outcome, bool FromCache, bool Rechecked, TimeSpan Elapsed);

/// <summary>A request's counters (M5b R8).</summary>
/// <param name="Hits">Units whose outcome came from the result cache.</param>
/// <param name="Misses">Units that were verified because the cache had no outcome for them.</param>
/// <param name="TacticRuns">Units whose proof search ran: theorems, and recursive definitions' decrease proofs.</param>
/// <param name="Rechecked">Units among <paramref name="Hits"/> whose cached proofs the kernel checked again (<c>WarrantRecheck</c>, M5b R11).</param>
public sealed record VerifyCounters(int Hits, int Misses, int TacticRuns, int Rechecked);

/// <summary>Which <see cref="UnitOutcome"/> an <see cref="OutcomeDto"/> carries.</summary>
public enum OutcomeKind
{
    /// <summary><see cref="TranslatedOutcome"/>.</summary>
    Translated,

    /// <summary><see cref="ProvedOutcome"/>.</summary>
    Proved,

    /// <summary><see cref="FalseOutcome"/>.</summary>
    False,

    /// <summary><see cref="NotProvedOutcome"/>.</summary>
    NotProved,

    /// <summary><see cref="UndecidedOutcome"/>.</summary>
    Undecided,

    /// <summary><see cref="InternalErrorOutcome"/>.</summary>
    InternalError,

    /// <summary><see cref="FailedOutcome"/>.</summary>
    Failed,

    /// <summary><see cref="SkippedOutcome"/>.</summary>
    Skipped,

    /// <summary><see cref="CancelledOutcome"/>.</summary>
    Cancelled,
}

/// <summary>
/// A <see cref="UnitOutcome"/> on the wire (M5b KTD6, KTD7): everything the client renders, with positions as VIR node IDs,
/// which the client maps through its own extraction's span table. The kernel declarations a unit admitted stay with the
/// service.
/// </summary>
/// <param name="Kind">Which outcome it is.</param>
/// <param name="Key">The unit's key.</param>
/// <param name="UnitKind">What the unit is.</param>
/// <param name="DisplayName">The C# display name.</param>
/// <param name="Assumptions">The unit's assumptions, with those a theorem inherits.</param>
public sealed record OutcomeDto(OutcomeKind Kind, string Key, VirUnitKind UnitKind, string DisplayName, ImmutableArray<AssumptionDto> Assumptions)
{
    /// <summary>A proved theorem's proof.</summary>
    public ProofKind? By { get; init; }

    /// <summary>A not-proved theorem's message, or the reason of an undecided, internal-error, failed or skipped unit.</summary>
    public string? Message { get; init; }

    /// <summary>A not-proved theorem's goals.</summary>
    public string? Goals { get; init; }

    /// <summary>The node a not-proved theorem's tactic failed at, or a failed unit's diagnostic points at.</summary>
    public int? Node { get; init; }

    /// <summary>A not-proved theorem's counterexample.</summary>
    public ImmutableArray<CounterexampleValue> Counterexample { get; init; } = [];

    /// <summary>A recursive method's decrease obligation that was not proved.</summary>
    public DecreaseFailure? Decrease { get; init; }

    /// <summary>A contract obligation's failing VCs, each at its node (M6 U11, #90).</summary>
    public ImmutableArray<Contracts.VcFailure> Vcs { get; init; } = [];

    /// <summary>A false comparison's sides with their values.</summary>
    public ImmutableArray<ReadBackSideDto> Sides { get; init; } = [];

    /// <summary>A skipped unit's dependency that was not admitted.</summary>
    public string? Dependency { get; init; }

    /// <summary>A failed unit's diagnostic code when the fault is the user's (<see cref="FailedOutcome.Code"/>).</summary>
    public string? Code { get; init; }

    /// <summary>The wire form of an outcome.</summary>
    /// <param name="outcome">The outcome.</param>
    /// <returns>Its wire form.</returns>
    public static OutcomeDto From(UnitOutcome outcome)
    {
        ArgumentNullException.ThrowIfNull(outcome);
        ImmutableArray<AssumptionDto> assumptions = [.. outcome.Assumptions.Select(a => new AssumptionDto(a.UnitKey, a.Assumption.Kind, a.Assumption.Subject))];
        OutcomeDto Of(OutcomeKind kind) => new(kind, outcome.Key, outcome.UnitKind, outcome.DisplayName, assumptions);
        return outcome switch
        {
            TranslatedOutcome => Of(OutcomeKind.Translated),
            ProvedOutcome p => Of(OutcomeKind.Proved) with { By = p.By },
            FalseOutcome f => Of(OutcomeKind.False) with { Sides = [.. f.Sides.Select(ReadBackSideDto.From)] },
            NotProvedOutcome n => Of(OutcomeKind.NotProved) with
            {
                Message = n.Message,
                Goals = n.Goals,
                Node = n.TacticNode,
                Counterexample = n.Counterexample,
                Decrease = n.Decrease,
                Vcs = n.Vcs,
            },
            UndecidedOutcome u => Of(OutcomeKind.Undecided) with { Message = u.Reason },
            InternalErrorOutcome i => Of(OutcomeKind.InternalError) with { Message = i.Reason },
            FailedOutcome f => Of(OutcomeKind.Failed) with { Message = f.Reason, Code = f.Code, Node = f.Node },
            SkippedOutcome s => Of(OutcomeKind.Skipped) with { Message = s.Reason, Dependency = s.Dependency },
            CancelledOutcome => Of(OutcomeKind.Cancelled),
            _ => throw new ArgumentException($"Unknown outcome {outcome.GetType().Name}.", nameof(outcome)),
        };
    }

    /// <summary>
    /// The outcome this wire form describes, with the declarations the unit admitted, as a cached outcome is rebuilt
    /// (M5b KTD14).
    /// </summary>
    /// <param name="declarations">
    /// The unit's admitted declarations (its certificate): a proved theorem's theorem, a translated unit's declarations;
    /// ignored for every other outcome.
    /// </param>
    /// <returns>The outcome.</returns>
    /// <exception cref="FormatException">A field the outcome needs is missing or malformed, or a proved theorem's certificate does not hold exactly one theorem.</exception>
    public UnitOutcome ToOutcome(ImmutableArray<KernelDeclaration> declarations)
    {
        ImmutableArray<UnitAssumption> assumptions = [.. Assumptions.Select(a => new UnitAssumption(a.UnitKey, new VirAssumption(a.Kind, a.Subject)))];
        string Text(string? text) => text ?? throw new FormatException($"The {Kind} outcome of {Key} has no message.");
        return Kind switch
        {
            OutcomeKind.Translated => new TranslatedOutcome(Key, UnitKind, DisplayName, assumptions, declarations),
            OutcomeKind.Proved => new ProvedOutcome(
                Key, UnitKind, DisplayName, assumptions, By ?? throw new FormatException($"The proved outcome of {Key} has no proof kind."),
                declarations is [TheoremDecl theorem] ? theorem : throw new FormatException($"The certificate of {Key} does not hold exactly one theorem.")),
            OutcomeKind.False => new FalseOutcome(Key, UnitKind, DisplayName, assumptions, [.. Sides.Select(s => s.ToSide())]),
            OutcomeKind.NotProved => new NotProvedOutcome(Key, UnitKind, DisplayName, assumptions, Text(Message), Goals ?? "", Node, Counterexample)
            {
                Decrease = Decrease,
                Vcs = Vcs.IsDefault ? [] : Vcs,
            },
            OutcomeKind.Undecided => new UndecidedOutcome(Key, UnitKind, DisplayName, assumptions, Text(Message)),
            OutcomeKind.InternalError => new InternalErrorOutcome(Key, UnitKind, DisplayName, assumptions, Text(Message)),
            OutcomeKind.Failed => new FailedOutcome(Key, UnitKind, DisplayName, assumptions, Text(Message)) { Code = Code, Node = Node },
            OutcomeKind.Skipped => new SkippedOutcome(
                Key, UnitKind, DisplayName, assumptions, Dependency ?? throw new FormatException($"The skipped outcome of {Key} names no dependency."), Text(Message)),
            OutcomeKind.Cancelled => new CancelledOutcome(Key, UnitKind, DisplayName, assumptions),
            _ => throw new FormatException($"Unknown outcome kind {Kind}."),
        };
    }
}

/// <summary>One assumption of a unit's outcome (<see cref="UnitAssumption"/>).</summary>
/// <param name="UnitKey">The unit whose VIR records it.</param>
/// <param name="Kind">What is assumed.</param>
/// <param name="Subject">What it is assumed of.</param>
public sealed record AssumptionDto(string UnitKey, VirAssumptionKind Kind, string Subject);

/// <summary>What kind of value a <see cref="ReadBackSideDto"/> holds.</summary>
public enum ReadBackKind
{
    /// <summary>An <c>int</c>.</summary>
    IntValue,

    /// <summary>A <c>long</c>.</summary>
    LongValue,

    /// <summary>A <c>bool</c>.</summary>
    BoolValue,

    /// <summary>A value that was not read back.</summary>
    Unknown,
}

/// <summary>One side of a false comparison (<see cref="ReadBackSide"/>).</summary>
/// <param name="NodeId">The side's VIR node ID.</param>
/// <param name="Kind">The value's kind.</param>
/// <param name="Text">The value as C# writes it, or why it is unknown.</param>
public sealed record ReadBackSideDto(int NodeId, ReadBackKind Kind, string Text)
{
    /// <summary>The wire form of a side.</summary>
    /// <param name="side">The side.</param>
    /// <returns>Its wire form.</returns>
    public static ReadBackSideDto From(ReadBackSide side)
    {
        ArgumentNullException.ThrowIfNull(side);
        return side.Value switch
        {
            Int32Value v => new(side.NodeId, ReadBackKind.IntValue, v.ToString()),
            Int64Value v => new(side.NodeId, ReadBackKind.LongValue, v.ToString()),
            BoolValue v => new(side.NodeId, ReadBackKind.BoolValue, v.ToString()),
            UnknownValue v => new(side.NodeId, ReadBackKind.Unknown, v.Reason),
            _ => throw new ArgumentException($"Unknown value {side.Value.GetType().Name}.", nameof(side)),
        };
    }

    /// <summary>The side this wire form describes.</summary>
    /// <returns>The side.</returns>
    /// <exception cref="FormatException">The text is not a value of the kind.</exception>
    public ReadBackSide ToSide() => new(NodeId, Kind switch
    {
        ReadBackKind.IntValue => new Int32Value(int.Parse(Text, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture)),
        ReadBackKind.LongValue => new Int64Value(long.Parse(Text, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture)),
        ReadBackKind.BoolValue => Text switch
        {
            "true" => new BoolValue(true),
            "false" => new BoolValue(false),
            _ => throw new FormatException($"'{Text}' is not a bool."),
        },
        ReadBackKind.Unknown => (ReadBackValue)new UnknownValue(Text),
        _ => throw new FormatException($"Unknown value kind {Kind}."),
    });
}

/// <summary>
/// The server's JSON-RPC methods and error codes (M5b KTD2, KTD26; docs/m5b/01). Every connection calls
/// <see cref="Hello"/> first.
/// </summary>
public static class ServerProtocol
{
    /// <summary><c>hello(protocol)</c>: checks the client's protocol version; answers a <see cref="HelloResponse"/>.</summary>
    public const string Hello = "hello";

    /// <summary><c>verify(request)</c>: verifies a <see cref="VerifyRequest"/>; answers a <see cref="VerifyResponse"/>.</summary>
    public const string Verify = "verify";

    /// <summary><c>cancel(id)</c>: cancels the running request with that id, from any connection; answers whether one was running.</summary>
    public const string Cancel = "cancel";

    /// <summary><c>status()</c>: answers a <see cref="ServerStatus"/>.</summary>
    public const string Status = "status";

    /// <summary><c>shutdown()</c>: lets the running requests finish, then exits.</summary>
    public const string Shutdown = "shutdown";

    /// <summary><c>explain(request)</c>: verifies an <see cref="ExplainRequest"/> with a trace; answers an <see cref="ExplainResponse"/>.</summary>
    public const string Explain = "explain";

    /// <summary><c>export(request)</c>: verifies a <see cref="VerifyRequest"/> without the cache; answers an <see cref="ExportResponse"/>.</summary>
    public const string Export = "export";

    /// <summary><c>report(project)</c>: answers the JSON assumption report of the project directory's last verify, or null.</summary>
    public const string Report = "report";

    /// <summary>The error of a <c>hello</c> with another protocol version; the server then drains and exits.</summary>
    public const int ProtocolMismatchError = -32001;

    /// <summary>The error of a <c>verify</c> that arrives while the server drains.</summary>
    public const int ShuttingDownError = -32002;

    /// <summary>The error of a <c>verify</c> whose request id another running request already has.</summary>
    public const int RequestIdInUseError = -32003;

    /// <summary>
    /// The wire's JSON options, the same at both ends: camel-case, enums as strings, the service's records through their
    /// source-generated contracts (<see cref="ServiceJsonContext"/>), and any other type by reflection. The fallback is
    /// for the transport's own messages: StreamJsonRpc's <c>$/cancelRequest</c> carries a type the context cannot name,
    /// and without it the notification is dropped, so a client could never cancel the request it is waiting on.
    /// </summary>
    /// <returns>New options.</returns>
    public static JsonSerializerOptions CreateSerializerOptions() => new(ServiceJsonContext.Default.Options)
    {
        TypeInfoResolver = JsonTypeInfoResolver.Combine(ServiceJsonContext.Default, new DefaultJsonTypeInfoResolver()),
    };
}

/// <summary>The answer to <c>hello</c>.</summary>
/// <param name="ProtocolVersion">The protocol the server speaks.</param>
/// <param name="ToolchainIdentity">The server's toolchain identity (<see cref="Toolchain.Identity"/>).</param>
/// <param name="ProcessId">The server's process id.</param>
public sealed record HelloResponse(int ProtocolVersion, string ToolchainIdentity, int ProcessId);

/// <summary>What the server holds and runs (M5b KTD26), the answer to <c>status</c>.</summary>
/// <param name="ProcessId">The server's process id.</param>
/// <param name="Endpoint">The endpoint it listens on: the pipe name on Windows, the socket path elsewhere.</param>
/// <param name="ToolchainIdentity">Its toolchain identity.</param>
/// <param name="Uptime">The time since it started.</param>
/// <param name="BundleSha256">The SHA-256 of the semantics bundle it loaded; null when unknown.</param>
/// <param name="SidecarSha256">The SHA-256 of the attribute sidecar it loaded; null when unknown.</param>
/// <param name="GcHeapBytes">The size of the managed heap after the last garbage collection.</param>
/// <param name="WorkingSetBytes">The process's working set.</param>
/// <param name="Counters">The counters of every request it has answered: cache hits, misses and tactic runs.</param>
/// <param name="ActiveRequests">The requests it is running.</param>
public sealed record ServerStatus(
    int ProcessId,
    string Endpoint,
    string ToolchainIdentity,
    TimeSpan Uptime,
    string? BundleSha256,
    string? SidecarSha256,
    long GcHeapBytes,
    long WorkingSetBytes,
    VerifyCounters Counters,
    ImmutableArray<ActiveRequest> ActiveRequests);

/// <summary>A request the server is running.</summary>
/// <param name="RequestId">The id the client chose, by which <c>cancel</c> stops it.</param>
/// <param name="ProjectDirectory">The project it verifies.</param>
/// <param name="Units">The number of units it carries.</param>
/// <param name="Elapsed">The time since it arrived.</param>
public sealed record ActiveRequest(string RequestId, string ProjectDirectory, int Units, TimeSpan Elapsed);

/// <summary>The System.Text.Json contracts of the service's requests and responses, generated at compile time.</summary>
[JsonSourceGenerationOptions(UseStringEnumConverter = true, PropertyNamingPolicy = JsonKnownNamingPolicy.CamelCase)]
[JsonSerializable(typeof(VerifyRequest))]
[JsonSerializable(typeof(VerifyResponse))]
[JsonSerializable(typeof(ExplainRequest))]
[JsonSerializable(typeof(ExplainResponse))]
[JsonSerializable(typeof(ExportResponse))]
[JsonSerializable(typeof(HelloResponse))]
[JsonSerializable(typeof(ServerStatus))]
[JsonSerializable(typeof(int))]
[JsonSerializable(typeof(bool))]
[JsonSerializable(typeof(string))]
public sealed partial class ServiceJsonContext : JsonSerializerContext;
