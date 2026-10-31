using System.Diagnostics;
using LeanSharp.Cic;

namespace LeanSharp.Kernel;

/// <summary>The kernel's verdict on one exported declaration.</summary>
/// <param name="Name">The declaration's (first) constant name.</param>
/// <param name="Accepted">Whether the kernel admitted it.</param>
/// <param name="Error">Why it was rejected, if it was.</param>
/// <param name="ResourceLimit">Whether the rejection was due to fuel or size limits rather than a type error.</param>
/// <param name="Elapsed">Time spent checking.</param>
public sealed record CheckResult(Name Name, bool Accepted, string? Error, bool ResourceLimit, TimeSpan Elapsed);

/// <summary>
/// Re-checks declarations read from a lean4export file with the LeanSharp kernel, the way Lean's own
/// replay checker does.
/// </summary>
/// <remarks>
/// lean4export provides <em>constants</em>, but the kernel admits <em>declarations</em>, so they
/// are reconstructed:
/// <list type="bullet">
/// <item>An inductive block is re-admitted from its types and constructors only; the constructors
/// and recursors the kernel derives must match the exported ones (up to binder names).</item>
/// <item>The first quotient constant triggers the kernel's quotient package; all four exported
/// quotient constants must match the generated ones.</item>
/// <item>Unsafe or partial definitions with several members in <c>All</c> are buffered and
/// admitted together as one mutual block.</item>
/// </list>
/// Checking must run on a large-stack thread; <see cref="CheckAll"/> takes care of that.
/// </remarks>
public sealed class ExportChecker
{
    private readonly KernelLimits _limits;
    private readonly Dictionary<Name, DefinitionInfo> _pendingMutual = [];

    /// <summary>Creates a checker that admits into <paramref name="env"/>.</summary>
    /// <param name="env">The environment to extend.</param>
    /// <param name="limits">Resource limits per type checker (default: <see cref="KernelLimits.Corpus"/>).</param>
    /// <param name="admitRejected">
    /// When true, a rejected declaration is still added (unchecked) so later declarations that
    /// depend on it can be checked, as in Ansatz's corpus runs. Never use this for a trust decision.
    /// </param>
    public ExportChecker(KernelEnvironment env, KernelLimits? limits = null, bool admitRejected = false)
    {
        Env = env ?? throw new ArgumentNullException(nameof(env));
        _limits = limits ?? KernelLimits.Corpus;
        AdmitRejected = admitRejected;
    }

    /// <summary>The environment being extended.</summary>
    public KernelEnvironment Env { get; }

    /// <summary>Whether rejected declarations are admitted anyway (see the constructor).</summary>
    public bool AdmitRejected { get; }

    /// <summary>Checks every declaration on a large-stack thread, in order.</summary>
    public IReadOnlyList<CheckResult> CheckAll(IEnumerable<Declaration> declarations, Action<CheckResult>? onResult = null)
    {
        ArgumentNullException.ThrowIfNull(declarations);
        return KernelThread.Run(() =>
        {
            var results = new List<CheckResult>();
            foreach (var d in declarations)
            {
                if (Check(d) is { } r)
                {
                    results.Add(r);
                    onResult?.Invoke(r);
                }
            }
            if (_pendingMutual.Count > 0)
            {
                var r = new CheckResult(_pendingMutual.Keys.First(), false, "incomplete mutual definition block", false, TimeSpan.Zero);
                results.Add(r);
                onResult?.Invoke(r);
            }
            return (IReadOnlyList<CheckResult>)results;
        });
    }

    /// <summary>
    /// Checks one declaration. Returns null while a mutual block is still incomplete. Must be called
    /// on a large-stack thread (see <see cref="KernelThread"/>).
    /// </summary>
    public CheckResult? Check(Declaration declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        var name = declaration.Constants[0].Name;
        var sw = Stopwatch.StartNew();
        try
        {
            var fork = Env.Fork();
            switch (declaration)
            {
                case InductiveDeclaration ind:
                    CheckInductive(fork, ind);
                    break;
                case ConstantDeclaration { Constant: QuotInfo q }:
                    CheckQuot(fork, q);
                    break;
                case ConstantDeclaration { Constant: DefinitionInfo { Safety: not DefinitionSafety.Safe, All.Count: > 1 } def }:
                    if (!AddToMutualBlock(fork, def))
                    {
                        return null;
                    }
                    name = def.All[0];
                    break;
                case ConstantDeclaration { Constant: var c }:
                    Kernel.Add(fork, ToKernelDeclaration(c), _limits);
                    break;
                default:
                    throw new ArgumentException($"Unsupported declaration {declaration.GetType().Name}.", nameof(declaration));
            }
            fork.Commit();
            return new CheckResult(name, true, null, false, sw.Elapsed);
        }
        catch (KernelException ex)
        {
            if (AdmitRejected)
            {
                AdmitUnchecked(declaration);
            }
            return new CheckResult(name, false, ex.Message, ex is KernelResourceException, sw.Elapsed);
        }
    }

    private void AdmitUnchecked(Declaration declaration)
    {
        foreach (var c in declaration.Constants)
        {
            if (Env.Find(c.Name) is null)
            {
                Env.AddCore(c);
            }
        }
        if (declaration.Constants.Any(c => c is QuotInfo))
        {
            Env.MarkQuotInitialized();
        }
    }

    private static KernelDeclaration ToKernelDeclaration(ConstantInfo c) => c switch
    {
        AxiomInfo a => new AxiomDecl(a),
        DefinitionInfo d => new DefinitionDecl(d),
        TheoremInfo t => new TheoremDecl(t),
        OpaqueInfo o => new OpaqueDecl(o),
        _ => throw new KernelException($"'{c.Name}': a {c.Kind} cannot be declared on its own"),
    };

    private bool AddToMutualBlock(KernelEnvironment fork, DefinitionInfo def)
    {
        _pendingMutual[def.Name] = def;
        if (!def.All.All(_pendingMutual.ContainsKey))
        {
            return false;
        }
        var members = def.All.Select(n => _pendingMutual[n]).ToEquatableArray();
        foreach (var n in def.All)
        {
            _pendingMutual.Remove(n);
        }
        Kernel.Add(fork, new MutualDefinitionDecl(members), _limits);
        return true;
    }

    private void CheckQuot(KernelEnvironment fork, QuotInfo exported)
    {
        if (!fork.IsQuotInitialized)
        {
            Kernel.Add(fork, new QuotDecl(), _limits);
        }
        if (fork.Find(exported.Name) is not { } generated || !ConstantsMatch(generated, exported))
        {
            throw new KernelException($"exported quotient constant '{exported.Name}' does not match the kernel's");
        }
    }

    private void CheckInductive(KernelEnvironment fork, InductiveDeclaration ind)
    {
        if (ind.Types.Count == 0)
        {
            throw new KernelException("empty inductive declaration");
        }
        var first = ind.Types[0];
        var ctorsByName = new Dictionary<Name, ConstructorInfo>();
        foreach (var c in ind.Constructors)
        {
            if (!ctorsByName.TryAdd(c.Name, c))
            {
                throw new KernelException($"constructor '{c.Name}' is exported twice");
            }
        }
        var types = new List<InductiveType>();
        foreach (var t in ind.Types)
        {
            var ctors = new List<InductiveConstructor>();
            foreach (var cn in t.Constructors)
            {
                if (!ctorsByName.TryGetValue(cn, out var c))
                {
                    throw new KernelException($"constructor '{cn}' of '{t.Name}' is missing from the export");
                }
                ctors.Add(new InductiveConstructor(c.Name, c.Type));
            }
            types.Add(new InductiveType(t.Name, t.Type, ctors.ToEquatableArray()));
        }
        Kernel.Add(fork, new InductiveDecl(first.LevelParams, first.NumParams, types.ToEquatableArray(), first.IsUnsafe), _limits);

        // Everything exported must be exactly what the kernel generated, and vice versa for recursors.
        foreach (var exported in ind.Constants)
        {
            if (fork.Find(exported.Name) is not { } generated || !ConstantsMatch(generated, exported))
            {
                throw new KernelException($"exported {exported.Kind} '{exported.Name}' does not match the one the kernel generates");
            }
        }
        var exportedNames = ind.Constants.Select(c => c.Name).ToHashSet();
        foreach (var generated in fork.LocalConstants)
        {
            if (!exportedNames.Contains(generated.Name))
            {
                throw new KernelException($"the kernel generates '{generated.Name}', which is missing from the export");
            }
        }
    }

    /// <summary>Equality of constants with expressions compared up to binder annotations (Lean's <c>BEq ConstantInfo</c>).</summary>
    internal static bool ConstantsMatch(ConstantInfo a, ConstantInfo b)
    {
        if (a.Kind != b.Kind || a.Name != b.Name || !a.LevelParams.Equals(b.LevelParams) || !a.Type.AlphaEquals(b.Type))
        {
            return false;
        }
        return (a, b) switch
        {
            (InductiveInfo x, InductiveInfo y) =>
                x.NumParams == y.NumParams && x.NumIndices == y.NumIndices && x.All.Equals(y.All)
                && x.Constructors.Equals(y.Constructors) && x.NumNested == y.NumNested && x.IsRec == y.IsRec
                && x.IsUnsafeFlag == y.IsUnsafeFlag && x.IsReflexive == y.IsReflexive,
            (ConstructorInfo x, ConstructorInfo y) =>
                x.Inductive == y.Inductive && x.Index == y.Index && x.NumParams == y.NumParams
                && x.NumFields == y.NumFields && x.IsUnsafeFlag == y.IsUnsafeFlag,
            (RecursorInfo x, RecursorInfo y) =>
                x.All.Equals(y.All) && x.NumParams == y.NumParams && x.NumIndices == y.NumIndices
                && x.NumMotives == y.NumMotives && x.NumMinors == y.NumMinors && x.K == y.K
                && x.IsUnsafeFlag == y.IsUnsafeFlag && x.Rules.Count == y.Rules.Count
                && x.Rules.Zip(y.Rules).All(p => p.First.Constructor == p.Second.Constructor
                    && p.First.NumFields == p.Second.NumFields && p.First.Rhs.AlphaEquals(p.Second.Rhs)),
            (QuotInfo x, QuotInfo y) => x.QuotKind == y.QuotKind,
            _ => a.Value is { } va && b.Value is { } vb ? va.AlphaEquals(vb) : a.Value is null && b.Value is null,
        };
    }
}
