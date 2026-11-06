using System.Diagnostics.CodeAnalysis;
using Warrant.Cic;

namespace Warrant.Kernel;

/// <summary>
/// The set of constants the kernel has admitted. Only the kernel's admission functions
/// (<see cref="Kernel"/>) add to it.
/// </summary>
/// <remarks>
/// <para>
/// Admission can fail part-way through (for example after declaring an inductive type but before
/// its recursor checks out), so work happens on a child environment that is committed only on
/// success, mirroring how Lean's persistent environments are discarded on error.
/// </para>
/// <para>
/// An environment that will not grow further can be <see cref="Freeze">frozen</see> and then
/// <see cref="Fork">forked</see>: each fork is an O(1) overlay that sees the frozen base and admits
/// into itself only. Since nothing writes to the base after freezing, any number of forks can
/// read it in parallel.
/// </para>
/// <para>
/// A base environment can have a <see cref="IConstantSource">source</see> (M5b KTD18): constants it reads on demand, after
/// its own and before reporting a constant unknown. Such an environment cannot enumerate its <see cref="Constants"/>.
/// </para>
/// </remarks>
public sealed class KernelEnvironment
{
    private readonly KernelEnvironment? _parent;
    private readonly Dictionary<Name, ConstantInfo> _constants = [];
    private readonly IConstantSource? _source;
    private readonly bool _sourceQuotInitialized;
    private bool? _quotInitialized;
    private bool _frozen;

    /// <summary>Creates an empty environment.</summary>
    public KernelEnvironment()
    {
    }

    /// <summary>
    /// Creates an environment on a source of trusted constants, which it reads as they are needed. The quotient package
    /// counts as added only when the source says so and its four quotient constants are exactly the ones the kernel
    /// generates (<see cref="Quotient.ExpectedConstants"/>): the flag enables quotient reduction, so a source cannot set it
    /// by claiming it.
    /// </summary>
    /// <param name="source">The source.</param>
    public KernelEnvironment(IConstantSource source)
    {
        _source = source ?? throw new ArgumentNullException(nameof(source));
        _sourceQuotInitialized = source.QuotientsInitialized && Quotient.HoldsExpectedConstants(source);
    }

    private KernelEnvironment(KernelEnvironment parent) => _parent = parent;

    /// <summary>The number of constants (including any in parent environments and the source).</summary>
    public int Count => _constants.Count + (_parent?.Count ?? _source?.Count ?? 0);

    /// <summary>Whether this environment has been frozen (see <see cref="Freeze"/>).</summary>
    public bool IsFrozen => _frozen;

    /// <summary>Whether the quotient package (<c>Quot</c>, <c>Quot.mk</c>, …) has been added.</summary>
    public bool IsQuotInitialized => _quotInitialized ?? _parent?.IsQuotInitialized ?? _sourceQuotInitialized;

    /// <summary>Looks up a constant: in this environment, its parents, then the base environment's source.</summary>
    public ConstantInfo? Find(Name name)
    {
        var env = this;
        while (true)
        {
            if (env._constants.TryGetValue(name, out var c))
            {
                return c;
            }
            if (env._parent is null)
            {
                return env._source is not null && env._source.TryGet(name, out var fromSource) ? fromSource : null;
            }
            env = env._parent;
        }
    }

    /// <summary>Looks up a constant.</summary>
    public bool TryGet(Name name, [NotNullWhen(true)] out ConstantInfo? constant)
    {
        constant = Find(name);
        return constant is not null;
    }

    /// <summary>Looks up a constant.</summary>
    /// <exception cref="KernelException">The constant is unknown.</exception>
    public ConstantInfo Get(Name name) => Find(name) ?? throw new KernelException($"unknown constant '{name}'");

    /// <summary>All constants (unordered).</summary>
    /// <exception cref="InvalidOperationException">The base environment reads its constants from a source, which is not enumerated.</exception>
    public IEnumerable<ConstantInfo> Constants =>
        _parent is null
            ? _source is null ? _constants.Values : throw new InvalidOperationException("An environment on a constant source cannot enumerate its constants.")
            : _parent.Constants.Concat(_constants.Values);

    /// <summary>Rejects a name that is already declared.</summary>
    /// <exception cref="KernelException">The name is taken.</exception>
    public void CheckName(Name name)
    {
        if (Find(name) is not null)
        {
            throw new KernelException($"'{name}' has already been declared");
        }
    }

    /// <summary>The constants added to this environment itself (not its parents), in insertion order.</summary>
    internal IEnumerable<ConstantInfo> LocalConstants => _constants.Values;

    /// <summary>
    /// Forbids any further additions to this environment, so that it can be shared by
    /// <see cref="Fork">forks</see>. Admitting into a frozen environment throws
    /// <see cref="InvalidOperationException"/>. Freezing is permanent and idempotent.
    /// </summary>
    public void Freeze() => _frozen = true;

    /// <summary>
    /// An empty overlay on this frozen environment: it sees every constant here and admits new
    /// ones into itself only, so neither this environment nor any other fork of it sees them.
    /// </summary>
    /// <exception cref="InvalidOperationException">This environment is not frozen.</exception>
    public KernelEnvironment Fork()
    {
        if (!_frozen)
        {
            throw new InvalidOperationException("Only a frozen environment can be forked; call Freeze first.");
        }
        return new(this);
    }

    /// <summary>A child environment whose additions become visible here only after <see cref="Commit"/>.</summary>
    internal KernelEnvironment Child() => new(this);

    /// <summary>Adds this child's constants (and quotient flag) to its parent.</summary>
    /// <exception cref="InvalidOperationException">The parent is frozen.</exception>
    internal void Commit()
    {
        var parent = _parent ?? throw new InvalidOperationException("Only a child environment can be committed.");
        parent.ThrowIfFrozen();
        foreach (var (name, c) in _constants)
        {
            parent._constants.Add(name, c);
        }
        if (_quotInitialized is { } q)
        {
            parent._quotInitialized = q;
        }
    }

    /// <summary>Adds a constant without checking it (the kernel's <c>add_core</c>).</summary>
    internal void AddCore(ConstantInfo constant)
    {
        ThrowIfFrozen();
        _constants[constant.Name] = constant;
    }

    internal void MarkQuotInitialized()
    {
        ThrowIfFrozen();
        _quotInitialized = true;
    }

    private void ThrowIfFrozen()
    {
        if (_frozen)
        {
            throw new InvalidOperationException("The environment is frozen; admit into a fork of it instead.");
        }
    }
}
