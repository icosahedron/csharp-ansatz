using System.Diagnostics.CodeAnalysis;
using LeanSharp.Cic;

namespace LeanSharp.Kernel;

/// <summary>
/// The set of constants the kernel has admitted. Only the kernel's admission functions
/// (<see cref="Kernel"/>) add to it.
/// </summary>
/// <remarks>
/// Admission can fail part-way through (for example after declaring an inductive type but before
/// its recursor checks out), so work happens on a <see cref="Fork"/> that is committed only on
/// success, mirroring how Lean's persistent environments are discarded on error.
/// </remarks>
public sealed class KernelEnvironment
{
    private readonly KernelEnvironment? _parent;
    private readonly Dictionary<Name, ConstantInfo> _constants = [];
    private bool? _quotInitialized;

    /// <summary>Creates an empty environment.</summary>
    public KernelEnvironment()
    {
    }

    private KernelEnvironment(KernelEnvironment parent) => _parent = parent;

    /// <summary>The number of constants (including any in parent environments).</summary>
    public int Count => _constants.Count + (_parent?.Count ?? 0);

    /// <summary>Whether the quotient package (<c>Quot</c>, <c>Quot.mk</c>, …) has been added.</summary>
    public bool IsQuotInitialized => _quotInitialized ?? _parent?.IsQuotInitialized ?? false;

    /// <summary>Looks up a constant.</summary>
    public ConstantInfo? Find(Name name)
    {
        for (var env = this; env is not null; env = env._parent)
        {
            if (env._constants.TryGetValue(name, out var c))
            {
                return c;
            }
        }
        return null;
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
    public IEnumerable<ConstantInfo> Constants =>
        _parent is null ? _constants.Values : _parent.Constants.Concat(_constants.Values);

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

    /// <summary>A child environment whose additions become visible here only after <see cref="Commit"/>.</summary>
    internal KernelEnvironment Fork() => new(this);

    /// <summary>Adds this fork's constants (and quotient flag) to its parent.</summary>
    internal void Commit()
    {
        var parent = _parent ?? throw new InvalidOperationException("Only a fork can be committed.");
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
    internal void AddCore(ConstantInfo constant) => _constants[constant.Name] = constant;

    internal void MarkQuotInitialized() => _quotInitialized = true;
}
