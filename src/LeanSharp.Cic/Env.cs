using System.Diagnostics.CodeAnalysis;

namespace LeanSharp.Cic;

/// <summary>
/// A set of constants indexed by name, together with the declarations that introduced them, in
/// admission order.
/// </summary>
/// <remarks>
/// This is a plain container: adding a declaration does not type-check it. Checking is the
/// kernel's job (milestone 2), which will decide what may be added.
/// </remarks>
public sealed class Env
{
    private readonly Dictionary<Name, ConstantInfo> _constants = [];
    private readonly List<Declaration> _declarations = [];

    /// <summary>The number of constants.</summary>
    public int ConstantCount => _constants.Count;

    /// <summary>The declarations, in the order they were added.</summary>
    public IReadOnlyList<Declaration> Declarations => _declarations;

    /// <summary>All constants (unordered).</summary>
    public IEnumerable<ConstantInfo> Constants => _constants.Values;

    /// <summary>Adds every constant of <paramref name="declaration"/>.</summary>
    /// <exception cref="DuplicateConstantException">A constant with the same name already exists.</exception>
    public void Add(Declaration declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        var constants = declaration.Constants;
        var seen = new HashSet<Name>();
        foreach (var c in constants)
        {
            if (_constants.ContainsKey(c.Name) || !seen.Add(c.Name))
            {
                throw new DuplicateConstantException(c.Name);
            }
        }
        foreach (var c in constants)
        {
            _constants.Add(c.Name, c);
        }
        _declarations.Add(declaration);
    }

    /// <summary>Looks up a constant by name.</summary>
    public bool TryGet(Name name, [NotNullWhen(true)] out ConstantInfo? constant) =>
        _constants.TryGetValue(name, out constant);

    /// <summary>Looks up a constant by name, or returns <see langword="null"/>.</summary>
    public ConstantInfo? Find(Name name) => _constants.GetValueOrDefault(name);

    /// <summary>Whether a constant with this name exists.</summary>
    public bool Contains(Name name) => _constants.ContainsKey(name);
}

/// <summary>Thrown when a declaration would redefine an existing constant.</summary>
public sealed class DuplicateConstantException : Exception
{
    /// <summary>Creates the exception for <paramref name="name"/>.</summary>
    public DuplicateConstantException(Name name)
        : base($"Constant '{name}' is already declared.") => ConstantName = name;

    /// <summary>Creates the exception with a message.</summary>
    public DuplicateConstantException()
        : base("Constant is already declared.") => ConstantName = Name.Anonymous;

    /// <summary>Creates the exception with a message.</summary>
    public DuplicateConstantException(string message)
        : base(message) => ConstantName = Name.Anonymous;

    /// <summary>Creates the exception with a message and inner exception.</summary>
    public DuplicateConstantException(string message, Exception innerException)
        : base(message, innerException) => ConstantName = Name.Anonymous;

    /// <summary>The duplicated name.</summary>
    public Name ConstantName { get; }
}
