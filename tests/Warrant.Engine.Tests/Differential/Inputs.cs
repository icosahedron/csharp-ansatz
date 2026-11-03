using FsCheck;
using FsCheck.Fluent;
using Warrant.Vir;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// Inputs for differential tests (docs/m4/07, "Inputs"), as .NET values:
/// <list type="bullet">
/// <item><c>int</c> and <c>long</c>: the boundaries of <see cref="Generators"/>, then its boundary-biased random values;</item>
/// <item><c>bool</c>: both values;</item>
/// <item>an open enum: every named value plus unnamed values, including the underlying type's <c>MinValue</c> and <c>MaxValue</c>;</item>
/// <item>a closed enum or class: every member and nothing else;</item>
/// <item>a record: its fields by these rules (every combination of the fields' boundary values).</item>
/// </list>
/// </summary>
internal sealed class Inputs(Values values)
{
    /// <summary>The boundary values of a type.</summary>
    public IReadOnlyList<object?> Boundaries(VirType type)
    {
        switch (type)
        {
            case PrimitiveType { Kind: VirPrimitive.Int32 }:
                return [.. Generators.Int32Boundaries.Cast<object?>()];
            case PrimitiveType { Kind: VirPrimitive.Int64 }:
                return [.. Generators.Int64Boundaries.Cast<object?>()];
            case PrimitiveType { Kind: VirPrimitive.Bool }:
                return [false, true];
        }
        var key = ((RefType)type).Key;
        var clr = values.Assembly.TypeOf(key);
        switch (values.Definition(key))
        {
            case EnumDefinition e:
                return [.. EnumValues(e).Select(v => Enum.ToObject(clr, v))];
            case ClosedDefinition c when clr.IsEnum:
                return [.. c.Members.Select(m => Enum.ToObject(clr, m.Value!.Value))];
            case ClosedDefinition c:
                return [.. c.Members.Select(m => CorpusAssembly.ReadStatic(clr, m.Name))];
            case RecordDefinition r:
                return [.. Combinations(r.Fields.Select(f => Boundaries(f.Type)).ToList()).Select(fields => Activator.CreateInstance(clr, fields))];
            default:
                throw new InvalidOperationException($"unknown definition for {key}");
        }
    }

    /// <summary>Random values of a type.</summary>
    public Gen<object?> Random(VirType type)
    {
        switch (type)
        {
            case PrimitiveType { Kind: VirPrimitive.Int32 }:
                return Generators.Int32Values.Select(v => (object?)v);
            case PrimitiveType { Kind: VirPrimitive.Int64 }:
                return Generators.Int64Values.Select(v => (object?)v);
            case PrimitiveType { Kind: VirPrimitive.Bool }:
                return Gen.Elements<object?>(false, true);
        }
        var key = ((RefType)type).Key;
        var clr = values.Assembly.TypeOf(key);
        switch (values.Definition(key))
        {
            case EnumDefinition e:
                {
                    var underlying = ((PrimitiveType)e.Underlying).Kind == VirPrimitive.Int32
                        ? Generators.Int32Values.Select(v => (long)v)
                        : Generators.Int64Values;
                    var named = Gen.Elements<long>(e.Members.Select(m => m.Value).ToArray());
                    return Gen.Frequency<long>((1, named), (1, underlying)).Select(v => (object?)Enum.ToObject(clr, v));
                }
            case ClosedDefinition:
                return Gen.Elements<object?>(Boundaries(type).ToArray());
            case RecordDefinition r:
                return Sequence(r.Fields.Select(f => Random(f.Type)).ToList()).Select(fields => Activator.CreateInstance(clr, fields));
            default:
                throw new InvalidOperationException($"unknown definition for {key}");
        }
    }

    /// <summary>
    /// The boundary inputs of a function: with up to three parameters, every combination of the parameters' boundary
    /// values; with more, each parameter's boundary values in turn with the others at their first boundary value.
    /// </summary>
    public IReadOnlyList<object?[]> BoundaryInputs(IReadOnlyList<VirType> parameters)
    {
        var lists = parameters.Select(Boundaries).ToList();
        if (parameters.Count <= 3)
        {
            return [.. Combinations(lists)];
        }
        var first = lists.Select(l => l[0]).ToArray();
        var result = new List<object?[]>();
        for (int i = 0; i < lists.Count; i++)
        {
            foreach (var v in lists[i])
            {
                var input = (object?[])first.Clone();
                input[i] = v;
                result.Add(input);
            }
        }
        return result;
    }

    /// <summary><paramref name="count"/> random inputs of a function, from a fresh seed.</summary>
    public IReadOnlyList<object?[]> RandomInputs(IReadOnlyList<VirType> parameters, int count) =>
        count == 0 ? [] : Sequence(parameters.Select(Random).ToList()).Sample(count, size: 50);

    /// <summary>
    /// The open enum's named values, then the unnamed ones: the underlying type's <c>MinValue</c> and <c>MaxValue</c>,
    /// -1, and one past the largest named value.
    /// </summary>
    public static IEnumerable<long> EnumValues(EnumDefinition e)
    {
        var named = e.Members.Select(m => m.Value).ToList();
        var is32 = ((PrimitiveType)e.Underlying).Kind == VirPrimitive.Int32;
        long[] unnamed = [is32 ? int.MinValue : long.MinValue, is32 ? int.MaxValue : long.MaxValue, -1, named.Count == 0 ? 0 : named.Max() + 1];
        return named.Concat(unnamed.Where(v => !named.Contains(v))).Distinct();
    }

    private static IEnumerable<object?[]> Combinations(IReadOnlyList<IReadOnlyList<object?>> lists)
    {
        IEnumerable<object?[]> result = [[]];
        foreach (var list in lists)
        {
            var current = result;
            result = current.SelectMany(prefix => list.Select(v => (object?[])[.. prefix, v]));
        }
        return result;
    }

    private static Gen<object?[]> Sequence(IReadOnlyList<Gen<object?>> gens)
    {
        var result = Gen.Constant(Array.Empty<object?>());
        foreach (var gen in gens)
        {
            var prefix = result;
            result = prefix.SelectMany(p => gen.Select(v => (object?[])[.. p, v]));
        }
        return result;
    }
}
