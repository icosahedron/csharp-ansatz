using System.Reflection;
using System.Runtime.Loader;

namespace Warrant.Vir.Tests;

/// <summary>
/// Loads the netstandard2.0 build of Warrant.Vir into its own load context, rebuilds each sample unit
/// from that build's types, and checks that its writer produces the same bytes as the net10.0 build's.
/// </summary>
public class NetstandardWriterTests
{
    private static readonly Lazy<Assembly> Netstandard = new(Load);

    public static TheoryData<string> UnitKeys() => RoundTripTests.UnitKeys();

    [Fact]
    public void TheLoadedAssemblyIsTheNetstandardBuild()
    {
        var framework = Netstandard.Value.GetCustomAttribute<System.Runtime.Versioning.TargetFrameworkAttribute>();
        Assert.Equal(".NETStandard,Version=v2.0", framework?.FrameworkName);
        Assert.Null(Netstandard.Value.GetType("Warrant.Vir.VirReader"));
    }

    [Theory]
    [MemberData(nameof(UnitKeys))]
    public void BothBuildsWriteTheSameBytes(string key)
    {
        var unit = Samples.All().Single(u => u.Key == key);
        var asm = Netstandard.Value;
        var clone = Clone(unit, asm);
        var write = asm.GetType("Warrant.Vir.VirWriter", throwOnError: true)!.GetMethod("Write")!;

        var bytes = (byte[])write.Invoke(null, [clone])!;

        Assert.Equal(VirWriter.Write(unit), bytes);
    }

    private static Assembly Load()
    {
        var path = typeof(NetstandardWriterTests).Assembly.GetCustomAttributes<AssemblyMetadataAttribute>()
            .Single(a => a.Key == "VirNetstandardAssembly").Value!;
        var context = new AssemblyLoadContext("Warrant.Vir.netstandard2.0", isCollectible: false);
        return context.LoadFromAssemblyPath(Path.GetFullPath(path));
    }

    /// <summary>Rebuilds a VIR value from the other build's types, through each record's primary constructor.</summary>
    private static object? Clone(object? value, Assembly target)
    {
        switch (value)
        {
            case null:
                return null;
            case string or int or long or bool or System.Numerics.BigInteger:
                return value;
        }
        var type = value.GetType();
        if (type.IsEnum)
        {
            return Enum.ToObject(MapType(type, target), Convert.ToInt32(value, System.Globalization.CultureInfo.InvariantCulture));
        }
        if (type.IsGenericType && type.GetGenericTypeDefinition() == typeof(VirList<>))
        {
            var element = MapType(type.GetGenericArguments()[0], target);
            var items = ((System.Collections.IEnumerable)value).Cast<object?>().Select(v => Clone(v, target)).ToArray();
            var array = Array.CreateInstance(element, items.Length);
            Array.Copy(items, array, items.Length);
            return Activator.CreateInstance(MapType(type, target), array);
        }
        var mapped = MapType(type, target);
        var ctor = mapped.GetConstructors()
            .Where(c => c.GetParameters().All(p => p.ParameterType != mapped))
            .OrderByDescending(c => c.GetParameters().Length)
            .First();
        var args = ctor.GetParameters()
            .Select(p => Clone(type.GetProperty(p.Name!)!.GetValue(value), target))
            .ToArray();
        return ctor.Invoke(args);
    }

    private static Type MapType(Type type, Assembly target)
    {
        if (type.Assembly != typeof(VirUnit).Assembly)
        {
            return type;
        }
        if (type.IsGenericType)
        {
            var definition = target.GetType(type.GetGenericTypeDefinition().FullName!, throwOnError: true)!;
            return definition.MakeGenericType(type.GetGenericArguments().Select(t => MapType(t, target)).ToArray());
        }
        return target.GetType(type.FullName!, throwOnError: true)!;
    }
}
