using System.Globalization;
using Warrant.Vir;

namespace Warrant.Engine.Reports;

/// <summary>
/// The subject of a <see cref="VirAssumptionKind.MayThrow"/> assumption on an outcome (M6 KTD20, #70): what a method may
/// throw, where, and through which call. Sites are VIR node IDs, as an outcome's other positions are (M5b KTD7), so a
/// cached outcome stays right when code moves; the report maps them to lines through the units' span tables.
/// </summary>
/// <remarks>
/// <see cref="Format"/> writes the fields joined by <c>|</c>, leaving out trailing empty ones, so a bare type key such as
/// <c>T:System.ArgumentException</c> is a subject with no site. A documentation-comment ID never contains <c>|</c>.
/// </remarks>
/// <param name="Thrown">
/// The thrown type's key, e.g. <c>T:System.ArgumentException</c>, for an explicit <c>throw</c>; for an exception
/// propagated from a dependency (<c>ClrExn.external</c>), the key of the dependency member whose call raised it.
/// </param>
/// <param name="Node">The node of the <c>throw</c>, or of the dependency call, in unit <paramref name="In"/>; null when unknown.</param>
/// <param name="In">
/// The key of the unit <paramref name="Node"/> belongs to, for a throw in a verified callee; null for the unit the
/// assumption is recorded for.
/// </param>
/// <param name="Via">
/// For a throw propagated through a verified callee, the key of the callee this unit calls; null for the unit's own throw.
/// </param>
/// <param name="CallNode">The node of the call to <paramref name="Via"/> in the unit the assumption is recorded for.</param>
public sealed record MayThrowSubject(string Thrown, int? Node = null, string? In = null, string? Via = null, int? CallNode = null)
{
    private const char Separator = '|';

    /// <summary>The subject string an <see cref="Service.AssumptionDto"/> carries.</summary>
    /// <returns>The fields joined by <c>|</c>, without trailing empty ones.</returns>
    public string Format()
    {
        string?[] fields = [Thrown, Number(Node), In, Via, Number(CallNode)];
        int count = fields.Length;
        while (count > 1 && string.IsNullOrEmpty(fields[count - 1]))
        {
            count--;
        }
        return string.Join(Separator, fields.Take(count).Select(f => f ?? ""));
    }

    /// <summary>Reads a subject <see cref="Format"/> wrote.</summary>
    /// <param name="subject">The subject.</param>
    /// <returns>The parts.</returns>
    /// <exception cref="FormatException">The subject has more than five fields, no thrown key, or a node that is not a number.</exception>
    public static MayThrowSubject Parse(string subject)
    {
        ArgumentNullException.ThrowIfNull(subject);
        var fields = subject.Split(Separator);
        if (fields.Length > 5 || fields[0].Length == 0)
        {
            throw new FormatException($"Not a may-throw subject: '{subject}'.");
        }
        string? Field(int i) => i < fields.Length && fields[i].Length > 0 ? fields[i] : null;
        int? Node(int i) => Field(i) is { } text
            ? int.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture, out var n) ? n : throw new FormatException($"Not a node ID in may-throw subject '{subject}'.")
            : null;
        return new MayThrowSubject(fields[0], Node(1), Field(2), Field(3), Node(4));
    }

    private static string? Number(int? n) => n?.ToString(CultureInfo.InvariantCulture);
}
