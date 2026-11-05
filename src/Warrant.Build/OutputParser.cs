using System;
using System.Globalization;
using System.Text;

namespace Warrant.Build;

/// <summary>What a <c>WRT1</c> record carries: a diagnostic, the goal block of the preceding diagnostic, or the summary.</summary>
internal enum RecordKind
{
    /// <summary>A diagnostic with a code and, usually, a location (<c>diag</c>).</summary>
    Diagnostic,

    /// <summary>The goal block of the preceding diagnostic (<c>goal</c>).</summary>
    Goal,

    /// <summary>The one-line summary of the run (<c>summary</c>).</summary>
    Summary,
}

/// <summary>A record's severity.</summary>
internal enum RecordSeverity
{
    /// <summary>Fails the build.</summary>
    Error,

    /// <summary>Reported, and the build continues.</summary>
    Warning,

    /// <summary>Informational.</summary>
    Info,
}

/// <summary>
/// One line of <c>warrant verify --format msbuild</c> output, decoded. Positions are 1-based, and 0 when unknown.
/// </summary>
/// <param name="Kind">The record kind.</param>
/// <param name="Severity">The severity.</param>
/// <param name="Code">The diagnostic code, such as <c>WRT0001</c>; empty for goals and summaries.</param>
/// <param name="File">The path as the compiler saw it; empty when there is no location.</param>
/// <param name="Line">The start line.</param>
/// <param name="Column">The start column.</param>
/// <param name="EndLine">The end line.</param>
/// <param name="EndColumn">The end column.</param>
/// <param name="Message">The unescaped message; the first line is self-contained.</param>
internal sealed record OutputRecord(
    RecordKind Kind,
    RecordSeverity Severity,
    string Code,
    string File,
    int Line,
    int Column,
    int EndLine,
    int EndColumn,
    string Message);

/// <summary>
/// Decodes the CLI-to-task record format: <c>WRT1</c>, kind, severity, code, file, line, column, end line, end column
/// and message, separated by tabs, with the message's backslash, newline, carriage return and tab escaped (KTD20).
/// </summary>
internal static class OutputParser
{
    /// <summary>The literal tag, with its tab, that starts every record line.</summary>
    public const string RecordPrefix = "WRT1\t";

    private const int FieldCount = 10;

    /// <summary>
    /// Decodes <paramref name="line"/> as a record. Returns null for ordinary output, which is any line that does not
    /// start with <see cref="RecordPrefix"/> or that is not a well-formed record.
    /// </summary>
    /// <param name="line">One line of the CLI's standard output, without its line terminator.</param>
    /// <returns>The record, or null.</returns>
    public static OutputRecord? Parse(string line)
    {
        if (line is null || !line.StartsWith(RecordPrefix, StringComparison.Ordinal))
        {
            return null;
        }

        // The message escapes its tabs, so a record has exactly ten fields.
        var fields = line.Split('\t');
        if (fields.Length != FieldCount
            || !TryKind(fields[1], out var kind)
            || !TrySeverity(fields[2], out var severity)
            || !TryPosition(fields[5], out var startLine)
            || !TryPosition(fields[6], out var column)
            || !TryPosition(fields[7], out var endLine)
            || !TryPosition(fields[8], out var endColumn))
        {
            return null;
        }

        return new OutputRecord(kind, severity, fields[3], fields[4], startLine, column, endLine, endColumn, Unescape(fields[9]));
    }

    /// <summary>
    /// Reverses the message escaping: <c>\\</c>, <c>\n</c>, <c>\r</c> and <c>\t</c>. Any other backslash is kept.
    /// </summary>
    /// <param name="text">The escaped message field.</param>
    /// <returns>The message.</returns>
    public static string Unescape(string text)
    {
        if (text.IndexOf('\\') < 0)
        {
            return text;
        }

        var result = new StringBuilder(text.Length);
        for (var i = 0; i < text.Length; i++)
        {
            var c = text[i];
            if (c != '\\' || i + 1 == text.Length)
            {
                result.Append(c);
                continue;
            }

            var decoded = text[i + 1] switch
            {
                '\\' => '\\',
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                _ => (char?)null,
            };
            if (decoded is { } d)
            {
                result.Append(d);
                i++;
            }
            else
            {
                result.Append(c);
            }
        }

        return result.ToString();
    }

    private static bool TryKind(string field, out RecordKind kind)
    {
        switch (field)
        {
            case "diag":
                kind = RecordKind.Diagnostic;
                return true;
            case "goal":
                kind = RecordKind.Goal;
                return true;
            case "summary":
                kind = RecordKind.Summary;
                return true;
            default:
                kind = default;
                return false;
        }
    }

    private static bool TrySeverity(string field, out RecordSeverity severity)
    {
        switch (field)
        {
            case "error":
                severity = RecordSeverity.Error;
                return true;
            case "warning":
                severity = RecordSeverity.Warning;
                return true;
            case "info":
                severity = RecordSeverity.Info;
                return true;
            default:
                severity = default;
                return false;
        }
    }

    private static bool TryPosition(string field, out int value) =>
        int.TryParse(field, NumberStyles.None, CultureInfo.InvariantCulture, out value);
}

