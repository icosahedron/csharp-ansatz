using System.Collections.Immutable;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using Warrant.Vir;

namespace Warrant.Engine.Reports;

/// <summary>
/// Renders an <see cref="AssumptionReport"/> as JSON, and reads it back. The output is deterministic: properties in a
/// fixed order, units and assumptions in report order, indented with <c>\n</c> line ends, no BOM.
/// </summary>
public static class JsonReport
{
    private static readonly JsonWriterOptions WriterOptions = new()
    {
        Indented = true,
        NewLine = "\n",
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    /// <summary>Renders the report.</summary>
    /// <param name="report">The report.</param>
    /// <returns>The JSON text, ending in a newline.</returns>
    public static string Render(AssumptionReport report)
    {
        ArgumentNullException.ThrowIfNull(report);
        using var stream = new MemoryStream();
        using (var w = new Utf8JsonWriter(stream, WriterOptions))
        {
            w.WriteStartObject();
            w.WriteString("kernel", report.Kernel);
            w.WriteString("bundle", report.Bundle);
            w.WriteStartArray("global");
            foreach (var g in report.Global)
            {
                w.WriteStringValue(g);
            }
            w.WriteEndArray();
            w.WriteStartArray("units");
            foreach (var u in report.Units)
            {
                w.WriteStartObject();
                w.WriteString("key", u.Key);
                w.WriteString("kind", KindName(u.Kind));
                w.WriteString("displayName", u.DisplayName);
                w.WriteString("status", StatusName(u.Status));
                w.WriteString("outcome", u.Outcome);
                WriteOptional(w, "by", u.By);
                WriteOptional(w, "claim", u.Claim);
                WriteOptional(w, "detail", u.Detail);
                w.WriteStartArray("assumptions");
                foreach (var a in u.Assumptions)
                {
                    w.WriteStartObject();
                    w.WriteString("kind", AssumptionName(a.Kind));
                    w.WriteString("subject", a.Subject);
                    w.WriteString("from", a.From);
                    w.WriteBoolean("inherited", a.Inherited);
                    w.WriteString("text", a.Text);
                    w.WriteEndObject();
                }
                w.WriteEndArray();
                if (!u.Global.IsEmpty)
                {
                    w.WriteStartArray("global");
                    foreach (var g in u.Global)
                    {
                        w.WriteStringValue(g);
                    }
                    w.WriteEndArray();
                }
                w.WriteEndObject();
            }
            w.WriteEndArray();
            w.WriteEndObject();
        }
        return Encoding.UTF8.GetString(stream.ToArray()) + "\n";
    }

    /// <summary>Reads a report <see cref="Render"/> wrote.</summary>
    /// <param name="json">The JSON text.</param>
    /// <returns>The report.</returns>
    /// <exception cref="JsonException">The text is not a report.</exception>
    public static AssumptionReport Read(string json)
    {
        ArgumentNullException.ThrowIfNull(json);
        try
        {
            using var doc = JsonDocument.Parse(json);
            var root = doc.RootElement;
            var units = root.GetProperty("units").EnumerateArray().Select(u => new UnitReport(
                u.GetProperty("key").GetString()!,
                ParseKind(u.GetProperty("kind").GetString()!),
                u.GetProperty("displayName").GetString()!,
                ParseStatus(u.GetProperty("status").GetString()!),
                u.GetProperty("outcome").GetString()!,
                Optional(u, "by"),
                Optional(u, "claim"),
                Optional(u, "detail"),
                u.GetProperty("assumptions").EnumerateArray().Select(a => new ReportAssumption(
                    ParseAssumption(a.GetProperty("kind").GetString()!),
                    a.GetProperty("subject").GetString()!,
                    a.GetProperty("from").GetString()!,
                    a.GetProperty("inherited").GetBoolean(),
                    a.GetProperty("text").GetString()!)).ToImmutableArray())
            {
                Global = u.TryGetProperty("global", out var global) ? [.. global.EnumerateArray().Select(g => g.GetString()!)] : [],
            });
            return new AssumptionReport(
                root.GetProperty("kernel").GetString()!,
                root.GetProperty("bundle").GetString()!,
                root.GetProperty("global").EnumerateArray().Select(g => g.GetString()!).ToImmutableArray(),
                units.ToImmutableArray());
        }
        catch (Exception ex) when (ex is KeyNotFoundException or InvalidOperationException or ArgumentException)
        {
            throw new JsonException($"Not an assumption report: {ex.Message}", ex);
        }
    }

    private static void WriteOptional(Utf8JsonWriter w, string name, string? value)
    {
        if (value is null)
        {
            w.WriteNull(name);
        }
        else
        {
            w.WriteString(name, value);
        }
    }

    private static string? Optional(JsonElement e, string name) =>
        e.TryGetProperty(name, out var v) && v.ValueKind == JsonValueKind.String ? v.GetString() : null;

    private static string KindName(VirUnitKind kind) => kind switch
    {
        VirUnitKind.Function => "function",
        VirUnitKind.Theorem => "theorem",
        VirUnitKind.Type => "type",
        _ => throw new ArgumentException($"unit kind {kind} is not reported until M6 U12"),
    };

    private static VirUnitKind ParseKind(string s) => s switch
    {
        "function" => VirUnitKind.Function,
        "theorem" => VirUnitKind.Theorem,
        "type" => VirUnitKind.Type,
        _ => throw new ArgumentException($"unknown unit kind '{s}'"),
    };

    private static string StatusName(ReportStatus status) => status switch
    {
        ReportStatus.Translated => "translated",
        ReportStatus.Verified => "verified",
        _ => "failed",
    };

    private static ReportStatus ParseStatus(string s) => s switch
    {
        "translated" => ReportStatus.Translated,
        "verified" => ReportStatus.Verified,
        "failed" => ReportStatus.Failed,
        _ => throw new ArgumentException($"unknown status '{s}'"),
    };

    private static string AssumptionName(VirAssumptionKind kind) => kind switch
    {
        VirAssumptionKind.NonNull => "non-null",
        VirAssumptionKind.Closed => "closed",
        VirAssumptionKind.ClosedEquality => "closed-equality",
        VirAssumptionKind.ReferencedSource => "referenced-source",
        _ => throw new ArgumentException($"unknown assumption kind {kind}"),
    };

    private static VirAssumptionKind ParseAssumption(string s) => s switch
    {
        "non-null" => VirAssumptionKind.NonNull,
        "closed" => VirAssumptionKind.Closed,
        "closed-equality" => VirAssumptionKind.ClosedEquality,
        "referenced-source" => VirAssumptionKind.ReferencedSource,
        _ => throw new ArgumentException($"unknown assumption kind '{s}'"),
    };
}
