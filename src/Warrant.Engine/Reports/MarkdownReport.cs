using System.Text;
using Warrant.Vir;

namespace Warrant.Engine.Reports;

/// <summary>Renders an <see cref="AssumptionReport"/> as Markdown, in the layout docs/m4/07 shows.</summary>
public static class MarkdownReport
{
    /// <summary>Renders the report.</summary>
    /// <param name="report">The report.</param>
    /// <returns>The Markdown text, with <c>\n</c> line ends.</returns>
    public static string Render(AssumptionReport report)
    {
        ArgumentNullException.ThrowIfNull(report);
        var sb = new StringBuilder();
        sb.Append("# Assumption report\n\n");
        sb.Append("Kernel: ").Append(report.Kernel).Append(". Bundle: ").Append(report.Bundle).Append(".\n\n");
        sb.Append("```text\n");
        int width = report.Units.Select(u => u.DisplayName.Length).DefaultIfEmpty(0).Max() + 2;
        bool first = true;
        foreach (var unit in report.Units)
        {
            if (!first)
            {
                sb.Append('\n');
            }
            first = false;
            sb.Append(unit.DisplayName.PadRight(width)).Append(Status(unit).PadRight(13)).Append('(').Append(Parenthetical(unit, report)).Append(")\n");
            if (unit.Claim is { } claim)
            {
                sb.Append("  Claim: ").Append(claim).Append('\n');
            }
            if (unit.Detail is { } detail)
            {
                sb.Append("  Reason: ").Append(detail).Append('\n');
            }
            foreach (var group in unit.Assumptions.GroupBy(Heading))
            {
                sb.Append("  Assumed (").Append(group.Key).Append("):\n");
                foreach (var a in group)
                {
                    sb.Append("    - ").Append(a.Text).Append('\n');
                }
            }
            sb.Append("  Assumed (global):\n");
            foreach (var g in unit.Global.Concat(report.Global))
            {
                sb.Append("    - ").Append(g).Append('\n');
            }
        }
        sb.Append("```\n");
        return sb.ToString();
    }

    private static string Status(UnitReport unit) => unit.Status switch
    {
        ReportStatus.Translated => "TRANSLATED",
        ReportStatus.Verified => "VERIFIED",
        _ => "FAILED",
    };

    private static string Parenthetical(UnitReport unit, AssumptionReport report)
    {
        var context = $"kernel: {report.Kernel}, bundle: {report.Bundle}";
        return unit.Status switch
        {
            ReportStatus.Verified => $"by {unit.By}; {context}",
            ReportStatus.Failed => $"{unit.Outcome}; {context}",
            _ => context,
        };
    }

    private static string Heading(ReportAssumption a) =>
        a.Inherited ? $"from {a.From}"
        : a.Kind switch
        {
            VirAssumptionKind.NonNull => "parameters",
            VirAssumptionKind.Closed or VirAssumptionKind.ClosedEquality or VirAssumptionKind.ReferencedSource => "types",
            VirAssumptionKind.CallerPrecondition or VirAssumptionKind.CalleeContract or VirAssumptionKind.ExternalContract => "contracts",
            VirAssumptionKind.MayThrow => "exceptions",
            _ => throw new InvalidOperationException($"Unknown assumption kind {a.Kind}."),
        };
}
