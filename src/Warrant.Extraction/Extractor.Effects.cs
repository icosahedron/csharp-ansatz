using Microsoft.CodeAnalysis;
using Warrant.Vir;

namespace Warrant.Extraction;

public static partial class Extractor
{
    internal sealed partial class Run
    {
        /// <summary>The construct <see cref="Effects"/> names for a call to a method that has <c>Spec.Requires</c>.</summary>
        private const string RequiresCall = "call to a method with Spec.Requires";

        /// <summary>
        /// KTD11's rejections, from the shared effect inference over the units still accepted (plan M6 U8): a contract on a
        /// recursive method, a recursive method that can raise, a <c>Spec</c> expression that calls a method that can raise
        /// (KTD26 as amended, #165), and a theorem whose statement can raise, by an operation of its own or through a method
        /// it calls (#164). Each names the construct and the callee that made the unit raising.
        /// </summary>
        private void RejectEffects()
        {
            var accepted = _candidates.Values
                .Where(c => c.Kind != VirUnitKind.Type && c.Rejection is null)
                .OrderBy(c => c.Key, StringComparer.Ordinal)
                .ToList();
            var analysis = Effects.Analyze(accepted.Where(c => c.Kind != VirUnitKind.Contract).Select(Provisional));
            foreach (var c in accepted)
            {
                c.Rejection = c.Kind switch
                {
                    VirUnitKind.Theorem => RaisingTheorem(c, analysis),
                    // A contract unit is its Spec calls alone, so only its claims can call something that raises (U18).
                    VirUnitKind.Contract => RaisingClaim(c, analysis),
                    _ => RaisingFunction(c, analysis),
                };
            }
        }

        /// <summary>A unit as effect inference reads it: its body or statement, without assumptions or dependencies.</summary>
        private VirUnit Provisional(Candidate c) =>
            c.Kind == VirUnitKind.Theorem
                ? VirUnit.Theorem(c.Key, c.Statement!, VirList<VirAssumption>.Empty, _context.Facts, VirList<string>.Empty, new VirList<VirParam>(c.Params))
                : VirUnit.Function(c.Key, new VirList<VirParam>(c.Params), c.Returns!, c.Body!, VirList<VirAssumption>.Empty, _context.Facts, VirList<string>.Empty);

        /// <summary>
        /// A theorem is a <c>Prop</c>, not a program, so nothing in its statement may raise (KTD11): Lean's total operations
        /// would make <c>a / 0 == 0</c> provable.
        /// </summary>
        private Rejection? RaisingTheorem(Candidate c, EffectAnalysis analysis)
        {
            if (analysis.CauseOf(c.Key) is not { } cause)
            {
                return null;
            }
            var name = Symbols.Display(c.Symbol);
            const string advice = "a theorem is a claim, not code that runs, so state the property as a Spec.Ensures on the method instead, or, for a property relating two calls, on a verified method that makes both calls";
            if (string.Equals(cause.Unit, c.Key, StringComparison.Ordinal))
            {
                return new Rejection(
                    DiagnosticIds.Unsupported,
                    cause.Construct,
                    At(c, cause.Node, c.Symbol),
                    $"{name}: the statement has {Describe(cause, own: true)}, which can raise an exception; {advice}.");
            }
            var callee = cause.Callee!;
            return new Rejection(
                DiagnosticIds.Unsupported,
                "theorem calling a raising method",
                At(c, FirstCallTo(c, callee), c.Symbol),
                $"{name}: the statement calls {Display(callee)}, which can raise an exception ({Describe(cause, own: false)}); {advice}.");
        }

        /// <summary>A function's KTD11 rejection, if it has one: recursion with a contract or with effects, or a raising call in a contract.</summary>
        private Rejection? RaisingFunction(Candidate c, EffectAnalysis analysis)
        {
            var name = Symbols.Display(c.Symbol);
            // A Spec.Requires is allowed (#256): each recursive call is checked against it. A Spec.Ensures is not yet.
            var contract = c.Body is BlockStmt block ? block.Stmts.FirstOrDefault(s => s is EnsuresStmt) : null;
            if (analysis.IsRecursive(c.Key) && contract is not null)
            {
                return new Rejection(
                    DiagnosticIds.Unsupported,
                    "contract on a recursive method",
                    At(c, contract, c.Symbol),
                    $"{name}: a recursive method takes no Spec.Ensures, because its recursive call cannot use its own contract before it is proved; a Spec.Requires is allowed.");
            }
            if (analysis.IsRecursive(c.Key) && analysis.CauseOf(c.Key) is { } cause)
            {
                bool own = string.Equals(cause.Unit, c.Key, StringComparison.Ordinal);
                return new Rejection(
                    DiagnosticIds.Unsupported,
                    "recursion with effects",
                    At(c, own ? cause.Node : FirstCallTo(c, cause.Callee!), c.Symbol),
                    $"{name}: a recursive method cannot raise an exception in M6, and this one can ({Describe(cause, own)}{(own ? "" : $", through {Display(cause.Callee!)}")}): its recursive call would sit inside the effect monad, where the decrease obligations cannot see it.");
            }

            return RaisingClaim(c, analysis);
        }

        /// <summary>A Spec expression is a Prop, so it may not call a program that can raise (KTD26 as amended, #165).</summary>
        private Rejection? RaisingClaim(Candidate c, EffectAnalysis analysis)
        {
            var name = Symbols.Display(c.Symbol);
            foreach (var claim in Claims(c))
            {
                foreach (var call in Descendants(claim).OfType<CallExpr>())
                {
                    if (analysis.CauseOf(call.Target) is { } raising)
                    {
                        return new Rejection(
                            DiagnosticIds.Unsupported,
                            "Spec expression calling a raising method",
                            At(c, call, c.Symbol),
                            $"{name}: a Spec.Requires or Spec.Ensures is a claim, not code that runs, so it cannot call {Display(call.Target)}, which can raise an exception ({Describe(raising, string.Equals(raising.Unit, call.Target, StringComparison.Ordinal))}).");
                    }
                }
            }
            return null;
        }

        /// <summary>The conditions of a function's <c>Spec.Requires</c> and <c>Spec.Ensures</c>.</summary>
        private static IEnumerable<VirExpr> Claims(Candidate c) =>
            c.Body is BlockStmt block
                ? block.Stmts.Select(s => s switch { RequiresStmt r => r.Condition, EnsuresStmt e => e.Condition, _ => null }).OfType<VirExpr>()
                : [];

        /// <summary>
        /// What makes a unit raising, for a message: the construct and the unit it is in, unless that is the unit the
        /// message is about (<paramref name="own"/>).
        /// </summary>
        private string Describe(RaiseCause cause, bool own)
        {
            var what = cause.Construct == RequiresCall && cause.Node is CallExpr call
                ? $"a call to {Display(call.Target)}, which has a Spec.Requires"
                : cause.Construct;
            return own ? what : $"{what} in {Display(cause.Unit)}";
        }

        private string Display(string key) => _candidates.TryGetValue(key, out var c) ? Symbols.Display(c.Symbol) : key;

        /// <summary>The first call in a unit's own VIR to <paramref name="callee"/>, in pre-order.</summary>
        private static CallExpr? FirstCallTo(Candidate c, string callee) =>
            VirTreeNodes(c).OfType<CallExpr>().FirstOrDefault(call => string.Equals(call.Target, callee, StringComparison.Ordinal));

        /// <summary>Where a node of a unit came from, or the unit's own declaration when the node has no source.</summary>
        private static Location? At(Candidate c, VirNode? node, ISymbol symbol) =>
            (node is null ? null : c.Walker?.SyntaxOf(node)?.GetLocation()) ?? Symbols.FirstLocation(symbol);
    }
}
