using System.Collections.Immutable;
using System.Globalization;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>
/// Turns a compilation into VIR units and diagnostics, enforcing the M4 subset (docs/m4/03).
/// </summary>
public static partial class Extractor
{
    /// <summary>The extractor version recorded in every unit's <c>facts</c>.</summary>
    public const string Version = "0.1.0";

    private const string DependsOnRejected = "depends on a rejected unit";

    private const string PreprocessorConditional = "preprocessor conditional";

    /// <summary>The most <c>#if</c> symbols extraction combines: 2^6 = 64 extractions.</summary>
    private const int MaxConditionalSymbols = 6;

    /// <summary>The Roslyn version recorded in <c>facts</c>: the loaded compiler's assembly version, as <c>major.minor.build</c>.</summary>
    public static string RoslynVersion
    {
        get
        {
            var v = typeof(CSharpCompilation).Assembly.GetName().Version!;
            return string.Format(CultureInfo.InvariantCulture, "{0}.{1}.{2}", v.Major, v.Minor, v.Build);
        }
    }

    /// <summary>
    /// Extracts every <c>[Verified]</c> member, <c>[Theorem]</c>, and record, enum or closed type they use, comparing every
    /// combination of the <c>#if</c> symbols (M4's settings, for a compilation without a build's defines).
    /// A compilation with errors gives no units, only its errors.
    /// </summary>
    /// <param name="compilation">The compilation, normally from <c>Warrant.Frontend.CompilationFactory</c>.</param>
    /// <param name="cancellationToken">Cancels the extraction.</param>
    /// <returns>The units in dependency order, and the diagnostics.</returns>
    public static ExtractionResult Extract(CSharpCompilation compilation, CancellationToken cancellationToken = default) =>
        Extract(compilation, null, cancellationToken);

    /// <summary>
    /// Extracts every <c>[Verified]</c> member, <c>[Theorem]</c>, and record, enum or closed type they use.
    /// A compilation with errors gives no units, only its errors.
    /// </summary>
    /// <param name="compilation">The compilation, normally from <c>Warrant.Frontend.CompilationFactory</c>.</param>
    /// <param name="options">Whether the compilation has a build's defines, and whether to compare <c>#if</c> combinations anyway; null for M4's settings.</param>
    /// <param name="cancellationToken">Cancels the extraction.</param>
    /// <returns>The units in dependency order, and the diagnostics.</returns>
    public static ExtractionResult Extract(CSharpCompilation compilation, ExtractionOptions? options, CancellationToken cancellationToken = default)
    {
        if (compilation is null)
        {
            throw new ArgumentNullException(nameof(compilation));
        }
        options ??= ExtractionOptions.Default;
        // A referenced project's source is one target framework's build of it, while a multi-targeted project
        // (KeepConditionalCheck) ships for every framework, whose builds of the referenced project can differ. So its
        // closed classes are used only when the run is for one configuration (#32).
        var referencedSource = options.KeepConditionalCheck ? null : options.ReferencedSource;
        // With a build's defines (from Csc, KTD21), the code is translated under that build's configuration only.
        if (options.BuildDefines && !options.KeepConditionalCheck)
        {
            return ExtractOne(compilation, referencedSource, cancellationToken);
        }
        // Otherwise code under #if could be code no build runs, or could add an overload or a type that changes what
        // other code binds to. So every combination of the symbols the #if conditions test is extracted, and a unit is
        // kept only if its VIR is the same in every combination that compiles. A combination that does not compile is
        // not a real build. A multi-targeted build keeps the check, so code that differs between its target frameworks
        // is rejected rather than verified for one; the symbols no condition tests keep the build's values.
        var symbols = ConditionalSymbols(compilation, cancellationToken);
        if (symbols.Count == 0)
        {
            return ExtractOne(compilation, referencedSource, cancellationToken);
        }
        if (symbols.Count > MaxConditionalSymbols)
        {
            var at = compilation.SyntaxTrees
                .SelectMany(t => t.GetRoot(cancellationToken).DescendantTrivia())
                .First(t => t.IsKind(SyntaxKind.IfDirectiveTrivia));
            var tooMany = new ExtractionDiagnostic(
                DiagnosticIds.Unsupported,
                ExtractionSeverity.Error,
                PreprocessorConditional,
                null,
                Symbols.Span(at.GetLocation()),
                $"M4 combines at most {MaxConditionalSymbols} {PreprocessorConditional} symbols; this compilation tests {string.Join(", ", symbols)}.");
            return new ExtractionResult([], [tooMany], hasCompileErrors: false);
        }

        // The compilation as given comes first, so it is the reference the kept units are taken from.
        var given = Defined(compilation, symbols);
        var combinations = new List<List<string>> { given };
        for (int mask = 0; mask < 1 << symbols.Count; mask++)
        {
            var defined = symbols.Where((_, i) => (mask & (1 << i)) != 0).ToList();
            if (!defined.SequenceEqual(given, StringComparer.Ordinal))
            {
                combinations.Add(defined);
            }
        }
        var results = new List<ExtractionResult>();
        ExtractionResult? firstFailure = null;
        foreach (var defined in combinations)
        {
            var result = ExtractOne(
                ReferenceEquals(defined, given) ? compilation : WithSymbols(compilation, symbols, defined, cancellationToken),
                referencedSource,
                cancellationToken);
            if (result.HasCompileErrors)
            {
                firstFailure ??= result;
            }
            else
            {
                results.Add(result);
            }
        }
        return results.Count == 0 ? firstFailure! : Agreeing(results, symbols);
    }

    private static ExtractionResult ExtractOne(
        CSharpCompilation compilation, Func<string, CSharpCompilation?>? referencedSource, CancellationToken cancellationToken)
    {
        // As in CompilationFactory.Failure, a warning made an error is not one: Csc may have suppressed it, and it does not
        // change what the code means.
        var errors = compilation.GetDiagnostics(cancellationToken)
            .Where(d => d.Severity == DiagnosticSeverity.Error && !d.IsWarningAsError)
            .Select(d => new ExtractionDiagnostic(
                d.Id, ExtractionSeverity.Error, null, null, Symbols.Span(d.Location), d.GetMessage(CultureInfo.InvariantCulture)))
            .ToList();
        if (errors.Count > 0)
        {
            return new ExtractionResult([], Sort(errors), hasCompileErrors: true);
        }
        return new Run(compilation, cancellationToken, referencedSource: referencedSource).Execute();
    }

    /// <summary>The symbols any <c>#if</c> or <c>#elif</c> condition in the compilation tests, sorted ordinally.</summary>
    private static List<string> ConditionalSymbols(CSharpCompilation compilation, CancellationToken cancellationToken) =>
        compilation.SyntaxTrees
            .SelectMany(t => t.GetRoot(cancellationToken).DescendantTrivia())
            .Where(t => t.IsKind(SyntaxKind.IfDirectiveTrivia) || t.IsKind(SyntaxKind.ElifDirectiveTrivia))
            .Select(t => (ConditionalDirectiveTriviaSyntax)t.GetStructure()!)
            .SelectMany(d => d.Condition.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>())
            .Select(i => i.Identifier.ValueText)
            .Distinct(StringComparer.Ordinal)
            .OrderBy(n => n, StringComparer.Ordinal)
            .ToList();

    /// <summary>The tested symbols the compilation's trees define, sorted ordinally.</summary>
    private static List<string> Defined(CSharpCompilation compilation, List<string> symbols)
    {
        var names = new HashSet<string>(
            compilation.SyntaxTrees.SelectMany(t => ((CSharpParseOptions)t.Options).PreprocessorSymbolNames), StringComparer.Ordinal);
        return symbols.Where(names.Contains).ToList();
    }

    /// <summary>
    /// The compilation with every tree parsed again so that, of the tested <paramref name="symbols"/>, exactly
    /// <paramref name="defined"/> are defined; the symbols no condition tests keep the build's values.
    /// </summary>
    private static CSharpCompilation WithSymbols(
        CSharpCompilation compilation, List<string> symbols, List<string> defined, CancellationToken cancellationToken)
    {
        var trees = compilation.SyntaxTrees.Select(t =>
        {
            var options = (CSharpParseOptions)t.Options;
            var names = options.PreprocessorSymbolNames
                .Where(n => !symbols.Contains(n, StringComparer.Ordinal))
                .Concat(defined)
                .Distinct(StringComparer.Ordinal);
            return CSharpSyntaxTree.ParseText(t.GetText(cancellationToken), options.WithPreprocessorSymbols(names), t.FilePath, cancellationToken);
        });
        return compilation.RemoveAllSyntaxTrees().AddSyntaxTrees(trees);
    }

    /// <summary>
    /// The first result without the units whose VIR differs in another result, or that depend on one; with the warnings
    /// of every result, since a WRT0008 in any build is a way to break a closed assumption.
    /// </summary>
    private static ExtractionResult Agreeing(List<ExtractionResult> results, List<string> symbols)
    {
        var reference = results[0];
        var diagnostics = reference.Diagnostics.ToList();
        var rejected = new HashSet<string>(StringComparer.Ordinal);
        var kept = new List<ExtractedUnit>();

        // Units come dependencies first, so a rejected dependency is already in the set when its user is reached.
        foreach (var unit in reference.Units)
        {
            var vir = VirWriter.Write(unit.Unit);
            bool differs = results.Skip(1).Any(r => r.Find(unit.Key) is not { } other || !vir.AsSpan().SequenceEqual(VirWriter.Write(other.Unit)));
            var dependency = unit.Unit.Deps.FirstOrDefault(rejected.Contains);
            if (differs)
            {
                rejected.Add(unit.Key);
                diagnostics.Add(new ExtractionDiagnostic(
                    DiagnosticIds.Unsupported,
                    ExtractionSeverity.Error,
                    PreprocessorConditional,
                    unit.Key,
                    unit.Location,
                    $"{unit.DisplayName} translates differently depending on which of {string.Join(", ", symbols)} the build defines."));
            }
            else if (dependency is not null)
            {
                rejected.Add(unit.Key);
                diagnostics.Add(new ExtractionDiagnostic(
                    DiagnosticIds.Unsupported,
                    ExtractionSeverity.Error,
                    DependsOnRejected,
                    unit.Key,
                    unit.Location,
                    $"{unit.DisplayName} depends on {dependency}, which is rejected."));
            }
            else
            {
                kept.Add(unit);
            }
        }
        foreach (var warning in results.Skip(1).SelectMany(r => r.Diagnostics).Where(d => d.Severity == ExtractionSeverity.Warning))
        {
            if (!diagnostics.Contains(warning))
            {
                diagnostics.Add(warning);
            }
        }
        // WRT0013 is about a unit that is translated (#239): one a combination rejects, or that does not agree across
        // combinations, gets none, though a combination in which it cannot raise reported it.
        var keptKeys = new HashSet<string>(kept.Select(u => u.Key), StringComparer.Ordinal);
        diagnostics.RemoveAll(d => d.Id == DiagnosticIds.IneffectiveSpec && (d.MemberKey is null || !keptKeys.Contains(d.MemberKey)));
        return new ExtractionResult(kept, Sort(diagnostics), hasCompileErrors: false);
    }

    /// <summary>The language version as <c>facts</c> records it: <c>14</c> for C# 14.0, <c>7.3</c> for C# 7.3.</summary>
    /// <param name="version">The effective language version.</param>
    /// <returns>The version text.</returns>
    public static string LanguageText(LanguageVersion version)
    {
        var text = version.ToDisplayString();
        return text.EndsWith(".0", StringComparison.Ordinal) ? text.Substring(0, text.Length - 2) : text;
    }

    /// <summary>Sorts diagnostics as <see cref="ExtractionResult.Diagnostics"/> is: by file, line, column, ID, member and construct.</summary>
    internal static List<ExtractionDiagnostic> Sorted(List<ExtractionDiagnostic> diagnostics) => Sort(diagnostics);

    private static List<ExtractionDiagnostic> Sort(List<ExtractionDiagnostic> diagnostics)
    {
        diagnostics.Sort((a, b) =>
        {
            int c = string.CompareOrdinal(a.Location?.Path, b.Location?.Path);
            if (c == 0)
            {
                c = (a.Location?.StartLine ?? 0).CompareTo(b.Location?.StartLine ?? 0);
            }
            if (c == 0)
            {
                c = (a.Location?.StartColumn ?? 0).CompareTo(b.Location?.StartColumn ?? 0);
            }
            if (c == 0)
            {
                c = string.CompareOrdinal(a.Id, b.Id);
            }
            if (c == 0)
            {
                c = string.CompareOrdinal(a.MemberKey, b.MemberKey);
            }
            if (c == 0)
            {
                c = string.CompareOrdinal(a.Construct, b.Construct);
            }
            return c;
        });
        return diagnostics;
    }

    /// <summary>A member or type that may become a unit.</summary>
    private sealed class Candidate
    {
        public Candidate(string key, ISymbol symbol, VirUnitKind kind)
        {
            Key = key;
            Symbol = symbol;
            Kind = kind;
        }

        public string Key { get; }

        public ISymbol Symbol { get; }

        /// <summary>
        /// The symbol the unit is shown as, when not <see cref="Symbol"/>: a contract unit is the interface member whose
        /// contract it states (M6 U20), so reports name <c>IPaymentStore.GetPayment</c>, not the contract class.
        /// </summary>
        public ISymbol? DisplaySymbol { get; init; }

        public VirUnitKind Kind { get; }

        public Walker? Walker { get; set; }

        public SortedSet<string> Deps { get; set; } = new(StringComparer.Ordinal);

        public SortedSet<string> Calls { get; set; } = new(StringComparer.Ordinal);

        public Rejection? Rejection { get; set; }

        public List<IParameterSymbol> ParameterSymbols { get; } = [];

        public List<VirParam> Params { get; } = [];

        public VirType? Returns { get; set; }

        public string? Self { get; set; }

        public VirNode? Body { get; set; }

        public VirExpr? Statement { get; set; }

        public VirList<TacticNode>? Script { get; set; }

        public VirBudget? Budget { get; set; }

        public TypeBuild? Type { get; set; }
    }

    /// <summary>One extraction: the whole compilation (<see cref="Execute"/>), or one member's closure (<see cref="ExecuteFor"/>).</summary>
    internal sealed partial class Run
    {
        private readonly CSharpCompilation _compilation;
        private readonly CancellationToken _cancellationToken;
        private readonly ExtractionContext _context;
        private readonly Dictionary<string, Candidate> _candidates = new(StringComparer.Ordinal);
        private readonly List<ExtractionDiagnostic> _diagnostics = [];
        private readonly Lazy<CompilationScan> _scan;
        private readonly Lazy<ProofIndex> _proofs;
        private readonly Lazy<ContractIndex> _contracts;

        /// <param name="compilation">The compilation.</param>
        /// <param name="cancellationToken">Cancels the run.</param>
        /// <param name="scan">The compilation's scan, shared by runs on the same compilation; null to make one when needed.</param>
        /// <param name="referencedSource">A referenced project's compilation by assembly name, for its closed classes (#32).</param>
        /// <param name="deferReferenced">
        /// Whether a closed class from another assembly is accepted unchecked, with no type unit: the analyzer's setting,
        /// since only the build has the referenced projects' source and checks such classes.
        /// </param>
        /// <param name="proofs">The compilation's <c>[ProofFor]</c> methods, shared by runs on the same compilation; null to index them when needed.</param>
        /// <param name="contracts">The compilation's <c>[ContractFor]</c> classes, shared by runs on the same compilation; null to index them when needed.</param>
        public Run(
            CSharpCompilation compilation,
            CancellationToken cancellationToken,
            Lazy<CompilationScan>? scan = null,
            Func<string, CSharpCompilation?>? referencedSource = null,
            bool deferReferenced = false,
            Lazy<ProofIndex>? proofs = null,
            Lazy<ContractIndex>? contracts = null)
        {
            _compilation = compilation;
            _cancellationToken = cancellationToken;
            _context = new ExtractionContext(compilation, Facts(compilation), referencedSource, deferReferenced);
            _scan = scan ?? new Lazy<CompilationScan>(() => CompilationScan.Run(_context, _cancellationToken), LazyThreadSafetyMode.None);
            _proofs = proofs ?? new Lazy<ProofIndex>(
                () => ProofIndex.Build(compilation, SortedSourceTypes(compilation), _cancellationToken), LazyThreadSafetyMode.None);
            _contracts = contracts ?? new Lazy<ContractIndex>(
                () => ContractIndex.Build(compilation, SortedSourceTypes(compilation), _cancellationToken), LazyThreadSafetyMode.None);
            _context.Contracts = _contracts;
        }

        public static VirFacts Facts(CSharpCompilation compilation) => new(
            compilation.Options.CheckOverflow ? VirOverflow.Checked : VirOverflow.Wrap,
            LanguageText(compilation.LanguageVersion),
            Version,
            RoslynVersion);

        public ExtractionResult Execute()
        {
            var types = SortedSourceTypes(_compilation);
            foreach (var member in AttributedMembers(types))
            {
                _cancellationToken.ThrowIfCancellationRequested();
                var candidate = BuildMember(member);
                _candidates.Add(candidate.Key, candidate);
            }

            // A contract unit for every interface member a verified method calls through a dependency (KTD10).
            foreach (var candidate in _candidates.Values.OrderBy(c => c.Key, StringComparer.Ordinal).ToList())
            {
                AddContracts(candidate);
            }

            // Type units for every type a unit uses, then the shape checks for every [Closed] type, used or not.
            AddUsedTypes();
            foreach (var type in types.Where(t => Symbols.IsClosed(t) && !_context.IsUsed(Symbols.Key(t))))
            {
                var build = TypeChecks.Build(_context, _scan, type);
                if (build.Rejection is { } r)
                {
                    Report(Symbols.Key(type), r);
                }
            }

            // The shape of every [ContractFor] class, used or not (KTD10).
            foreach (var contractClass in _contracts.Value.Classes)
            {
                ReportContractClass(contractClass);
            }

            // WRT0008 anywhere in the compilation (KTD18).
            _diagnostics.AddRange(UnnamedClosedValues(_scan.Value, types));

            RejectCycles();
            RejectEffects();
            RejectDependents();
            WarnIneffectiveSpecs();

            foreach (var c in _candidates.Values.Where(c => c.Rejection is not null).OrderBy(c => c.Key, StringComparer.Ordinal))
            {
                Report(c.Key, c.Rejection!);
            }
            foreach (var proof in _proofs.Value.Methods)
            {
                ReportProof(proof);
            }

            var accepted = _candidates.Values.Where(c => c.Rejection is null).ToDictionary(c => c.Key, StringComparer.Ordinal);
            var order = Graph.TopologicalOrder(accepted.Keys, k => accepted[k].Deps);
            var units = order.Select(k => Finish(accepted[k])).ToList();
            return new ExtractionResult(units, Sort(_diagnostics), hasCompileErrors: false);
        }

        /// <summary>
        /// The diagnostics of one member or type and of everything it reaches (M5b KTD22): the member, the members it calls
        /// or cites, transitively, and the types they use, checked with the same rules as <see cref="Execute"/>. That set is
        /// closed under calls and dependencies, so cycles and rejected dependencies come out as they do for the whole
        /// compilation. No units are built and no WRT0008 is reported.
        /// </summary>
        /// <param name="root">A <c>[Verified]</c> member, a <c>[Theorem]</c>, or a record, enum or closed type.</param>
        /// <param name="attributed">The compilation's <c>[Verified]</c> members and <c>[Theorem]</c>s by key.</param>
        /// <returns>The diagnostics, keyed by the members and types they are about.</returns>
        public List<ExtractionDiagnostic> ExecuteFor(ISymbol root, IReadOnlyDictionary<string, ISymbol> attributed)
        {
            // A [ProofFor] method is not a unit: what can be wrong with it is in the compilation's index (KTD16).
            if (ProofIndex.IsProofFor(root))
            {
                ReportProof((IMethodSymbol)root);
                if (!attributed.ContainsKey(Symbols.Key(root)))
                {
                    return Sort(_diagnostics);
                }
            }
            if (root is INamedTypeSymbol type)
            {
                _context.UseType(type);
            }
            else
            {
                var pending = new Queue<ISymbol>();
                pending.Enqueue(root);
                while (pending.Count > 0)
                {
                    _cancellationToken.ThrowIfCancellationRequested();
                    var member = pending.Dequeue();
                    var key = Symbols.Key(member);
                    if (_candidates.ContainsKey(key))
                    {
                        continue;
                    }
                    var candidate = BuildMember(member);
                    _candidates.Add(key, candidate);
                    var reachedFrom = new List<Candidate> { candidate };
                    reachedFrom.AddRange(AddContracts(candidate));
                    foreach (var reached in reachedFrom.SelectMany(c => c.Deps.Concat(c.Calls)))
                    {
                        if (!_candidates.ContainsKey(reached) && attributed.TryGetValue(reached, out var next))
                        {
                            pending.Enqueue(next);
                        }
                    }
                }
            }
            AddUsedTypes();
            RejectCycles();
            RejectEffects();
            RejectDependents();
            WarnIneffectiveSpecs();
            foreach (var c in _candidates.Values.Where(c => c.Rejection is not null).OrderBy(c => c.Key, StringComparer.Ordinal))
            {
                Report(c.Key, c.Rejection!);
            }
            return Sort(_diagnostics);
        }

        /// <summary>The diagnostic about a <c>[ContractFor]</c> class's shape, if it has not the contract shape (KTD10).</summary>
        /// <param name="contractClass">The class.</param>
        /// <returns>The diagnostics, keyed by the class.</returns>
        public List<ExtractionDiagnostic> ExecuteForContractClass(INamedTypeSymbol contractClass)
        {
            ReportContractClass(contractClass);
            return Sort(_diagnostics);
        }

        private void ReportContractClass(INamedTypeSymbol contractClass)
        {
            var key = Symbols.Key(contractClass);
            if (_contracts.Value.ProblemOf(key) is { } problem)
            {
                Report(key, problem);
            }
        }

        /// <summary>
        /// Builds the contract units of the interface members a candidate calls through its dependencies, those not built yet.
        /// </summary>
        /// <returns>The contract candidates built.</returns>
        private List<Candidate> AddContracts(Candidate candidate)
        {
            var added = new List<Candidate>();
            if (candidate.Rejection is not null)
            {
                // A rejected walk stopped part-way; the units it reached are not used by any unit that is kept.
                return added;
            }
            foreach (var pair in candidate.Walker?.ContractMembers ?? new Dictionary<string, Walker.ContractMember>())
            {
                if (!_candidates.ContainsKey(pair.Key))
                {
                    var contract = BuildContract(pair.Key, pair.Value);
                    _candidates.Add(pair.Key, contract);
                    added.Add(contract);
                }
            }
            return added;
        }

        /// <summary>
        /// The contract unit of an interface member (KTD10): its contract class member's parameters, result and leading
        /// <c>Spec.Requires</c> and <c>Spec.Ensures</c>, keyed by the interface member. It is rejected when another
        /// contract class's interface also has the member, which would give it two contracts.
        /// </summary>
        private Candidate BuildContract(string key, Walker.ContractMember contract)
        {
            var member = contract.Member;
            var implementation = contract.ContractClass.FindImplementationForInterfaceMember(member) as IMethodSymbol;
            var walker = new Walker(_context, inTheorem: false);
            var candidate = new Candidate(key, (ISymbol?)implementation ?? member, VirUnitKind.Contract)
            {
                DisplaySymbol = member,
                Walker = walker,
                Deps = walker.Deps,
                Calls = walker.Calls,
            };
            try
            {
                var covering = _contracts.Value.ClassesCovering(member);
                if (covering.Count > 1)
                {
                    throw new RejectedException(new Rejection(
                        DiagnosticIds.Unsupported,
                        "interface member with two contract classes",
                        Symbols.FirstLocation(covering[1]),
                        $"{Symbols.Display(member)} is a member of the interfaces of both {Symbols.Display(covering[0])} and {Symbols.Display(covering[1])}, so which contract it keeps is ambiguous."));
                }
                if (implementation is null || !SymbolEqualityComparer.Default.Equals(implementation.ContainingType, contract.ContractClass))
                {
                    throw new RejectedException(new Rejection(
                        DiagnosticIds.Unsupported,
                        "interface member without a contract member",
                        Symbols.FirstLocation(contract.ContractClass),
                        $"{Symbols.Display(contract.ContractClass)} has no member for {Symbols.Display(member)}, so nothing states what it is assumed to do."));
                }
                Parameters(candidate, walker, implementation, implementation.Parameters);
                bool annotated = implementation.ReturnNullableAnnotation == NullableAnnotation.Annotated;
                candidate.Returns = walker.MapReturn(implementation.ReturnType, annotated, ReturnTypeSyntax(implementation));
                walker.SetReturns(implementation.ReturnType, annotated);
                var declaration = implementation.DeclaringSyntaxReferences.First().GetSyntax(_cancellationToken);
                candidate.Body = walker.ContractBody(Body(implementation) as IMethodBodyOperation, declaration);
            }
            catch (RejectedException e)
            {
                candidate.Rejection = e.Rejection;
            }
            candidate.Deps.Remove(key);
            return candidate;
        }

        /// <summary>Reports why a <c>[ProofFor]</c> method supplies no script, if it supplies none.</summary>
        private void ReportProof(IMethodSymbol proof)
        {
            var key = Symbols.Key(proof);
            if (_proofs.Value.ProblemOf(key) is { } problem)
            {
                Report(key, problem);
            }
        }

        private void AddUsedTypes()
        {
            while (_context.TryNextType(out var type))
            {
                AddType(type);
            }
        }

        /// <summary>The compilation's source types, by key.</summary>
        public static List<INamedTypeSymbol> SortedSourceTypes(CSharpCompilation compilation) =>
            SourceTypes(compilation.Assembly.GlobalNamespace)
                .OrderBy(Symbols.Key, StringComparer.Ordinal)
                .ToList();

        /// <summary>The <c>[Verified]</c> members and <c>[Theorem]</c>s of the types, by key.</summary>
        public static IEnumerable<ISymbol> AttributedMembers(IEnumerable<INamedTypeSymbol> types) =>
            types
                .SelectMany(t => t.GetMembers())
                .Where(m => m is IMethodSymbol { MethodKind: not MethodKind.PropertyGet and not MethodKind.PropertySet } or IPropertySymbol)
                .Where(m => Symbols.IsVerified(m) || Symbols.IsTheorem(m))
                .OrderBy(Symbols.Key, StringComparer.Ordinal);

        /// <summary>WRT0008: the operations the scan found, then every closed enum without a member valued 0.</summary>
        public static IEnumerable<ExtractionDiagnostic> UnnamedClosedValues(CompilationScan scan, IEnumerable<INamedTypeSymbol> types)
        {
            foreach (var (operation, construct, member) in scan.UnnamedClosedValues)
            {
                yield return Warning(member, construct, operation.Syntax.GetLocation());
            }
            foreach (var type in types.Where(t => Symbols.Shape(t) == TypeShape.ClosedEnum && !TypeChecks.HasZero(t)))
            {
                yield return Warning(type, "closed enum without a member valued 0", Symbols.FirstLocation(type));
            }
        }

        private static IEnumerable<INamedTypeSymbol> SourceTypes(INamespaceSymbol ns)
        {
            foreach (var type in ns.GetTypeMembers())
            {
                foreach (var t in WithNested(type))
                {
                    yield return t;
                }
            }
            foreach (var child in ns.GetNamespaceMembers())
            {
                foreach (var t in SourceTypes(child))
                {
                    yield return t;
                }
            }
        }

        private static IEnumerable<INamedTypeSymbol> WithNested(INamedTypeSymbol type)
        {
            if (type.IsImplicitlyDeclared)
            {
                yield break;
            }
            yield return type;
            foreach (var nested in type.GetTypeMembers())
            {
                foreach (var t in WithNested(nested))
                {
                    yield return t;
                }
            }
        }

        private void Report(string key, Rejection r) =>
            _diagnostics.Add(new ExtractionDiagnostic(
                r.Id, ExtractionSeverity.Error, r.Construct, key, r.At is null ? null : Symbols.Span(r.At), r.Message));

        private static ExtractionDiagnostic Warning(ISymbol member, string construct, Location? at) =>
            new(
                DiagnosticIds.UnnamedClosedValue,
                ExtractionSeverity.Warning,
                construct,
                Symbols.Key(member),
                at is null ? null : Symbols.Span(at),
                $"{Symbols.Display(member)}: {construct} can give a [Closed] enum a value the model says cannot exist.");

        private void AddType(INamedTypeSymbol type)
        {
            // A referenced project's closed class is checked against its own declarations, in its own compilation (#32).
            var scan = _context.IsOwn(type)
                ? _scan
                : new Lazy<CompilationScan>(() => CompilationScan.OfDeclarations(_context, type, _cancellationToken), LazyThreadSafetyMode.None);
            var build = TypeChecks.Build(_context, scan, type);
            var candidate = new Candidate(Symbols.Key(type), type, VirUnitKind.Type)
            {
                Type = build,
                Deps = build.Deps,
                Rejection = build.Rejection,
            };
            _candidates.Add(candidate.Key, candidate);
        }

        private Candidate BuildMember(ISymbol member)
        {
            bool theorem = Symbols.IsTheorem(member);
            var walker = new Walker(_context, inTheorem: theorem);
            var candidate = new Candidate(Symbols.Key(member), member, theorem ? VirUnitKind.Theorem : VirUnitKind.Function)
            {
                Walker = walker,
                Deps = walker.Deps,
                Calls = walker.Calls,
            };
            try
            {
                if (theorem)
                {
                    Theorem(candidate, walker, (IMethodSymbol)member);
                }
                else
                {
                    Function(candidate, walker, member);
                }
            }
            catch (RejectedException e)
            {
                candidate.Rejection = e.Rejection;
            }
            // A call to itself is recursion, which RejectCycles checks through Calls; it is not a dependency.
            candidate.Deps.Remove(candidate.Key);
            return candidate;
        }

        private static RejectedException Reject(ISymbol member, string construct) =>
            new(new Rejection(
                DiagnosticIds.Unsupported, construct, Symbols.FirstLocation(member), $"{Symbols.Display(member)}: M4 does not support {construct}."));

        /// <summary>
        /// A theorem: <c>Prove.That(claim)</c>, optionally followed by <c>.By(...)</c>. Its parameters are universally
        /// quantified (KTD17), and <c>[Theorem(...)]</c>'s named arguments are its budgets (KTD24).
        /// </summary>
        private void Theorem(Candidate candidate, Walker walker, IMethodSymbol method)
        {
            if (method.IsGenericMethod || method.ContainingType.IsGenericType)
            {
                throw Reject(method, "generic member");
            }
            if (!method.IsStatic)
            {
                throw Reject(method, "theorem that is not static");
            }
            Parameters(candidate, walker, method, method.Parameters, opaque: false);
            var value = ReturnedExpression(method)
                ?? throw Reject(method, "theorem that is not Prove.That");
            IInvocationOperation? by = null;
            if (value is IInvocationOperation { Instance: { } proof } script && Symbols.IsNamed(script.TargetMethod, "Warrant.Proof", "By"))
            {
                by = script;
                value = proof;
            }
            if (value is not IInvocationOperation call || !Symbols.IsNamed(call.TargetMethod, "Warrant.Prove", "That") || call.Arguments.Length != 1)
            {
                throw Reject(method, "theorem that is not Prove.That");
            }
            candidate.Statement = walker.Expr(call.Arguments[0].Value);
            candidate.Script = by is null ? null : walker.Script(by);
            candidate.Budget = Budget(method);
        }

        /// <summary>The budget overrides of <c>[Theorem(...)]</c>, or null when it sets none (zero means the project's).</summary>
        private static VirBudget? Budget(IMethodSymbol method)
        {
            var attribute = method.GetAttributes().First(a => a.AttributeClass?.ToDisplayString() == Symbols.TheoremAttribute);
            int timeout = 0;
            long tacticFuel = 0, kernelFuel = 0;
            foreach (var named in attribute.NamedArguments)
            {
                switch (named.Key)
                {
                    case "TimeoutSeconds":
                        timeout = (int)named.Value.Value!;
                        break;
                    case "TacticFuel":
                        tacticFuel = (long)named.Value.Value!;
                        break;
                    case "KernelFuel":
                        kernelFuel = (long)named.Value.Value!;
                        break;
                }
            }
            return timeout == 0 && tacticFuel == 0 && kernelFuel == 0 ? null : new VirBudget(timeout, tacticFuel, kernelFuel);
        }

        // `opaque`: whether a CancellationToken parameter is accepted as opaque (#215): for a function or a contract unit,
        // not for a theorem, whose parameters are quantified over.
        private static void Parameters(Candidate candidate, Walker walker, ISymbol member, ImmutableArray<IParameterSymbol> parameters, bool opaque = true)
        {
            foreach (var p in parameters)
            {
                if (p.RefKind != RefKind.None)
                {
                    throw Reject(member, "ref parameter");
                }
                var at = p.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
                var ptype = walker.MapParameterType(p.Type, p.NullableAnnotation == NullableAnnotation.Annotated, at, opaque);
                walker.AddParameter(p, candidate.Params.Count, ptype);
                candidate.Params.Add(new VirParam(p.Name, ptype));
                candidate.ParameterSymbols.Add(p);
            }
        }

        private void Function(Candidate candidate, Walker walker, ISymbol member)
        {
            var type = member.ContainingType;
            if (member is IMethodSymbol { MethodKind: not MethodKind.Ordinary })
            {
                throw Reject(member, "unsupported member kind");
            }
            if (member is IMethodSymbol { IsGenericMethod: true } || type.IsGenericType)
            {
                throw Reject(member, "generic member");
            }
            if (member is IPropertySymbol { IsIndexer: true })
            {
                throw Reject(member, "indexer");
            }
            if (member is IPropertySymbol { SetMethod: not null })
            {
                throw Reject(member, "property setter");
            }
            // A verified instance method of a plain class may call its dependencies (M6 KTD9); its class is not a value the
            // model has, so it has no receiver. A record's instance members read the record.
            bool record = Symbols.Shape(type) == TypeShape.Record && type.IsReferenceType;
            bool service = member is IMethodSymbol && type.TypeKind == TypeKind.Class && Symbols.Shape(type) == TypeShape.Other;
            if (!member.IsStatic && !record && !service)
            {
                throw Reject(member, "instance member of a class");
            }
            if (member is IMethodSymbol { IsAsync: true, ReturnsVoid: true })
            {
                throw Reject(member, "async void method");
            }

            Parameters(candidate, walker, member, member is IMethodSymbol m ? m.Parameters : ImmutableArray<IParameterSymbol>.Empty);
            var (returnType, annotated, byRef) = member switch
            {
                IMethodSymbol method => (method.ReturnType, method.ReturnNullableAnnotation == NullableAnnotation.Annotated, method.ReturnsByRef || method.ReturnsByRefReadonly),
                IPropertySymbol property => (property.Type, property.NullableAnnotation == NullableAnnotation.Annotated, property.ReturnsByRef || property.ReturnsByRefReadonly),
                _ => throw Reject(member, "unsupported member kind"),
            };
            if (byRef)
            {
                throw Reject(member, "ref return");
            }
            candidate.Returns = walker.MapReturn(returnType, annotated, ReturnTypeSyntax(member));
            walker.SetReturns(returnType, annotated, member is IMethodSymbol { IsAsync: true });
            if (!member.IsStatic && record)
            {
                candidate.Self = ((RefType)walker.MapType(type, annotated: false, null)).Key;
            }
            else if (!member.IsStatic)
            {
                walker.SetOwner(type);
            }

            var body = Body(member) ?? throw Reject(member, "member without a body");
            candidate.Body = body switch
            {
                IMethodBodyOperation { ExpressionBody: { } e } => ExpressionBody(walker, member, e, candidate.Returns),
                IMethodBodyOperation { BlockBody: { } b } => walker.Body(b),
                IBlockOperation b when IsArrow(b) => ExpressionBody(walker, member, b, candidate.Returns),
                _ => throw Reject(member, "member without a body"),
            };

            // A [ProofFor(nameof(M))] method's script proves M's contract obligation (KTD16); a malformed step rejects M.
            if (_proofs.Value.ScriptFor(candidate.Key) is { } by)
            {
                candidate.Script = walker.ContractScript(by, candidate.Key);
            }
        }

        private static bool IsArrow(IBlockOperation block) => block.Syntax is ArrowExpressionClauseSyntax;

        private static SyntaxNode? ReturnTypeSyntax(ISymbol member) =>
            member.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() switch
            {
                MethodDeclarationSyntax m => m.ReturnType,
                PropertyDeclarationSyntax p => p.Type,
                var other => other,
            };

        private static VirExpr ExpressionBody(Walker walker, ISymbol member, IBlockOperation block, VirType returns)
        {
            if (block.Operations.Length == 1 && block.Operations[0] is IReturnOperation { ReturnedValue: { } value })
            {
                return walker.Returned(value);
            }
            // `=> throw new E(...)`: the body is the throw statement, of the member's return type.
            if (block.Operations.Length == 1
                && (block.Operations[0] is IExpressionStatementOperation { Operation: IThrowOperation } s ? s.Operation : block.Operations[0]) is IThrowOperation t)
            {
                return walker.ThrowExpression(t, returns);
            }
            // `=> F(x)` or `=> await store.Save(p)` in a member that returns no value: a call run for its effects (M6 KTD22).
            if (block.Operations.Length == 1 && block.Operations[0] is IExpressionStatementOperation { Operation: var effect }
                && (returns == VirType.Unit || returns == VirType.Task(VirType.Unit)))
            {
                return walker.Discarded(effect);
            }
            throw Reject(member, "member without a body");
        }

        /// <summary>The body operation of a method or of a property's getter.</summary>
        private IOperation? Body(ISymbol member)
        {
            if (member is IMethodSymbol method)
            {
                method = method.PartialImplementationPart ?? method;
                var syntax = method.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<MethodDeclarationSyntax>().FirstOrDefault();
                return syntax is null ? null : _context.Model(syntax.SyntaxTree).GetOperation(syntax, _cancellationToken);
            }
            var property = member.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<PropertyDeclarationSyntax>().FirstOrDefault();
            if (property is null)
            {
                return null;
            }
            var model = _context.Model(property.SyntaxTree);
            if (property.ExpressionBody is { } arrow)
            {
                return model.GetOperation(arrow, _cancellationToken);
            }
            var getter = property.AccessorList?.Accessors.FirstOrDefault(a => a.IsKind(SyntaxKind.GetAccessorDeclaration));
            return getter is null || (getter.Body is null && getter.ExpressionBody is null)
                ? null
                : model.GetOperation(getter, _cancellationToken);
        }

        /// <summary>The value a theorem returns: its expression body, or the value of a block's only statement.</summary>
        private IOperation? ReturnedExpression(IMethodSymbol method)
        {
            var body = Body(method) as IMethodBodyOperation;
            var block = body?.ExpressionBody ?? body?.BlockBody;
            return block is { Operations.Length: 1 } && block.Operations[0] is IReturnOperation { ReturnedValue: { } value } ? value : null;
        }

        /// <summary>Recursion and cyclic record types (docs/m4/03, "Finding the units").</summary>
        private void RejectCycles()
        {
            var records = _candidates.Values
                .Where(c => c.Kind == VirUnitKind.Type && c.Rejection is null && Symbols.Shape((ITypeSymbol)c.Symbol) == TypeShape.Record)
                .ToDictionary(c => c.Key, StringComparer.Ordinal);
            foreach (var key in Graph.OnCycles(records.Keys, k => records[k].Deps))
            {
                var c = records[key];
                c.Rejection = new Rejection(
                    DiagnosticIds.Unsupported,
                    "cyclic record types",
                    Symbols.FirstLocation(c.Symbol),
                    $"{Symbols.Display(c.Symbol)}: M4 does not support cyclic record types; without null no value of the type can be built.");
            }

            // Direct self-recursion with a leading Spec.Decreases is accepted (KTD14); anything else on a cycle is not.
            var functions = _candidates.Values
                .Where(c => c.Kind != VirUnitKind.Type && c.Rejection is null)
                .ToDictionary(c => c.Key, StringComparer.Ordinal);
            var mutual = Graph.OnCycles(functions.Keys, k => functions[k].Calls.Where(callee => !string.Equals(callee, k, StringComparison.Ordinal)));
            foreach (var key in Graph.OnCycles(functions.Keys, k => functions[k].Calls))
            {
                var c = functions[key];
                var name = Symbols.Display(c.Symbol);
                var at = FirstCall(c, functions) ?? Symbols.FirstLocation(c.Symbol);
                if (c.Kind == VirUnitKind.Theorem)
                {
                    c.Rejection = new Rejection(
                        DiagnosticIds.MalformedSpec, "theorem used in its own proof", Symbols.FirstLocation(c.Symbol), $"{name}: a theorem cannot be used in its own proof script.");
                }
                else if (mutual.Contains(key))
                {
                    c.Rejection = new Rejection(
                        DiagnosticIds.Unsupported, "mutual recursion", at, $"{name}: mutual recursion is not supported; only a method that calls itself can recurse.");
                }
                else if (!(c.Body is BlockStmt { Stmts.Count: > 0 } block && block.Stmts[0] is DecreasesStmt))
                {
                    c.Rejection = new Rejection(
                        DiagnosticIds.Unsupported,
                        "recursion without Spec.Decreases",
                        at,
                        $"{name}: a recursive method states its measure with Spec.Decreases as the first statement of a block body.");
                }
                else if (NestedCall(c) is { } nested)
                {
                    c.Rejection = new Rejection(
                        DiagnosticIds.Unsupported,
                        "nested recursion",
                        c.Walker!.SyntaxOf(nested)?.GetLocation() ?? at,
                        $"{name}: a recursive call inside another recursive call's argument is not supported.");
                }
            }
        }

        /// <summary>A call from a unit to itself inside the arguments of another such call, if there is one.</summary>
        private static CallExpr? NestedCall(Candidate c)
        {
            foreach (var node in VirTreeNodes(c))
            {
                if (node is CallExpr outer && outer.Target == c.Key)
                {
                    var inner = outer.Args.SelectMany(Descendants).OfType<CallExpr>().FirstOrDefault(call => call.Target == c.Key);
                    if (inner is not null)
                    {
                        return inner;
                    }
                }
            }
            return null;
        }

        private static IEnumerable<VirNode> Descendants(VirNode node) =>
            new[] { node }.Concat(VirTree.Children(node).SelectMany(Descendants));

        /// <summary>The location of the first call from a member to another member on its cycle, for the diagnostic.</summary>
        private static Location? FirstCall(Candidate c, Dictionary<string, Candidate> functions)
        {
            var nodes = VirTreeNodes(c);
            foreach (var node in nodes)
            {
                if (node is CallExpr call && functions.ContainsKey(call.Target) && c.Walker!.SyntaxOf(node) is { } syntax)
                {
                    return syntax.GetLocation();
                }
            }
            return null;
        }

        private static IEnumerable<VirNode> VirTreeNodes(Candidate c)
        {
            var roots = new List<VirNode>();
            if (c.Body is { } b)
            {
                roots.Add(b);
            }
            if (c.Statement is { } s)
            {
                roots.Add(s);
            }
            roots.AddRange(c.Script ?? VirList<TacticNode>.Empty);
            var stack = new Stack<VirNode>(roots.AsEnumerable().Reverse());
            while (stack.Count > 0)
            {
                var n = stack.Pop();
                yield return n;
                foreach (var child in VirTree.Children(n).Reverse())
                {
                    stack.Push(child);
                }
            }
        }

        /// <summary>A unit that depends on a rejected unit is rejected too, until nothing changes.</summary>
        private void RejectDependents()
        {
            var ordered = _candidates.Values.OrderBy(c => c.Key, StringComparer.Ordinal).ToList();
            bool changed = true;
            while (changed)
            {
                changed = false;
                foreach (var c in ordered)
                {
                    if (c.Rejection is not null)
                    {
                        continue;
                    }
                    var rejected = c.Deps.FirstOrDefault(d => _candidates.TryGetValue(d, out var dep) && dep.Rejection is not null);
                    if (rejected is not null)
                    {
                        c.Rejection = new Rejection(
                            DiagnosticIds.Unsupported,
                            DependsOnRejected,
                            Symbols.FirstLocation(c.Symbol),
                            $"{Symbols.Display(c.Symbol)} depends on {rejected}, which is rejected.");
                        changed = true;
                    }
                }
            }
        }

        private ExtractedUnit Finish(Candidate c)
        {
            var assumptions = Assumptions(c);
            var deps = new VirList<string>(c.Deps);
            var unit = c.Kind switch
            {
                // A function's script is its [ProofFor] method's (KTD16). The constructor, not `with`: an init accessor's
                // signature differs between Warrant.Vir's netstandard2.0 build, which this assembly compiles against, and
                // its net10.0 build.
                VirUnitKind.Function => new VirUnit(
                    VirUnit.CurrentVersion, c.Key, VirUnitKind.Function, c.Self, new VirList<VirParam>(c.Params), c.Returns!, c.Body!, null, c.Script,
                    null, null, assumptions, _context.Facts, deps, c.Walker!.Dependencies),
                VirUnitKind.Theorem => VirUnit.Theorem(
                    c.Key, c.Statement!, assumptions, _context.Facts, deps, new VirList<VirParam>(c.Params), c.Script, c.Budget),
                VirUnitKind.Type => VirUnit.TypeUnit(c.Key, c.Type!.Definition!, assumptions, _context.Facts, deps),
                VirUnitKind.Contract => VirUnit.Contract(
                    c.Key, new VirList<VirParam>(c.Params), c.Returns!, (BlockStmt)c.Body!, assumptions, _context.Facts, deps),
                _ => throw new InvalidOperationException($"Extraction makes no {c.Kind} units."),
            };
            var walker = c.Walker;
            var spans = SpanTable.Build(unit, node => walker?.SyntaxOf(node) is { } s ? Symbols.Span(s) : null);
            var location = Symbols.FirstLocation(c.Symbol);
            return new ExtractedUnit(unit, spans, Symbols.Display(c.DisplaySymbol ?? c.Symbol), location is null ? null : Symbols.Span(location));
        }

        /// <summary>
        /// Non-null values a unit receives, directly or through record fields (R7), including the values a
        /// <c>Spec.ForAll</c> ranges over, then the closed types it uses (R8):
        /// that only their named members exist, and for a closed class with its own equality, that it agrees with identity.
        /// </summary>
        private VirList<VirAssumption> Assumptions(Candidate c)
        {
            var result = new List<VirAssumption>();
            foreach (var p in c.ParameterSymbols.Concat(c.Walker?.Universals ?? []))
            {
                // A value declared nullable (`Payment? p`) may be null, which the model says (M6 KTD5); nothing assumes otherwise.
                if (Symbols.IsNullableReference(p.Type) && p.NullableAnnotation != NullableAnnotation.Annotated)
                {
                    result.Add(new VirAssumption(VirAssumptionKind.NonNull, p.Name));
                    NonNullFields(p.Name, p.Type, [], result);
                }
            }
            if (c.Kind != VirUnitKind.Type && !c.Symbol.IsStatic)
            {
                NonNullFields("this", c.Symbol.ContainingType, [], result);
            }
            if (c.Kind == VirUnitKind.Function && c.Walker is { } walker)
            {
                DependencyAssumptions(walker, result);
            }
            // M6 KTD20 (#89): the method's own Spec.Requires, which a verified caller proves at its call, but which nothing
            // checks at run time or at a call from code Warrant does not verify.
            if (c.Kind == VirUnitKind.Function && c.Body is BlockStmt body && body.Stmts.Any(s => s is RequiresStmt))
            {
                result.Add(new VirAssumption(VirAssumptionKind.CallerPrecondition, c.Key));
            }

            var closed = new List<string>(c.Deps.Where(d => _candidates.TryGetValue(d, out var dep) && dep.Type is not null && Symbols.IsClosed((ITypeSymbol)dep.Symbol)));
            if (c.Type is not null && Symbols.IsClosed(c.Type.Symbol))
            {
                closed.Add(c.Key);
            }
            closed.Sort(StringComparer.Ordinal);
            foreach (var key in closed)
            {
                result.Add(new VirAssumption(VirAssumptionKind.Closed, key));
            }
            foreach (var key in closed.Where(k => _candidates[k].Type!.OwnEquality))
            {
                result.Add(new VirAssumption(VirAssumptionKind.ClosedEquality, key));
            }
            foreach (var key in closed.Where(k => !_context.IsOwn(_candidates[k].Symbol)))
            {
                result.Add(new VirAssumption(VirAssumptionKind.ReferencedSource, key));
            }
            return new VirList<VirAssumption>(result);
        }

        /// <summary>
        /// What a method with dependencies assumes of them (KTD9, KTD20, #71): each dependency it calls through is not null,
        /// and neither is each non-nullable reference a member it calls returns, the <c>Task</c> included (as
        /// <c>store.Get()</c>, and the awaited value as <c>await store.Get()</c>), nor any record field reachable from one;
        /// and each member does what its contract unit says.
        /// </summary>
        private static void DependencyAssumptions(Walker walker, List<VirAssumption> result)
        {
            foreach (var use in walker.DependencyUses)
            {
                result.Add(new VirAssumption(VirAssumptionKind.NonNull, use.Name));
            }
            foreach (var use in walker.DependencyUses)
            {
                foreach (var member in use.Members.Values)
                {
                    var called = $"{use.Name}.{member.Name}()";
                    if (Walker.IsTask(member.ReturnType) is { } task)
                    {
                        if (task.IsReferenceType)
                        {
                            NonNullResult(called, task, NullableAnnotation.NotAnnotated, result);
                        }
                        if (task.TypeArguments.Length == 1)
                        {
                            NonNullResult("await " + called, task.TypeArguments[0], task.TypeArgumentNullableAnnotations[0], result);
                        }
                    }
                    else
                    {
                        NonNullResult(called, member.ReturnType, member.ReturnNullableAnnotation, result);
                    }
                }
            }
            foreach (var key in walker.ContractMembers.Keys)
            {
                result.Add(new VirAssumption(VirAssumptionKind.ExternalContract, key));
            }
        }

        /// <summary>A returned reference that is assumed present, unless it is declared nullable or cannot be null.</summary>
        private static void NonNullResult(string subject, ITypeSymbol type, NullableAnnotation annotation, List<VirAssumption> result)
        {
            bool reference = Walker.IsTask(type) is not null || Symbols.IsNullableReference(type);
            var assumption = new VirAssumption(VirAssumptionKind.NonNull, subject);
            if (reference && annotation != NullableAnnotation.Annotated && !result.Contains(assumption))
            {
                result.Add(assumption);
                NonNullFields(subject, type, [], result);
            }
        }

        private static void NonNullFields(string prefix, ITypeSymbol type, HashSet<string> path, List<VirAssumption> result)
        {
            if (type is not INamedTypeSymbol record || Symbols.Shape(record) != TypeShape.Record
                || Symbols.PrimaryConstructor(record) is not { } primary
                || Symbols.PositionalProperties(record, primary) is not { } fields
                || !path.Add(Symbols.Key(record)))
            {
                return;
            }
            foreach (var field in fields)
            {
                if (Symbols.IsNullableReference(field.Type) && field.NullableAnnotation != NullableAnnotation.Annotated)
                {
                    var subject = prefix + "." + field.Name;
                    result.Add(new VirAssumption(VirAssumptionKind.NonNull, subject));
                    NonNullFields(subject, field.Type, path, result);
                }
            }
            path.Remove(Symbols.Key(record));
        }
    }
}
