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
public static class Extractor
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
    /// Extracts every <c>[Verified]</c> member, <c>[Theorem]</c>, and record, enum or closed type they use.
    /// A compilation with errors gives no units, only its errors.
    /// </summary>
    /// <param name="compilation">The compilation, normally from <c>Warrant.Frontend.CompilationFactory</c>.</param>
    /// <param name="cancellationToken">Cancels the extraction.</param>
    /// <returns>The units in dependency order, and the diagnostics.</returns>
    public static ExtractionResult Extract(CSharpCompilation compilation, CancellationToken cancellationToken = default)
    {
        if (compilation is null)
        {
            throw new ArgumentNullException(nameof(compilation));
        }
        // The compilation is parsed without the defines of a real build, which M5a takes from Csc. Code under #if could
        // therefore be code no build runs, or could add an overload or a type that changes what other code binds to.
        // So every combination of the symbols the #if conditions test is extracted, and a unit is kept only if its VIR is
        // the same in every combination that compiles. A combination that does not compile is not a real build.
        var symbols = ConditionalSymbols(compilation, cancellationToken);
        if (symbols.Count == 0)
        {
            return ExtractOne(compilation, cancellationToken);
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

        var results = new List<ExtractionResult>();
        ExtractionResult? firstFailure = null;
        for (int mask = 0; mask < 1 << symbols.Count; mask++)
        {
            var defined = symbols.Where((_, i) => (mask & (1 << i)) != 0).ToList();
            var result = ExtractOne(mask == 0 ? compilation : WithSymbols(compilation, defined, cancellationToken), cancellationToken);
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

    private static ExtractionResult ExtractOne(CSharpCompilation compilation, CancellationToken cancellationToken)
    {
        var errors = compilation.GetDiagnostics(cancellationToken)
            .Where(d => d.Severity == DiagnosticSeverity.Error)
            .Select(d => new ExtractionDiagnostic(
                d.Id, ExtractionSeverity.Error, null, null, Symbols.Span(d.Location), d.GetMessage(CultureInfo.InvariantCulture)))
            .ToList();
        if (errors.Count > 0)
        {
            return new ExtractionResult([], Sort(errors), hasCompileErrors: true);
        }
        return new Run(compilation, cancellationToken).Execute();
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

    /// <summary>The compilation with every tree parsed again with <paramref name="defined"/> added to its symbols.</summary>
    private static CSharpCompilation WithSymbols(CSharpCompilation compilation, List<string> defined, CancellationToken cancellationToken)
    {
        var trees = compilation.SyntaxTrees.Select(t =>
        {
            var options = (CSharpParseOptions)t.Options;
            var names = options.PreprocessorSymbolNames.Concat(defined).Distinct(StringComparer.Ordinal);
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

        public TypeBuild? Type { get; set; }
    }

    private sealed class Run
    {
        private readonly CSharpCompilation _compilation;
        private readonly CancellationToken _cancellationToken;
        private readonly ExtractionContext _context;
        private readonly Dictionary<string, Candidate> _candidates = new(StringComparer.Ordinal);
        private readonly List<ExtractionDiagnostic> _diagnostics = [];

        public Run(CSharpCompilation compilation, CancellationToken cancellationToken)
        {
            _compilation = compilation;
            _cancellationToken = cancellationToken;
            var facts = new VirFacts(
                compilation.Options.CheckOverflow ? VirOverflow.Checked : VirOverflow.Wrap,
                LanguageText(compilation.LanguageVersion),
                Version,
                RoslynVersion);
            _context = new ExtractionContext(compilation, facts);
        }

        public ExtractionResult Execute()
        {
            var scan = CompilationScan.Run(_context, _cancellationToken);
            var types = SourceTypes(_compilation.Assembly.GlobalNamespace)
                .OrderBy(Symbols.Key, StringComparer.Ordinal)
                .ToList();

            var members = types
                .SelectMany(t => t.GetMembers())
                .Where(m => m is IMethodSymbol { MethodKind: not MethodKind.PropertyGet and not MethodKind.PropertySet } or IPropertySymbol)
                .Where(m => Symbols.IsVerified(m) || Symbols.IsTheorem(m))
                .OrderBy(Symbols.Key, StringComparer.Ordinal);
            foreach (var member in members)
            {
                _cancellationToken.ThrowIfCancellationRequested();
                var candidate = BuildMember(member);
                _candidates.Add(candidate.Key, candidate);
            }

            // Type units for every type a unit uses, then the shape checks for every [Closed] type, used or not.
            while (_context.TryNextType(out var type))
            {
                AddType(type, scan);
            }
            foreach (var type in types.Where(t => Symbols.IsClosed(t) && !_context.IsUsed(Symbols.Key(t))))
            {
                var build = TypeChecks.Build(_context, scan, type);
                if (build.Rejection is { } r)
                {
                    Report(Symbols.Key(type), r);
                }
            }

            // WRT0008 anywhere in the compilation (KTD18).
            foreach (var (operation, construct, member) in scan.UnnamedClosedValues)
            {
                Warn(member, construct, operation.Syntax.GetLocation());
            }
            foreach (var type in types.Where(t => Symbols.Shape(t) == TypeShape.ClosedEnum && !TypeChecks.HasZero(t)))
            {
                Warn(type, "closed enum without a member valued 0", Symbols.FirstLocation(type));
            }

            RejectCycles();
            RejectDependents();

            foreach (var c in _candidates.Values.Where(c => c.Rejection is not null).OrderBy(c => c.Key, StringComparer.Ordinal))
            {
                Report(c.Key, c.Rejection!);
            }

            var accepted = _candidates.Values.Where(c => c.Rejection is null).ToDictionary(c => c.Key, StringComparer.Ordinal);
            var order = Graph.TopologicalOrder(accepted.Keys, k => accepted[k].Deps);
            var units = order.Select(k => Finish(accepted[k])).ToList();
            return new ExtractionResult(units, Sort(_diagnostics), hasCompileErrors: false);
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

        private void Warn(ISymbol member, string construct, Location? at) =>
            _diagnostics.Add(new ExtractionDiagnostic(
                DiagnosticIds.UnnamedClosedValue,
                ExtractionSeverity.Warning,
                construct,
                Symbols.Key(member),
                at is null ? null : Symbols.Span(at),
                $"{Symbols.Display(member)}: {construct} can give a [Closed] enum a value the model says cannot exist."));

        private void AddType(INamedTypeSymbol type, CompilationScan scan)
        {
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
            return candidate;
        }

        private static RejectedException Reject(ISymbol member, string construct) =>
            new(new Rejection(
                DiagnosticIds.Unsupported, construct, Symbols.FirstLocation(member), $"{Symbols.Display(member)}: M4 does not support {construct}."));

        private void Theorem(Candidate candidate, Walker walker, IMethodSymbol method)
        {
            if (method.Parameters.Length > 0)
            {
                throw Reject(method, "theorem with parameters");
            }
            if (method.IsGenericMethod || method.ContainingType.IsGenericType)
            {
                throw Reject(method, "generic member");
            }
            if (!method.IsStatic)
            {
                throw Reject(method, "theorem that is not static");
            }
            var value = ReturnedExpression(method)
                ?? throw Reject(method, "theorem that is not Prove.That");
            if (value is not IInvocationOperation call || !Symbols.IsNamed(call.TargetMethod, "Warrant.Prove", "That") || call.Arguments.Length != 1)
            {
                throw Reject(method, "theorem that is not Prove.That");
            }
            candidate.Statement = walker.Expr(call.Arguments[0].Value);
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
            if (!member.IsStatic && !(Symbols.Shape(type) == TypeShape.Record && type.IsReferenceType))
            {
                throw Reject(member, "instance member of a class");
            }

            var parameters = member is IMethodSymbol m ? m.Parameters : ImmutableArray<IParameterSymbol>.Empty;
            foreach (var p in parameters)
            {
                if (p.RefKind != RefKind.None)
                {
                    throw Reject(member, "ref parameter");
                }
                var at = p.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
                var ptype = walker.MapType(p.Type, p.NullableAnnotation == NullableAnnotation.Annotated, at);
                walker.AddParameter(p, candidate.Params.Count);
                candidate.Params.Add(new VirParam(p.Name, ptype));
                candidate.ParameterSymbols.Add(p);
            }
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
            candidate.Returns = walker.MapType(returnType, annotated, ReturnTypeSyntax(member));
            if (!member.IsStatic)
            {
                candidate.Self = ((RefType)walker.MapType(type, annotated: false, null)).Key;
            }

            var body = Body(member) ?? throw Reject(member, "member without a body");
            candidate.Body = body switch
            {
                IMethodBodyOperation { ExpressionBody: { } e } => ExpressionBody(walker, member, e),
                IMethodBodyOperation { BlockBody: { } b } => walker.Block(b),
                IBlockOperation b when IsArrow(b) => ExpressionBody(walker, member, b),
                _ => throw Reject(member, "member without a body"),
            };
        }

        private static bool IsArrow(IBlockOperation block) => block.Syntax is ArrowExpressionClauseSyntax;

        private static SyntaxNode? ReturnTypeSyntax(ISymbol member) =>
            member.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() switch
            {
                MethodDeclarationSyntax m => m.ReturnType,
                PropertyDeclarationSyntax p => p.Type,
                var other => other,
            };

        private static VirExpr ExpressionBody(Walker walker, ISymbol member, IBlockOperation block)
        {
            if (block.Operations.Length == 1 && block.Operations[0] is IReturnOperation { ReturnedValue: { } value })
            {
                return walker.Expr(value);
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

            var functions = _candidates.Values
                .Where(c => c.Kind != VirUnitKind.Type && c.Rejection is null)
                .ToDictionary(c => c.Key, StringComparer.Ordinal);
            foreach (var key in Graph.OnCycles(functions.Keys, k => functions[k].Calls))
            {
                var c = functions[key];
                var at = FirstCall(c, functions);
                c.Rejection = new Rejection(
                    DiagnosticIds.Unsupported,
                    "recursion",
                    at ?? Symbols.FirstLocation(c.Symbol),
                    $"{Symbols.Display(c.Symbol)}: M4 does not support recursion.");
            }
        }

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
                VirUnitKind.Function => VirUnit.Function(c.Key, new VirList<VirParam>(c.Params), c.Returns!, c.Body!, assumptions, _context.Facts, deps, c.Self),
                VirUnitKind.Theorem => VirUnit.Theorem(c.Key, c.Statement!, assumptions, _context.Facts, deps),
                _ => VirUnit.TypeUnit(c.Key, c.Type!.Definition!, assumptions, _context.Facts, deps),
            };
            var walker = c.Walker;
            var spans = SpanTable.Build(unit, node => walker?.SyntaxOf(node) is { } s ? Symbols.Span(s) : null);
            var location = Symbols.FirstLocation(c.Symbol);
            return new ExtractedUnit(unit, spans, Symbols.Display(c.Symbol), location is null ? null : Symbols.Span(location));
        }

        /// <summary>
        /// Non-null values a unit receives, directly or through record fields (R7), then the closed types it uses (R8):
        /// that only their named members exist, and for a closed class with its own equality, that it agrees with identity.
        /// </summary>
        private VirList<VirAssumption> Assumptions(Candidate c)
        {
            var result = new List<VirAssumption>();
            foreach (var p in c.ParameterSymbols)
            {
                if (Symbols.IsNullableReference(p.Type))
                {
                    result.Add(new VirAssumption(VirAssumptionKind.NonNull, p.Name));
                    NonNullFields(p.Name, p.Type, [], result);
                }
            }
            if (c.Kind != VirUnitKind.Type && !c.Symbol.IsStatic)
            {
                NonNullFields("this", c.Symbol.ContainingType, [], result);
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
            return new VirList<VirAssumption>(result);
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
                if (Symbols.IsNullableReference(field.Type))
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
