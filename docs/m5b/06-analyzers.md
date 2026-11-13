# 6. Analyzers

> Part of the [M5b design](README.md). Decisions: KTD21 to KTD23; Key Decision on what analyzers report.

Some mistakes need no proof search to find.
A `[Verified]` method that uses an unsupported construct (WRT0002), calls a theorem (WRT0003), has a malformed proof script (WRT0004) or calls an unmodelled member (WRT0005) is rejected by extraction before anything is translated, and so is a `[Closed]` type without the closed shape (WRT0009) or a value that can reach a `[Closed]` enum unnamed (WRT0008). From M6 the analyzer also reports the warning WRT0013 for a `Spec` statement that states nothing (`Spec.NoThrow` on a method that cannot raise, #239); the method is still translated. Like every analyzer diagnostic it is
worked out for the IDE's one configuration: a build that compares `#if` combinations may reject the method instead,
and then reports no WRT0013.
In M5a the developer finds out only when the build runs.
`Warrant.Analyzers` reports the same diagnostics as they type.

## Same rules, one copy

The analyzer must say what the build will say, at the same place.
The only reliable way is for both to run the same code, so the analyzer compiles the `Warrant.Extraction` and `Warrant.Vir` sources into its own assembly (KTD21).

Shipping one assembly, rather than an analyzer plus helper libraries, also avoids a loading problem.
When the compiler runs on .NET Framework there is no `AssemblyLoadContext`, and the first assembly loaded with a given identity wins; two Warrant versions in one Visual Studio session could otherwise bind each other's copy of `Warrant.Extraction`.

Extraction is already netstandard2.0, compiled against Roslyn 4.8.0, and does no I/O, which is what an analyzer needs: the .NET 8 SDK and Visual Studio 2022 ship Roslyn 4.8, and an analyzer built against a newer Roslyn fails to load there (CS9057).
Roslyn's rule against I/O in analyzers, RS1035, is checked only in the project that turns on `EnforceExtendedAnalyzerRules`, so Extraction and Vir turn it on too.
RS1035 does not ban clocks, `Guid.NewGuid` or `Stopwatch`; a banned-symbols list adds them, along with `Random` and `Environment`, so nothing nondeterministic creeps into the shared code.

## A per-member entry point

`Extractor.Extract` works on a whole compilation (KTD22).
It asks the compilation for all its errors first (`Compilation.GetDiagnostics()`), and without the build's defines it re-parses the compilation once per combination of up to six `#if` symbols, 64 times in the worst case.
That is right for a build and far too slow for a keystroke.

Extraction gains a second entry, `Diagnoser`, that runs the same checks for one symbol, skipping both.
For a member it checks the member and everything it reaches: the members it calls or cites in a proof script, transitively, and the types they use.
That set is closed under calls and dependencies, so mutual recursion and "depends on a rejected unit" come out exactly as a full extraction finds them; `Extractor.Run` has one closure mode, so both entries run the same rule code.
The scan of the whole compilation that the closed shape and WRT0008 need is made once per compilation, when first needed, and shared.
A member whose own declaration has a compiler error gets nothing, because the compiler already reports what is wrong with it; its users are still checked.

The analyzer calls `Diagnoser` from a symbol action for each member that carries `[Verified]` or `[Theorem]` and each `[Closed]` type, and reports WRT0008, which is a property of the whole compilation, from a compilation-end action.
A diagnostic about a record or enum is found through every member that uses it and reported once, so the set reported is the same on every run.
The shape, as built:

```csharp
// Abridged from src/Warrant.Analyzers/WarrantAnalyzer.cs.
public override void Initialize(AnalysisContext context)
{
    context.EnableConcurrentExecution();
    context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
    context.RegisterCompilationStartAction(start =>
    {
        if (start.Compilation.GetTypeByMetadataName("Warrant.VerifiedAttribute") is null) return;
        var session = new Session((CSharpCompilation)start.Compilation);   // one Diagnoser, one "reported" set
        start.RegisterSymbolAction(session.AnalyzeSymbol, SymbolKind.Method, SymbolKind.Property, SymbolKind.NamedType);
        start.RegisterCompilationEndAction(session.AnalyzeCompilation);    // WRT0008
    });
}
```

Two tests compare them on every compilation of the M4 and M5a corpora, against an extraction with the build's defines (what the analyzer sees): `Diagnoser`'s answer for each member equals the full extraction's for that member, and the analyzer's diagnostics equal the full extraction's, ID, span, severity and message alike.

## Determinism

Analyzer output must be the same on every run (design §3.2).
The analyzer keeps no state between compilations (RS1008) and runs concurrently, so the test (`TwentyConcurrentRunsGiveByteIdenticalDiagnosticsAndTheAnalyzerNeverThrows`) runs it 20 times with concurrent execution on a multi-file compilation, sorts the diagnostics by file, position, ID and message, and requires all 20 lists to be byte-identical.
The order Roslyn reports concurrent diagnostics in is not guaranteed, so the test compares sorted lists; the analyzer's own order within one member is deterministic and checked separately.

## IDE only

The compiler runs analyzers in command-line builds too.
If this one ran there, a WRT0002 at error severity would fail `CoreCompile`, the build would stop before the Warrant target, and every other theorem in the project would go unverified.
M5a reports WRT0002 from the CLI and still verifies the rest.
The CLI would also report the same diagnostic again.

So the `Warrant` package, which ships the analyzer under `analyzers/dotnet/cs/`, takes it out of `@(Analyzer)` before `CoreCompile` in every build that is not a design-time build (KTD23).
The SDK adds a package's analyzers while it resolves references, so the build test that checks a design-time build's list resolves references first, as Visual Studio does.
That lives in `Warrant`'s own targets rather than `Warrant.Build`'s, because a project may reference `Warrant` alone; it gets WRT0011 and must still build.
Visual Studio's live analysis uses the design-time build's analyzer list, so the developer sees the diagnostics while editing, and the build reports each one once, from the CLI, as before.
Warning severity in builds was the alternative; it would still print everything twice.

The analyzer is built against Roslyn 4.8 and tested under 4.8 and 5.9 (`Warrant.Analyzers.Tests.Roslyn48` and `Warrant.Analyzers.Tests`).

## What the analyzer sees

The analyzer sees the active configuration only.
A multi-targeted project's build keeps M4's check that a verified member translates the same under every `#if` combination (M5a KTD21); that diagnostic appears only in the build.
And the analyzer never reports proof results: it cannot ask the server (I/O), and a proof that depends on the last keystroke is M9's language server.

Two things the IDE shows differently from the build:
WRT0008 comes from a compilation-end action, which Visual Studio runs only with full solution analysis on;
and a diagnostic about a record or enum in another file is reported at the type, which the IDE shows when that file is analyzed through a member that uses it, while the member itself always shows "depends on a rejected unit".
