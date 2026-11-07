; Unshipped analyzer release
; https://github.com/dotnet/roslyn-analyzers/blob/main/src/Microsoft.CodeAnalysis.Analyzers/ReleaseTrackingAnalyzers.Help.md

### New Rules

Rule ID | Category | Severity | Notes
--------|----------|----------|-------
WRT0002 | Warrant | Error | WarrantAnalyzer, construct outside the supported subset
WRT0003 | Warrant | Error | WarrantAnalyzer, call to a theorem
WRT0004 | Warrant | Error | WarrantAnalyzer, malformed specification
WRT0005 | Warrant | Error | WarrantAnalyzer, call to a member that is not verified
WRT0008 | Warrant | Warning | WarrantAnalyzer, a [Closed] enum can hold an unnamed value
WRT0009 | Warrant | Error | WarrantAnalyzer, [Closed] class without the closed shape
