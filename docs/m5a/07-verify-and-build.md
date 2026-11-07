# 7. `warrant verify` and the build task

> Part of the [M5a design](README.md). Decisions: KTD19 to KTD24, Key Decisions in the [plan](../plans/2026-11-03-0838-feat-m5a-meta-tactics-plan.md).

M4 runs only from the test suite and `warrant translate`.
M5a runs in the normal build: after the compiler, MSBuild runs `warrant verify`, which reads the compiler's own arguments, proves the theorems, and reports diagnostics that fail the build.
This chapter covers the CLI verb, the task, how the compilation is reproduced, the diagnostics, and the budgets.

## Who does what

```mermaid
sequenceDiagram
  participant M as MSBuild (dotnet build or MSBuild.exe)
  participant C as Csc task
  participant W as Warrant.Build task
  participant V as warrant verify (net10.0 process)
  M->>C: CoreCompile (ProvideCommandLineArgs=true)
  C-->>M: @(CscCommandLineArgs), assembly
  M->>M: WarrantVerify target (after CoreCompile): write obj/…/warrant.csc.args (keep the last one if CoreCompile was skipped)
  M->>W: WarrantVerify task
  W->>V: dotnet warrant.dll verify --csc-args obj/warrant.csc.args --format msbuild …
  V->>V: compile, extract, translate, prove, report
  V-->>W: one record per diagnostic; exit code
  W-->>M: Log.LogError(code, file, line, column, message)
```

The design (§8.3) had the task rebuild the compilation and extract VIR inside MSBuild.
M5a moves both into the CLI (KTD21), for two reasons found while planning:

- `Warrant.Extraction` is compiled against Roslyn 4.8 so that M5b's analyzer loads in older hosts, and Roslyn 4.8 cannot parse C# 13 or 14; SDK 10 defaults `LangVersion` to 14 for `net10.0`. The CLI already runs Roslyn 5.0.
- Visual Studio's MSBuild runs on .NET Framework, where a task that loads Roslyn competes with MSBuild's own copies of its dependencies through binding redirects. A task with no Roslyn reference avoids the problem.

The task is then thin: a netstandard2.0 `ToolTask` that references only `Microsoft.Build.Utilities.Core` (KTD22).
Running the engine in a separate process also gives the time limit a clean place to act, and an out-of-memory or stack overflow in a tactic cannot take the build node down.
M5b keeps the child process: it still compiles and extracts, then sends the units' VIR to the verification server, or verifies them in-process when the server cannot be used, and renders the results ([M5b chapter 2](../m5b/02-client-and-build.md)). The server never loads Roslyn.

## Reproducing the compilation

Setting `ProvideCommandLineArgs` makes the `Csc` task output its full argument list as `@(CscCommandLineArgs)`, already resolved: sources, references, `/define:`, `/langversion:`, `/checked`, `/nullable`, `/unsafe`, `/features:` and analyzer configuration.
Visual Studio's own project system uses the same output for design-time builds.
The task writes the list to `obj/warrant.csc.args`, one argument per line, and the CLI parses it with Roslyn's `CSharpCommandLineParser`, so the compilation has exactly the options the compiler used.

Three details follow:

- **Skipped compiles.** When `CoreCompile` is up to date, Csc does not run and the item is empty, so the task reuses the file from the last compile.
- **Real defines.** With the compiler's `/define:` list, extraction no longer compares every combination of `#if` symbols (M4 docs/m4/03); code is translated under the build's actual configuration. The combination check stays for `warrant verify <directory>` and `translate`, which have no compiler arguments, and for multi-targeted projects (below), where a difference reads, for example, `Sample.Picks.Pick(int) translates differently depending on which of NET8_0 the build defines.` (WRT0002).
- **Source generators.** Generated sources are not in the arguments, so the CLI runs the generators itself, as Csc does (`SourceGenerators.cs`). It loads every C# generator among the `/analyzer:` arguments into an assembly load context of its own, gives them the `/additionalfile:` arguments and the analyzer configuration, and runs Roslyn's `CSharpGeneratorDriver`. Overloads, partial-member bodies and types that a generator adds are then part of the compilation Warrant translates. Analyzers are not run: they report diagnostics but do not change the program.
  A generator must be built for the compiler Warrant carries (Roslyn 5.9.0, the compiler in SDK 10.0.403) or an older one. Warrant follows the SDK's compiler rather than the oldest one it supports, because the SDK ships generators built for its own compiler: the Razor SDK adds `Microsoft.CodeAnalysis.Razor.Compiler.dll`, which references Roslyn 5.9, to every Web, Blazor and Razor class library project. A project built with an older SDK is compiled by Warrant with a newer Roslyn than its Csc, under the language version its own arguments set. Roslyn refuses one built for a newer compiler, and then the compilation can miss what it would have written. That, a generator that fails to load, and one that throws all end in WRT0012, even when the code compiles without the generator's output: Csc may have run the generator, and output such as an interceptor or an overload that binds more closely changes what the code means without any compile error. The message names the generator problem and any missing symbols: `error WRT0012: A source generator did not run, so the compilation may differ from the compiler's: Gen.dll: ReferencesNewerCompiler, built for compiler 6.0.0.0`. An analyzer assembly that fails to load is ignored when its metadata declares no `[Generator]` type, since analyzers do not change the program; a file whose metadata cannot be read counts as a generator.
  An interceptor (`[InterceptsLocation]`) replaces a call when Csc emits code, and the semantic model still names the original method. A call in a `[Verified]` or `[Theorem]` member that a generated interceptor replaces is therefore rejected with WRT0002, `Unsupported construct 'intercepted call'`, naming the interceptor.

## `warrant verify`

```text
warrant verify --csc-args <file> [--project-dir <dir>] [options]
warrant verify <directory>       [options]                 # M4 corpus settings, like translate

options:
  --format text|msbuild           default text
  --out <file.ndjson>             write certificates: the bundle and every admitted declaration
  --report <dir>                  write report.md and report.json
  --kernel-fuel <n> --tactic-fuel <n> --timeout <seconds>
  --bundle <path>                 another semantics bundle; the sidecar must sit next to it
  --keep-conditional-check        keep M4's #if combination check with --csc-args
```

The sidecar, `warrant-attributes.ndjson.gz`, is read from the bundle's directory, and its header must name the bundle's SHA-256.
A missing or mismatched sidecar is declined before the bundle is loaded.

The text format matches `translate`'s: one line per unit, diagnostics in `path(line,col): error WRTnnnn: message` form with the message's later lines indented below, then a summary.
On the M5a accepted corpus (*ran*):

```text
Warrant: 20 verified units, 7 theorems proved, 0 not proved.
```

The unit count includes type units.
`--format msbuild` writes one record per diagnostic, so a multi-line goal stays one event (KTD20):

```text
WRT1<TAB>kind<TAB>severity<TAB>code<TAB>file<TAB>line<TAB>col<TAB>endLine<TAB>endCol<TAB>message
```

`kind` is `diag`, `goal` (the goal block, which follows its diagnostic) or `summary`; only the message is escaped (`\\`, `\n`, `\r`, `\t`).
In this format the summary is a record and is not also printed as a plain line.
Exit codes are 0 when every theorem is proved (warnings allowed), 1 when at least one error was reported, and 2 for bad arguments or unreadable input, including a missing bundle and a missing or mismatched sidecar.
A unit the engine could not translate or admit is WRT0010 and exits 1.

The reference used to list `warrant verify <project>`.
Evaluating a project file needs MSBuild, so M5a takes the argument file the build writes, or a directory; a project mode is follow-up work, and the reference now says so.

## The task and its targets

The `Warrant.Build` package's targets, in outline:

```xml
<PropertyGroup>
  <WarrantEnabled Condition="'$(WarrantEnabled)' == ''">true</WarrantEnabled>
  <ProvideCommandLineArgs Condition="'$(WarrantEnabled)' == 'true'">true</ProvideCommandLineArgs>
  <WarrantCliPath Condition="'$(WarrantCliPath)' == ''">$(MSBuildThisFileDirectory)..\tools\net10.0\any\warrant.dll</WarrantCliPath>
  <!-- _WarrantFirstTargetFramework and _WarrantMultiTargeted, computed from $(TargetFrameworks) -->
</PropertyGroup>

<Target Name="WarrantVerify" AfterTargets="CoreCompile"
        Condition="'$(WarrantEnabled)' == 'true' and '$(DesignTimeBuild)' != 'true'
                   and ('$(TargetFrameworks)' == '' or '$(TargetFramework)' == '$(_WarrantFirstTargetFramework)')">
  <WriteLinesToFile Condition="'@(CscCommandLineArgs)' != ''"
                    File="$(IntermediateOutputPath)warrant.csc.args" Lines="@(CscCommandLineArgs)"
                    Overwrite="true" WriteOnlyWhenDifferent="true" />
  <WarrantVerify CscArgsFile="$(IntermediateOutputPath)warrant.csc.args"
                 ProjectDirectory="$(MSBuildProjectDirectory)"
                 CliPath="$(WarrantCliPath)" DotnetHostPath="$(DOTNET_HOST_PATH)"
                 KernelFuel="$(WarrantKernelFuel)" TacticFuel="$(WarrantTacticFuel)"
                 TimeoutSeconds="$(WarrantTimeoutSeconds)"
                 KeepConditionalCheck="$(_WarrantMultiTargeted)" />
</Target>
```

This is `src/Warrant.Build/build/Warrant.Build.targets`, shortened; `Warrant.Build.props` only sets `WarrantBuildImported`, which the WRT0011 check reads (below).

The target has no `Inputs` and `Outputs`, so every build verifies again (KTD22).
Skipping an unchanged project would be a cache keyed on timestamps, and the CI trust decision for M5a is that every build re-checks every proof (Key Decisions).
M5b keeps the target without them and adds a content-addressed result cache inside the CLI's run, so an unchanged build still runs the CLI but no tactics ([M5b chapter 4](../m5b/04-cache-and-recheck.md)).
In a multi-targeted project the target runs in the inner build of the first target framework only, so diagnostics are not repeated, and it asks the CLI to keep M4's `#if` combination check, so a verified method whose meaning differs under `#if NET8_0` is rejected instead of being proved for one framework and shipped unproved for the other.
A build of one framework that is not the first, such as `dotnet build -f net10.0` for `net8.0;net10.0`, therefore verifies nothing and gives no warning: the inner build cannot tell whether the first framework's build is part of the same invocation. Verify with the first framework, or a build of all of them.
Design-time builds, which Visual Studio runs constantly in the background, skip it.

The task launches the CLI, which the package carries framework-dependent under `tools/net10.0/any/`, as `dotnet warrant.dll`, using `$(DOTNET_HOST_PATH)` and falling back to `dotnet` on the path.
The build machine therefore needs the .NET 10 runtime even for a project that targets `net8.0`.

`LogEventsFromTextOutput` parses each record and calls `Log.LogError` (or `LogWarning`) with the code, file, line, column, end position and message.
Visual Studio's Error List shows only the first line of a message, so the first line is complete on its own (theorem, outcome, counterexample), and the rest of the message, ending with the goal, follows on the next lines; the goal record is also logged as a high-importance message, so it is in the build output either way.
The console and file loggers print each line of a multi-line message with the location in front, so one error event becomes several log lines (*ran*, from the build integration tests):

```text
Increments.cs(9,28,9,36): error WRT0001: Theorem 'Increments.NoScript(int)' could not be proved: unsolved goals. Counterexample: x = 2147483647.
Increments.cs(9,28,9,36): error WRT0001: x : Int32
Increments.cs(9,28,9,36): error WRT0001: ⊢ Increment x > x
```

MSBuild still counts it as one error.
When the CLI exits with 2, with another unexpected code, or with 1 without reporting an error, the task logs WRT0010 with the last 20 lines of its error output, and no MSBuild MSB6006 "exited with code" error is added.

## Noticing that nothing ran

A project that references `Warrant` but does not reference `Warrant.Build`, or sets `WarrantEnabled` to false, builds green with nothing checked.
The `Warrant` package's `build/` targets warn in that case (WRT0011, KTD23), and every verified build prints its summary line, so a build log always shows whether theorems were checked:

```text
…/build/Warrant.targets(…): warning WRT0011: Warrant: this project references Warrant but not Warrant.Build, so no theorem is verified. Add a reference to Warrant.Build, or add WRT0011 to NoWarn.
```

MSBuild places a `Warning` task's diagnostic at the task, so WRT0011's location is a line of the package's `build/Warrant.targets`, not of the project.
MSBuild cannot see whether a project has `[Verified]` code, so the warning does not try; a project that references `Warrant` for another reason silences it with `NoWarn`.
Both packages use `build/`, not `buildTransitive/`, so an application that only references a verified library neither warns nor verifies the library again.

## Diagnostics

| Code | Meaning in M5a |
|---|---|
| WRT0001 | A theorem, or a decrease obligation, was not proved. Shows the remaining goals, and a counterexample when the search finds one. |
| WRT0002 to WRT0005, WRT0008, WRT0009 | As in M4, raised by extraction. WRT0002 now also names `recursion without Spec.Decreases`, `mutual recursion`, `nested recursion`, `Spec.Decreases not first` and `lambda with statements`; WRT0004 covers malformed scripts and quantifiers (chapter 1). |
| WRT0006 | A theorem ran out of kernel fuel, tactic fuel or time; the message says which. |
| WRT0010 | Internal error: the kernel rejected a term Warrant built, the engine could not translate or admit a unit, Meta failed unexpectedly, or the CLI failed. Report it as a bug. |
| WRT0011 (warning) | Verification is not enabled for a project that references `Warrant`. |
| WRT0012 | The compilation could not be reproduced from Csc's arguments: it does not compile, or a source generator could not load or threw, even if the code compiles without it. Names the missing symbols and the generator problem. |

The engine never reports an unproved claim as false.
WRT0001 says a theorem "could not be proved"; a counterexample, when one is found, is what shows it is false.

## Budgets

Each theorem runs with three limits (Key Decisions, KTD24):

| Limit | Default | MSBuild property | Per theorem |
|---|---|---|---|
| kernel fuel | 20M steps (100M for `warrant verify <directory>` and the corpus tests) | `WarrantKernelFuel` | `[Theorem(KernelFuel = …)]` |
| tactic fuel | 171,970 steps: ten times the largest use in the M5a corpus (17,197, `ZeroIsNeutral`'s intro and omega), measured in U18 and again by each unit that adds a tactic; it was 910 before simp and 135,630 before omega | `WarrantTacticFuel` | `[Theorem(TacticFuel = …)]` |
| wall clock | 30 s | `WarrantTimeoutSeconds` | `[Theorem(TimeoutSeconds = …)]` |

Exhausting any of them fails the theorem with WRT0006 and never counts as a proof.
The wall clock covers both Meta and the kernel: Meta checks the deadline wherever it charges fuel, and the kernel checks it in `Tick()` (chapter 2).

## Visual Studio

The exit criterion includes Visual Studio's MSBuild, which runs on .NET Framework.
The build integration tests (U13, `WARRANT_BUILD_INTEGRATION=1`) ran the `Increment` sample on three hosts and got the same diagnostics from each:

| Host | MSBuild | Tested with |
|---|---|---|
| `dotnet build` | 18.9.15 | a `net10.0` sample on SDK 10.0.403 |
| Visual Studio 2026 | 18.11.1.51303 | a `net10.0` sample on SDK 10 |
| Visual Studio 2022 | 17.14.60.43110 | a `net8.0` sample pinned to SDK 9.0.320 by its own `global.json`: SDK 10 on this MSBuild fails with "requires at least version 18.0.0 of MSBuild" (confirmed) |

The tests locate Visual Studio with `vswhere` and report a host they cannot find as skipped with a reason, never as passed.
How the Error List in the Visual Studio IDE shows a multi-line message is a manual check, and it has not been done yet.
