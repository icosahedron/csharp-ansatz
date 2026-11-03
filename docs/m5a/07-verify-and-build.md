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
  M->>W: WarrantVerify target (after CoreCompile)
  W->>W: write obj/warrant.csc.args (keep the last one if CoreCompile was skipped)
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
M5b replaces the child process with the server.

## Reproducing the compilation

Setting `ProvideCommandLineArgs` makes the `Csc` task output its full argument list as `@(CscCommandLineArgs)`, already resolved: sources, references, `/define:`, `/langversion:`, `/checked`, `/nullable`, `/unsafe`, `/features:` and analyzer configuration.
Visual Studio's own project system uses the same output for design-time builds.
The task writes the list to `obj/warrant.csc.args`, one argument per line, and the CLI parses it with Roslyn's `CSharpCommandLineParser`, so the compilation has exactly the options the compiler used.

Three details follow:

- **Skipped compiles.** When `CoreCompile` is up to date, Csc does not run and the item is empty, so the task reuses the file from the last compile.
- **Real defines.** With the compiler's `/define:` list, extraction no longer compares every combination of `#if` symbols (M4 docs/m4/03); code is translated under the build's actual configuration. The combination check stays for `warrant verify <directory>` and `translate`, which have no compiler arguments, and for multi-targeted projects (below).
- **Source generators.** Generated sources exist only inside Csc and are not in the arguments. A project whose code does not compile without them fails with WRT0012 naming the missing symbols, rather than a verification of different code or a green build with nothing checked. Setting `EmitCompilerGeneratedFiles` makes Csc write them to disk; picking them up from there is follow-up work.

## `warrant verify`

```text
warrant verify --csc-args <file> [--project-dir <dir>] [options]
warrant verify <directory>       [options]                 # M4 corpus settings, like translate

options:
  --format text|msbuild           default text
  --out <file.ndjson>             write certificates: the bundle and every admitted declaration
  --report <dir>                  write report.md and report.json
  --kernel-fuel <n> --tactic-fuel <n> --timeout <seconds>
```

The text format matches `translate`'s: one line per unit, diagnostics in `path(line,col): error WRTnnnn: message` form, then a summary:

```text
Warrant: 12 verified units, 7 theorems proved, 1 not proved.
```

`--format msbuild` writes one record per diagnostic, with the code, file, line, column, end position and message, so a multi-line goal stays one event (KTD20).
Exit codes are 0 when every theorem is proved (warnings allowed), 1 when at least one error was reported, and 2 for bad arguments or an internal error.

The reference lists `warrant verify <project>`.
Evaluating a project file needs MSBuild, so M5a takes the argument file the build writes, or a directory; a project mode is follow-up work.

## The task and its targets

The `Warrant.Build` package's targets, in outline:

```xml
<PropertyGroup>
  <WarrantEnabled Condition="'$(WarrantEnabled)' == ''">true</WarrantEnabled>
  <ProvideCommandLineArgs Condition="'$(WarrantEnabled)' == 'true'">true</ProvideCommandLineArgs>
</PropertyGroup>

<Target Name="WarrantVerify" AfterTargets="CoreCompile"
        Condition="'$(WarrantEnabled)' == 'true' and '$(DesignTimeBuild)' != 'true'">
  <WriteLinesToFile Condition="'@(CscCommandLineArgs)' != ''"
                    File="$(IntermediateOutputPath)warrant.csc.args" Lines="@(CscCommandLineArgs)" Overwrite="true" />
  <WarrantVerify CscArgsFile="$(IntermediateOutputPath)warrant.csc.args"
                 ProjectDirectory="$(MSBuildProjectDirectory)"
                 KernelFuel="$(WarrantKernelFuel)" TacticFuel="$(WarrantTacticFuel)"
                 TimeoutSeconds="$(WarrantTimeoutSeconds)" />
</Target>
```

The target has no `Inputs` and `Outputs`, so every build verifies again (KTD22).
Skipping an unchanged project would be a cache keyed on timestamps, and the CI trust decision for M5a is that every build re-checks every proof (Key Decisions).
In a multi-targeted project the target runs in the inner build of the first target framework only, so diagnostics are not repeated, and it asks the CLI to keep M4's `#if` combination check, so a verified method whose meaning differs under `#if NET8_0` is rejected instead of being proved for one framework and shipped unproved for the other.
Design-time builds, which Visual Studio runs constantly in the background, skip it.

The task launches the CLI, which the package carries framework-dependent under `tools/net10.0/any/`, as `dotnet warrant.dll`, using `$(DOTNET_HOST_PATH)` and falling back to `dotnet` on the path.
The build machine therefore needs the .NET 10 runtime even for a project that targets `net8.0`; a missing runtime is reported as WRT0010 with the host's message.

`LogEventsFromTextOutput` parses each record and calls `Log.LogError` with the code, file, line, column and message.
Visual Studio's Error List shows only the first line of a message, so the first line is complete on its own (theorem, outcome, counterexample), and the goal follows on the next lines and is also logged as a high-importance message, so it is in the build output either way.
When the CLI exits with 2, the task logs WRT0010 with the tail of its error output, and suppresses MSBuild's generic "exited with code 2" error.

## Noticing that nothing ran

A project that references `Warrant` but does not reference `Warrant.Build`, or sets `WarrantEnabled` to false, builds green with nothing checked.
The `Warrant` package's `build/` targets warn in that case (WRT0011, KTD23), and every verified build prints its summary line, so a build log always shows whether theorems were checked.
MSBuild cannot see whether a project has `[Verified]` code, so the warning does not try; a project that references `Warrant` for another reason silences it with `NoWarn`.
Both packages use `build/`, not `buildTransitive/`, so an application that only references a verified library neither warns nor verifies the library again.

## Diagnostics

| Code | Meaning in M5a |
|---|---|
| WRT0001 | A theorem, or a decrease obligation, was not proved. Shows the remaining goals, and a counterexample when the search finds one. |
| WRT0002 to WRT0005, WRT0008, WRT0009 | As in M4, raised by extraction. WRT0002 now also names `recursion without Spec.Decreases` and `mutual recursion`; WRT0004 covers malformed scripts. |
| WRT0006 | A theorem ran out of kernel fuel, tactic fuel or time; the message says which. |
| WRT0010 | Internal error: the kernel rejected a term Warrant built, Meta failed unexpectedly, or the CLI crashed. Report it as a bug. |
| WRT0011 (warning) | Verification is not enabled for a project that references `Warrant`. |
| WRT0012 | The compilation could not be reproduced from Csc's arguments, for example because the code needs a source generator's output. Names the missing symbols. |

The engine never reports an unproved claim as false.
WRT0001 says a theorem "could not be proved"; a counterexample, when one is found, is what shows it is false.

## Budgets

Each theorem runs with three limits (Key Decisions, KTD24):

| Limit | Default | MSBuild property | Per theorem |
|---|---|---|---|
| kernel fuel | 20M steps (100M in corpus tests) | `WarrantKernelFuel` | `[Theorem(KernelFuel = …)]` |
| tactic fuel | 910 steps: ten times the largest use in the M5a corpus and U11's tests (91), measured in U11 and again by each unit that adds a tactic | `WarrantTacticFuel` | `[Theorem(TacticFuel = …)]` |
| wall clock | 30 s | `WarrantTimeoutSeconds` | `[Theorem(TimeoutSeconds = …)]` |

Exhausting any of them fails the theorem with WRT0006 and never counts as a proof.
The wall clock covers both Meta and the kernel: Meta checks the deadline wherever it charges fuel, and the kernel checks it in `Tick()` (chapter 2).

## Visual Studio

The exit criterion includes Visual Studio's MSBuild, which runs on .NET Framework.
The development machine has two installs:

| Host | MSBuild | Tested with |
|---|---|---|
| Visual Studio 2026 | 18.11 | a `net10.0` sample on SDK 10 |
| Visual Studio 2022 | 17.14 | a `net8.0` sample pinned to SDK 9 by its own `global.json`, because SDK 10 expects MSBuild 18 (U13 confirms this) |

The build integration tests (U13) locate them with `vswhere` and report a host they cannot find as skipped with a reason, never as passed.
The Error List's rendering of a multi-line message is checked by hand once and recorded in the pull request.
