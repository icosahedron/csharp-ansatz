#!/usr/bin/env bash
# Cross-kernel check: compare LeanSharp's kernel with Lean's own kernel.
#
#   scripts/cross-check.sh [WORKDIR]
#
# For every file in the test corpus:
#   1. Lean's kernel (tools/lean-replay) checks the original file;
#   2. LeanSharp's kernel checks it; the two verdicts must agree;
#   3. LeanSharp writes out what it admitted (its own generated constructors and
#      recursors), and Lean's kernel must accept that file.
# Then declarations built from scratch in C# (tests/.../CrossCheckFixtures.cs: recursive,
# mutual, nested, structure, universe-polymorphic and K-like types) are written by LeanSharp
# and must be accepted by Lean, which re-derives every recursor and compares it with ours.
#
# Set LEANSHARP_INIT_EXPORT to a full-Init export (scripts/export-lean-library.sh) to include it.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/lib/lean-toolchain.sh

WORKDIR="$(realpath -m "${1:-${TMPDIR:-/tmp}/leansharp-lean}")"
OUT="$WORKDIR/cross-check"
mkdir -p "$OUT"
ensure_lean_toolchain "$WORKDIR"

echo "building tools…" >&2
(cd tools/lean-replay && lake build >/dev/null)
dotnet build -c Release src/LeanSharp.Cli -v q >/dev/null
LEAN=tools/lean-replay/.lake/build/bin/lean-replay
LEANSHARP=(dotnet src/LeanSharp.Cli/bin/Release/net10.0/leansharp.dll)

verdict() { case "$1" in 0) echo accept;; 1) echo reject;; *) echo decline;; esac; }
failures=0
row() { printf '%-28s %-9s %-9s %-14s %s\n' "$@"; }
row FILE LEAN LEANSHARP "LEAN(EXPORT)" RESULT

files=(tests/data/init-medium.ndjson.gz tests/data/Nat.add_succ.ndjson tests/data/arena/*.ndjson)
if [ -n "${LEANSHARP_INIT_EXPORT:-}" ]; then files+=("$LEANSHARP_INIT_EXPORT"); fi

for f in "${files[@]}"; do
  name="$(basename "$f")"
  input="$f"
  if [[ "$f" == *.gz ]]; then input="$OUT/${name%.gz}"; gzip -dc "$f" > "$input"; fi
  set +e
  "$LEAN" "$input" > "$OUT/$name.lean.txt" 2>&1; lean=$(verdict $?)
  "${LEANSHARP[@]}" export "$f" "$OUT/$name.leansharp.ndjson" --quiet > "$OUT/$name.leansharp.txt" 2>&1; ls=$(verdict $?)
  "$LEAN" "$OUT/$name.leansharp.ndjson" > "$OUT/$name.export.txt" 2>&1; exported=$(verdict $?)
  set -e
  result=ok
  # Lean's parser reads only format 3.1.0, so it declines 3.0.0 originals; the export is 3.1.0.
  if [ "$lean" != decline ] && [ "$lean" != "$ls" ]; then result="VERDICTS DIFFER"; fi
  if [ "$exported" != accept ]; then result="LEAN REJECTS LEANSHARP EXPORT"; fi
  [ "$result" = ok ] || failures=$((failures + 1))
  row "$name" "$lean" "$ls" "$exported" "$result"
done

set +e
LEANSHARP_CROSSCHECK_OUT="$OUT/fixtures.ndjson" dotnet test tests/LeanSharp.Kernel.Tests -c Release \
  --filter "FullyQualifiedName~CrossCheckTests" > "$OUT/fixtures.test.txt" 2>&1; ls=$(verdict $?)
"$LEAN" "$OUT/fixtures.ndjson" > "$OUT/fixtures.lean.txt" 2>&1; lean=$(verdict $?)
set -e
result=ok
if [ "$ls" != accept ] || [ "$lean" != accept ]; then result="FIXTURES FAILED"; failures=$((failures + 1)); fi
row "C# fixtures" "-" "$ls" "$lean" "$result"

echo
echo "details in $OUT"
if [ "$failures" -gt 0 ]; then echo "$failures disagreement(s)"; exit 1; fi
echo "all verdicts agree"
