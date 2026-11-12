#!/usr/bin/env bash
# Cross-kernel check: compare Warrant's kernel with Lean's own kernel.
#
#   scripts/cross-check.sh [WORKDIR]
#
# For every file in the test corpus:
#   1. Lean's kernel (tools/lean-replay) checks the original file;
#   2. Warrant's kernel checks it; the two verdicts must agree;
#   3. Warrant writes out what it admitted (its own generated constructors and
#      recursors), and Lean's kernel must accept that file.
# Then declarations built from scratch in C# (tests/.../CrossCheckFixtures.cs: recursive,
# mutual, nested, structure, universe-polymorphic and K-like types) are written by Warrant
# and must be accepted by Lean, which re-derives every recursor and compares it with ours.
# Last, `warrant translate` translates the M4 corpus (tests/corpus/m4/accepted) and must succeed, and Lean's
# kernel must accept what it wrote: the semantics bundle plus every translated definition and proved theorem.
# Then `warrant verify` proves the M5a corpus (tests/corpus/m5a/accepted) by its scripts, and Lean's kernel must
# accept the certificate it wrote; a copy with one proof replaced must be rejected by both kernels. The same is done for
# the M6 corpus (tests/corpus/m6): its accepted members' certificate, ProcessPayment's contract among them, what Warrant
# admits from its refuted and rejected members, and a tampered copy.
#
# Set WARRANT_INIT_EXPORT to a full-Init export (scripts/export-lean-library.sh) to include it.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/lib/lean-toolchain.sh

WORKDIR="$(realpath -m "${1:-${TMPDIR:-/tmp}/warrant-lean}")"
OUT="$WORKDIR/cross-check"
mkdir -p "$OUT"
ensure_lean_toolchain "$WORKDIR"

echo "building tools…" >&2
(cd tools/lean-replay && lake build >/dev/null)
dotnet build -c Release src/Warrant.Cli -v q >/dev/null
LEAN=tools/lean-replay/.lake/build/bin/lean-replay
WARRANT=(dotnet src/Warrant.Cli/bin/Release/net10.0/warrant.dll)

verdict() { case "$1" in 0) echo accept;; 1) echo reject;; *) echo decline;; esac; }
failures=0
row() { printf '%-28s %-9s %-9s %-14s %s\n' "$@"; }
row FILE LEAN WARRANT "LEAN(EXPORT)" RESULT

files=(tests/data/init-medium.ndjson.gz tests/data/Nat.add_succ.ndjson tests/data/arena/*.ndjson)
if [ -n "${WARRANT_INIT_EXPORT:-}" ]; then files+=("$WARRANT_INIT_EXPORT"); fi

for f in "${files[@]}"; do
  name="$(basename "$f")"
  input="$f"
  if [[ "$f" == *.gz ]]; then input="$OUT/${name%.gz}"; gzip -dc "$f" > "$input"; fi
  set +e
  "$LEAN" "$input" > "$OUT/$name.lean.txt" 2>&1; lean=$(verdict $?)
  "${WARRANT[@]}" export "$f" "$OUT/$name.warrant.ndjson" --quiet > "$OUT/$name.warrant.txt" 2>&1; ls=$(verdict $?)
  "$LEAN" "$OUT/$name.warrant.ndjson" > "$OUT/$name.export.txt" 2>&1; exported=$(verdict $?)
  set -e
  result=ok
  # Lean's parser reads only format 3.1.0, so it declines 3.0.0 originals; the export is 3.1.0.
  if [ "$lean" != decline ] && [ "$lean" != "$ls" ]; then result="VERDICTS DIFFER"; fi
  if [ "$exported" != accept ]; then result="LEAN REJECTS WARRANT EXPORT"; fi
  [ "$result" = ok ] || failures=$((failures + 1))
  row "$name" "$lean" "$ls" "$exported" "$result"
done

set +e
WARRANT_CROSSCHECK_OUT="$OUT/fixtures.ndjson" dotnet test tests/Warrant.Kernel.Tests -c Release \
  --filter "FullyQualifiedName~CrossCheckTests" > "$OUT/fixtures.test.txt" 2>&1; ls=$(verdict $?)
"$LEAN" "$OUT/fixtures.ndjson" > "$OUT/fixtures.lean.txt" 2>&1; lean=$(verdict $?)
set -e
result=ok
if [ "$ls" != accept ] || [ "$lean" != accept ]; then result="FIXTURES FAILED"; failures=$((failures + 1)); fi
row "C# fixtures" "-" "$ls" "$lean" "$result"

# The M4 corpus (docs/m4/07): Warrant translates it, and Lean's kernel re-checks the bundle plus every admitted
# translated definition and proved theorem.
set +e
"${WARRANT[@]}" translate tests/corpus/m4/accepted --out "$OUT/m4.ndjson" > "$OUT/m4.translate.txt" 2>&1; ls=$(verdict $?)
"$LEAN" "$OUT/m4.ndjson" > "$OUT/m4.lean.txt" 2>&1; lean=$(verdict $?)
set -e
result=ok
if [ "$ls" != accept ] || [ "$lean" != accept ]; then result="M4 CORPUS FAILED"; failures=$((failures + 1)); fi
row "M4 corpus" "-" "$ls" "$lean" "$result"

# The M5a corpus (docs/m5a/08): `warrant verify` proves its theorems by their scripts and writes the certificate,
# the bundle plus every admitted declaration (quantified theorems with simp and omega proofs, recursive definitions
# with their decrease theorems and equation lemmas, generated casesOn and ctorIdx), which Lean's kernel re-checks.
set +e
"${WARRANT[@]}" verify tests/corpus/m5a/accepted --out "$OUT/m5a.ndjson" > "$OUT/m5a.verify.txt" 2>&1; ls=$(verdict $?)
"$LEAN" "$OUT/m5a.ndjson" > "$OUT/m5a.lean.txt" 2>&1; lean=$(verdict $?)
set -e
result=ok
if [ "$ls" != accept ] || [ "$lean" != accept ]; then result="M5A CORPUS FAILED"; failures=$((failures + 1)); fi
row "M5a corpus" "-" "$ls" "$lean" "$result"

# A tampered certificate: the last theorem's proof is replaced with the proof of the theorem before it, which proves
# a different statement. Both kernels must reject the file.
tampered="$OUT/m5a.tampered.ndjson"
thms="$(grep -n '^{"thm":' "$OUT/m5a.ndjson" | tail -2 || true)"
last_line="$(echo "$thms" | tail -1 | cut -d: -f1)"
proof="$(echo "$thms" | head -1 | sed -E 's/.*"value":([0-9]+).*/\1/')"
set +e
if [ "$(echo "$thms" | wc -l)" -eq 2 ]; then
  sed -E "${last_line}s/\"value\":[0-9]+/\"value\":$proof/" "$OUT/m5a.ndjson" > "$tampered"
  "${WARRANT[@]}" check "$tampered" --quiet > "$OUT/m5a.tampered.warrant.txt" 2>&1; ls=$(verdict $?)
  "$LEAN" "$tampered" > "$OUT/m5a.tampered.lean.txt" 2>&1; lean=$(verdict $?)
else
  ls=missing; lean=missing
fi
set -e
result=ok
if [ "$ls" != reject ] || [ "$lean" != reject ] || cmp -s "$OUT/m5a.ndjson" "$tampered"; then
  result="TAMPERED CERTIFICATE NOT REJECTED"; failures=$((failures + 1))
fi
row "M5a tampered" "-" "$ls" "$lean" "$result"

# The M6 corpus (plan M6 U14, R13): `warrant verify` proves the accepted members' contract obligations by the default
# procedure, design §5.2's ProcessPayment among them with its store as a hypothesis, and writes the certificate: the
# bundle with its Std closure plus every admitted definition and contract theorem, which Lean's kernel re-checks. The
# refuted and rejected compilations fail to verify, as they must, but what Warrant admitted from them (the definitions,
# and the contracts it did prove) must pass Lean's kernel too. Their checked-project members need overflow checking
# (#111), which only `warrant translate` sets for a directory, so they are translated with --check-overflow: their
# contracts are refuted either way, so the certificate is their definitions.
m6_row() { # name, expected Warrant verdict, Warrant's exit code, certificate
  local name="$1" want="$2" ls lean result=ok
  ls=$(verdict "$3")
  set +e
  "$LEAN" "$4" > "$4.lean.txt" 2>&1; lean=$(verdict $?)
  set -e
  if [ "$ls" != "$want" ] || [ "$lean" != accept ]; then result="M6 CORPUS FAILED"; failures=$((failures + 1)); fi
  row "$name" "-" "$ls" "$lean" "$result"
}
set +e
"${WARRANT[@]}" verify tests/corpus/m6/accepted --server off --out "$OUT/m6.ndjson" > "$OUT/m6.verify.txt" 2>&1; code=$?
set -e
# The exit criterion's certificate: ProcessPayment's contract theorem (the name …ProcessPayment(System.Int32).$contract)
# must be in it.
pp="$(grep -oE '^\{"in":[0-9]+,"str":\{"pre":[0-9]+,"str":"ProcessPayment\(System\.Int32\)"\}\}' "$OUT/m6.ndjson" | sed -E 's/^\{"in":([0-9]+).*/\1/' || true)"
contract="$(grep -oE "^\\{\"in\":[0-9]+,\"str\":\\{\"pre\":${pp:-none},\"str\":\"\\\$contract\"\\}\\}" "$OUT/m6.ndjson" | sed -E 's/^\{"in":([0-9]+).*/\1/' || true)"
if [ -z "$contract" ] || ! grep -qE "^\\{\"thm\":\\{.*\"name\":$contract," "$OUT/m6.ndjson"; then
  echo "the M6 certificate has no contract theorem for ProcessPayment" >&2; code=3
fi
m6_row "M6 corpus" accept "$code" "$OUT/m6.ndjson"
for sample in refuted rejected; do
  set +e
  "${WARRANT[@]}" verify "tests/corpus/m6/$sample" --server off --out "$OUT/m6-$sample.ndjson" > "$OUT/m6-$sample.verify.txt" 2>&1; code=$?
  set -e
  m6_row "M6 $sample" reject "$code" "$OUT/m6-$sample.ndjson"
done
rm -rf "$OUT/m6-checked" && mkdir -p "$OUT/m6-checked"
cp tests/corpus/m6/refuted/CheckedProject.cs "$OUT/m6-checked/"
set +e
"${WARRANT[@]}" translate "$OUT/m6-checked" --check-overflow --out "$OUT/m6-checked.ndjson" > "$OUT/m6-checked.translate.txt" 2>&1; code=$?
set -e
m6_row "M6 checked-project" reject "$code" "$OUT/m6-checked.ndjson"

# A tampered M6 certificate, as for M5a: ProcessPayment's contract theorem's proof is replaced with the proof of the
# theorem before it. Both kernels must reject the file.
tampered="$OUT/m6.tampered.ndjson"
thms="$(grep -n '^{"thm":' "$OUT/m6.ndjson" | grep -B1 -E "\"name\":${contract:-none}," | tail -2 || true)"
last_line="$(echo "$thms" | tail -1 | cut -d: -f1)"
proof="$(echo "$thms" | head -1 | sed -E 's/.*"value":([0-9]+).*/\1/')"
set +e
if [ "$(echo "$thms" | wc -l)" -eq 2 ]; then
  sed -E "${last_line}s/\"value\":[0-9]+/\"value\":$proof/" "$OUT/m6.ndjson" > "$tampered"
  "${WARRANT[@]}" check "$tampered" --quiet > "$OUT/m6.tampered.warrant.txt" 2>&1; ls=$(verdict $?)
  "$LEAN" "$tampered" > "$OUT/m6.tampered.lean.txt" 2>&1; lean=$(verdict $?)
else
  ls=missing; lean=missing
fi
set -e
result=ok
if [ "$ls" != reject ] || [ "$lean" != reject ] || cmp -s "$OUT/m6.ndjson" "$tampered"; then
  result="TAMPERED CERTIFICATE NOT REJECTED"; failures=$((failures + 1))
fi
row "M6 tampered" "-" "$ls" "$lean" "$result"

echo
echo "details in $OUT"
if [ "$failures" -gt 0 ]; then echo "$failures disagreement(s)"; exit 1; fi
echo "all verdicts agree"
