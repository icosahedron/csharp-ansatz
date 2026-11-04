#!/usr/bin/env bash
# Cross-kernel check: compare Warrant's verdicts with independent kernels (KTD27, ticket d953584).
#
#   scripts/cross-kernel.sh [WORKDIR]
#
# Kernels, one column each:
#   LEAN            Lean's own kernel (tools/lean-replay), run here;
#   WARRANT         Warrant's kernel (`warrant export`, which checks exactly as `warrant check` does and
#                   then writes what it admitted; on a written export, `warrant check`);
#   ANSATZ          Ansatz's `arena-check --fuel 100000000`, run here when ANSATZ_DIR (default ../ansatz)
#                   holds a built Ansatz checkout (`clojure -T:build javac`) and `clojure` is on PATH;
#                   otherwise SKIPPED;
#   ARENA-OFFICIAL, NANODA, LEAN4LEAN
#                   the verdicts lean-kernel-arena publishes in results.json (arena tests only).
# A decline, timeout or checker error is no verdict.
#
# Rows:
#   - every lean-kernel-arena test in the downloaded tarball whose SHA-256 matches results.json
#     (scripts/lib/arena.sh), compared with the arena's expected outcome; `either` is recorded, not judged;
#   - init-medium, Nat.add_succ and tests/data/arena/*, compared with their known outcome;
#   - Warrant's export of each of the above (what it admitted), which every kernel must accept;
#   - the declarations built in C# (CrossCheckFixtures.cs), the translated M4 corpus and the M5a certificate
#     (`warrant verify tests/corpus/m5a/accepted`), which must be accepted;
#   - the M5a certificate with one proof replaced, which must be rejected.
#
# The script exits 1 when Warrant's verdict contradicts a row's expected outcome, or when Lean rejects what
# Warrant admitted. Other kernels' disagreements are listed for docs/kernel.md and do not fail the run.
# The table is also written as tab-separated values to WORKDIR/cross-kernel/verdicts.tsv.
#
# Environment: LEAN_TOOLCHAIN_BIN (see scripts/lib/lean-toolchain.sh), ANSATZ_DIR, ARENA_REFRESH=1 to download
# the arena files again, KERNEL_TIMEOUT (seconds per kernel run, default 900), ARENA_ONLY=1 to run only
# the arena tests, CORPUS_ONLY=1 to skip them (and their download).
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/lib/lean-toolchain.sh
source scripts/lib/arena.sh

WORKDIR="$(realpath -m "${1:-${TMPDIR:-/tmp}/warrant-lean}")"
OUT="$WORKDIR/cross-kernel"
LOGS="$OUT/logs"
mkdir -p "$LOGS" "$OUT/exports"
ensure_lean_toolchain "$WORKDIR"
KERNEL_TIMEOUT="${KERNEL_TIMEOUT:-900}"

echo "building tools…" >&2
(cd tools/lean-replay && lake build >/dev/null)
dotnet build -c Release src/Warrant.Cli -v q >/dev/null
LEAN=tools/lean-replay/.lake/build/bin/lean-replay
WARRANT=(dotnet src/Warrant.Cli/bin/Release/net10.0/warrant.dll)

ANSATZ_DIR="${ANSATZ_DIR:-../ansatz}"
ansatz_skip=""
if ! command -v clojure >/dev/null 2>&1; then
  ansatz_skip="no clojure on PATH"
elif [ ! -d "$ANSATZ_DIR/classes/ansatz" ]; then
  ansatz_skip="no built Ansatz at $ANSATZ_DIR (clojure -T:build javac)"
else
  ANSATZ_DIR="$(realpath "$ANSATZ_DIR")"
  echo "Ansatz $(git -C "$ANSATZ_DIR" rev-parse --short HEAD 2>/dev/null || echo '?') at $ANSATZ_DIR" >&2
fi
[ -z "$ansatz_skip" ] || echo "Ansatz SKIPPED: $ansatz_skip" >&2

if [ -z "${CORPUS_ONLY:-}" ]; then fetch_arena "$WORKDIR"; else ARENA_COMMIT="- (CORPUS_ONLY)"; fi

# run LOG CMD… : runs one kernel with the time limit and prints its verdict (accept, reject, decline,
# timeout or error), keeping its output in LOG.
run() {
  local log="$1"; shift
  local code=0 start end
  start=$(date +%s%N)
  timeout "$KERNEL_TIMEOUT" "$@" > "$log" 2>&1 || code=$?
  end=$(date +%s%N)
  echo "exit $code, $(( (end - start) / 1000000 )) ms" >> "$log"
  case "$code" in
    0) echo accept;; 1) echo reject;; 2) echo decline;; 124) echo timeout;; *) echo error;;
  esac
}
lean_v()   { run "$LOGS/$1.lean.txt" "$LEAN" "$2"; }
ansatz_v() {
  if [ -n "$ansatz_skip" ]; then echo SKIPPED; return; fi
  local file; file="$(realpath "$2")"
  if command -v cygpath >/dev/null 2>&1; then file="$(cygpath -w "$file")"; fi
  (cd "$ANSATZ_DIR" && run "$LOGS/$1.ansatz.txt" clojure -J-Xmx8g -M:arena --fuel 100000000 "$file")
}

verdict_row() { printf '%-60s %-8s %-8s %-8s %-14s %-8s %-9s %s\n' "$@"; }
verdict_row FILE LEAN WARRANT ANSATZ ARENA-OFFICIAL NANODA LEAN4LEAN RESULT
printf 'file\texpected\tlean\twarrant\tansatz\tofficial\tnanoda\tlean4lean\tresult\n' > "$OUT/verdicts.tsv"
failures=0
noted=0

# judge NAME EXPECTED LEAN WARRANT ANSATZ OFFICIAL NANODA LEAN4LEAN [EXPORT]: prints the row and records it.
# EXPECTED is accept, reject or either. A kernel gives no verdict unless it says accept or reject.
judge() {
  local name="$1" expected="$2" lean="$3" warrant="$4" ansatz="$5" official="$6" nanoda="$7" l4l="$8" is_export="${9:-}"
  local differ=() result
  local -A kernels=([lean]="$lean" [warrant]="$warrant" [ansatz]="$ansatz" [official]="$official" [nanoda]="$nanoda" [lean4lean]="$l4l")
  if [ "$expected" = either ]; then
    result="either (recorded)"
  else
    for k in lean warrant ansatz official nanoda lean4lean; do
      case "${kernels[$k]}" in accept|reject) [ "${kernels[$k]}" = "$expected" ] || differ+=("$k");; esac
    done
    if [ "$warrant" != accept ] && [ "$warrant" != reject ]; then differ+=("warrant:$warrant"); fi
    if [ ${#differ[@]} -eq 0 ]; then result=ok; else result="DIFFERS from $expected: ${differ[*]}"; fi
    if [ "$warrant" = accept ] || [ "$warrant" = reject ]; then
      if [ "$warrant" != "$expected" ]; then result="WARRANT WRONG, $result"; failures=$((failures + 1)); fi
    fi
    if [ -n "$is_export" ] && [ "$lean" = reject ]; then result="LEAN REJECTS WARRANT EXPORT, $result"; failures=$((failures + 1)); fi
    [ "$result" = ok ] || noted=$((noted + 1))
  fi
  verdict_row "$name" "$lean" "$warrant" "$ansatz" "$official" "$nanoda" "$l4l" "$result"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$expected" "$lean" "$warrant" "$ansatz" "$official" "$nanoda" "$l4l" "$result" >> "$OUT/verdicts.tsv"
}

# check_file NAME FILE EXPECTED OFFICIAL NANODA LEAN4LEAN: the original row, then a row for Warrant's export.
# Runs a step that writes a file the next rows judge (`produce <name> <out> <log> <command...>`), after deleting the
# file a previous run left. A step that fails, or writes nothing, is a Warrant failure: a crash or a failed verify must
# not leave an older or partial file to be judged.
produce() {
  local name="$1" out="$2"; shift 2
  local v
  rm -f "$out"
  v="$(run "$@")"
  if [ "$v" != accept ] || [ ! -s "$out" ]; then
    echo "$name: the step that writes $(basename "$out") ended with $v (log $1)"
    failures=$((failures + 1))
    return 1
  fi
}

check_file() {
  local name="$1" file="$2" expected="$3" key="${1//\//_}"
  local input="$file" export="$OUT/exports/$key.warrant.ndjson"
  if [[ "$file" == *.gz ]]; then input="$OUT/exports/$key.ndjson"; gzip -dc "$file" > "$input"; fi
  rm -f "$export"
  local warrant; warrant=$(run "$LOGS/$key.warrant.txt" "${WARRANT[@]}" export "$input" "$export" --quiet)
  judge "$name" "$expected" "$(lean_v "$key" "$input")" "$warrant" "$(ansatz_v "$key" "$input")" "$4" "$5" "$6"
  if [ -s "$export" ]; then
    judge "$name (warrant export)" accept "$(lean_v "$key.export" "$export")" \
      "$(run "$LOGS/$key.export.warrant.txt" "${WARRANT[@]}" check "$export" --quiet)" \
      "$(ansatz_v "$key.export" "$export")" - - - export
  fi
}

if [ -z "${CORPUS_ONLY:-}" ]; then
  while IFS=$'\t' read -r file name outcome official nanoda l4l; do
    check_file "arena/$name" "$file" "$outcome" "$official" "$nanoda" "$l4l"
  done < "$ARENA_DIR/index.tsv"
fi

if [ -z "${ARENA_ONLY:-}" ]; then
  # Known outcomes of the committed corpus (tests/data/README.md): these are older exports of arena tests,
  # so their SHA-256s differ from results.json and the arena's published verdicts do not apply to them.
  for f in tests/data/init-medium.ndjson.gz tests/data/Nat.add_succ.ndjson tests/data/arena/*.ndjson; do
    case "$(basename "$f")" in
      init-medium.ndjson.gz|Nat.add_succ.ndjson|001_basicDef.ndjson|sparse-name-index.ndjson) expected=accept;;
      *) expected=reject;;
    esac
    check_file "${f#tests/data/}" "$f" "$expected" - - -
  done

  # Declarations built from scratch in C#, written by Warrant (as in scripts/cross-check.sh).
  fixtures_out="$OUT/exports/fixtures.ndjson"
  if command -v cygpath >/dev/null 2>&1; then fixtures_out="$(cygpath -w "$fixtures_out")"; fi
  if produce "C# fixtures" "$OUT/exports/fixtures.ndjson" "$LOGS/fixtures.build.txt" env WARRANT_CROSSCHECK_OUT="$fixtures_out" \
    dotnet test tests/Warrant.Kernel.Tests -c Release --filter "FullyQualifiedName~CrossCheckTests"; then
    judge "C# fixtures" accept "$(lean_v fixtures "$OUT/exports/fixtures.ndjson")" \
      "$(run "$LOGS/fixtures.warrant.txt" "${WARRANT[@]}" check "$OUT/exports/fixtures.ndjson" --quiet)" \
      "$(ansatz_v fixtures "$OUT/exports/fixtures.ndjson")" - - - export
  else
    judge "C# fixtures" accept - error - - - - export
  fi

  # The translated M4 corpus: the semantics bundle plus every translated definition and proved theorem.
  if produce "M4 corpus (translated)" "$OUT/exports/m4.ndjson" \
    "$LOGS/m4.translate.txt" "${WARRANT[@]}" translate tests/corpus/m4/accepted --out "$OUT/exports/m4.ndjson"; then
    judge "M4 corpus (translated)" accept "$(lean_v m4 "$OUT/exports/m4.ndjson")" \
      "$(run "$LOGS/m4.warrant.txt" "${WARRANT[@]}" check "$OUT/exports/m4.ndjson" --quiet)" \
      "$(ansatz_v m4 "$OUT/exports/m4.ndjson")" - - - export
  else
    judge "M4 corpus (translated)" accept - error - - - - export
  fi

  # The M5a certificate (docs/m5a/08): `warrant verify` proves the M5a corpus by its scripts and writes the bundle
  # plus every admitted declaration. Then the same certificate with the last theorem's proof replaced by the proof
  # of the theorem before it, which proves a different statement: every kernel must reject it.
  if produce "M5a certificate (verify)" "$OUT/exports/m5a.ndjson" \
    "$LOGS/m5a.verify.txt" "${WARRANT[@]}" verify tests/corpus/m5a/accepted --out "$OUT/exports/m5a.ndjson"; then
    judge "M5a certificate (verify)" accept "$(lean_v m5a "$OUT/exports/m5a.ndjson")" \
      "$(run "$LOGS/m5a.warrant.txt" "${WARRANT[@]}" check "$OUT/exports/m5a.ndjson" --quiet)" \
      "$(ansatz_v m5a "$OUT/exports/m5a.ndjson")" - - - export
    thms="$(grep -n '^{"thm":' "$OUT/exports/m5a.ndjson" | tail -2)"
    proof="$(echo "$thms" | head -1 | sed -E 's/.*"value":([0-9]+).*/\1/')"
    sed -E "$(echo "$thms" | tail -1 | cut -d: -f1)s/\"value\":[0-9]+/\"value\":$proof/" \
      "$OUT/exports/m5a.ndjson" > "$OUT/exports/m5a.tampered.ndjson"
    judge "M5a certificate, one proof replaced" reject "$(lean_v m5a.tampered "$OUT/exports/m5a.tampered.ndjson")" \
      "$(run "$LOGS/m5a.tampered.warrant.txt" "${WARRANT[@]}" check "$OUT/exports/m5a.tampered.ndjson" --quiet)" \
      "$(ansatz_v m5a.tampered "$OUT/exports/m5a.tampered.ndjson")" - - -
  else
    judge "M5a certificate (verify)" accept - error - - - - export
  fi
fi

echo
echo "arena commit $ARENA_COMMIT; Ansatz $([ -n "$ansatz_skip" ] && echo "SKIPPED ($ansatz_skip)" || echo ran)"
echo "details in $OUT (verdicts.tsv, logs/)"
echo "$noted row(s) with a disagreement or no Warrant verdict; each needs an entry in docs/kernel.md"
if [ "$failures" -gt 0 ]; then echo "$failures Warrant failure(s)"; exit 1; fi
echo "Warrant agrees with every expected outcome"
