#!/usr/bin/env bash
# Measure M5b's baselines for M8 (docs/m5b/08, "Baselines for M8"; plan KTD30) and print them as Markdown tables.
#
#   scripts/measure-m5b.sh [MATHLIB_NDJSON]
#
# For each M5a sample (tests/corpus/m5a/accepted, refuted, rejected) it runs `warrant verify --timings`, the CLI that a
# build's WarrantVerify task runs, in each mode:
#
#   cold        no server running: the CLI starts one (start, bundle load and connect are the "connect" column)
#   warm        server running, empty result cache
#   cache hit   the same cache again: lookups only
#   recheck     the same cache with --recheck: the kernel checks every cached proof again
#   in-process  --server off, no cache: M5a's path, bundle load included in the wall time
#
# "Wall" is the CLI process's wall time; "request" is the server's (or the in-process service's) time for the whole
# request; the per-unit columns come from the --timings lines. Server memory is read from `warrant server status` after
# the server starts (on an empty project) and after the warm, cache-hit and recheck runs of every sample.
#
# With a Mathlib lean4export NDJSON file (the argument, or MATHLIB_NDJSON), it also imports it into a trusted store and
# runs `warrant sample-store` on it: the import's time and the store's size, then the GC heap and working set after
# opening the store and looking up 1,000 random constants. The two are reported separately because the store's mapped
# pages count in the working set but are not managed memory. Without the file, that table is skipped.
#
# Environment:
#   MATHLIB_NDJSON  the Mathlib export, when no argument is given
#   MEASURE_DIR     the work directory (default: a new temporary one); the Mathlib store goes there, so it needs room
#   WARRANT_CLI     a built warrant.dll to measure (default: src/Warrant.Cli built in Release)
#
# The server runs on an endpoint of this run's own (WARRANT_SERVER_ENDPOINT) and is shut down on exit.
set -euo pipefail

repo="$(cd "$(dirname "$0")/.." && pwd)"
mathlib="${1:-${MATHLIB_NDJSON:-}}"
work="${MEASURE_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/warrant-measure.XXXXXX")}"
mkdir -p "$work"

if [ -z "${WARRANT_CLI:-}" ]; then
  echo "building the CLI (Release)..." >&2
  dotnet build "$repo/src/Warrant.Cli/Warrant.Cli.csproj" -c Release --nologo -v quiet -clp:NoSummary >&2
  WARRANT_CLI="$repo/src/Warrant.Cli/bin/Release/net10.0/warrant.dll"
fi

export WARRANT_SERVER_ENDPOINT="warrant-measure-$$-$RANDOM"
warrant() { dotnet "$WARRANT_CLI" "$@"; }
now_ms() { date +%s%3N; }

stop_server() {
  warrant server shutdown >/dev/null 2>&1 || true
  for _ in $(seq 1 300); do
    if warrant server status 2>/dev/null | grep -q '^No Warrant verification server is running'; then
      return
    fi
    sleep 0.1
  done
  echo "the server on $WARRANT_SERVER_ENDPOINT did not stop" >&2
  exit 1
}
trap 'warrant server shutdown >/dev/null 2>&1 || true' EXIT

samples=(accepted refuted rejected)
rm -rf "$work/cache" "$work/m5a" "$work/empty"
cp -r "$repo/tests/corpus/m5a" "$work/m5a"
mkdir -p "$work/empty"

rows=()
run_mode() {
  local mode="$1" sample="$2"
  shift 2
  local start end code=0 out
  start=$(now_ms)
  out="$(warrant verify "$work/m5a/$sample" --timings "$@")" || code=$?
  end=$(now_ms)
  if [ "$code" -gt 1 ]; then
    echo "warrant verify $sample ($mode) failed with exit code $code:" >&2
    echo "$out" >&2
    exit 1
  fi
  if echo "$out" | grep -q 'verification server unavailable'; then
    echo "warning: $sample ($mode) fell back to in-process verification" >&2
  fi
  rows+=("$(echo "$out" | awk -v mode="$mode" -v sample="$sample" -v wall=$((end - start)) '
    / connected (to the running server )?in [0-9.]+ ms$/ { connect = $(NF - 1) }
    /^timings \(.*\): [0-9.]+ ms for the request$/ { request = $3 }
    /^ +[0-9]+\.[0-9] ms  / { units++; sum += $1; if ($1 > max) max = $1 }
    END {
      printf "| %s | %s | %d | %s | %s | %d | %.1f | %.1f |", mode, sample, wall,
        connect == "" ? "-" : connect, request == "" ? "-" : request, units, units ? sum / units : 0, max
    }')")
}

memory_rows=()
memory() {
  memory_rows+=("$(warrant server status | awk -v label="$1" '
    /^GC heap/ { heap = $3 " " $4 }
    /^working set/ { ws = $3 " " $4 }
    /^cache/ { cache = $0; sub(/^cache +/, "", cache) }
    END { printf "| %s | %s | %s | %s |", label, heap, ws, cache }')")
}

for sample in "${samples[@]}"; do
  stop_server
  run_mode cold "$sample" --server auto --cache-dir "$work/cache/cold-$sample"
done

stop_server
warrant verify "$work/empty" --server auto >/dev/null
memory "after start (empty project)"
for sample in "${samples[@]}"; do
  run_mode warm "$sample" --server auto --cache-dir "$work/cache/$sample"
  run_mode "cache hit" "$sample" --server auto --cache-dir "$work/cache/$sample"
  run_mode recheck "$sample" --server auto --cache-dir "$work/cache/$sample" --recheck
done
memory "after the corpus (warm, cache hit and recheck of every sample)"
stop_server

for sample in "${samples[@]}"; do
  run_mode in-process "$sample" --server off
done

mathlib_rows=()
if [ -n "$mathlib" ]; then
  store="$work/mathlib-store"
  rm -rf "$store"
  start=$(now_ms)
  warrant import "$mathlib" --store "$store" >&2
  end=$(now_ms)
  size=$(du -sk "$store" | awk '{ if ($1 >= 1048576) printf "%.2f GB", $1 / 1048576; else printf "%.1f MB", $1 / 1024 }')
  mathlib_rows+=("| import (trusted) | $(awk -v ms=$((end - start)) 'BEGIN { printf "%.1f s", ms / 1000 }') | store $size |")
  sampled="$(warrant sample-store "$store" --count 1000 --seed 1)"
  echo "$sampled" >&2
  mathlib_rows+=("$(echo "$sampled" | awk '
    /^opened store/ { open = $(NF - 1) " ms" }
    /^looked up/ { lookup = $(NF - 4) " ms"; records = $(NF - 1) }
    /^GC heap/ { heap = $3 " MB"; ws = $7 " MB" }
    END { printf "| open, then 1,000 random lookups | open %s, lookups %s (%s records decoded) | GC heap %s, working set %s |", open, lookup, records, heap, ws }')")
fi

cores=$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN)
echo "## M5b baselines"
echo
echo "Machine: $(uname -s) $(uname -r) ($(uname -m)), $cores logical cores; .NET SDK $(dotnet --version); $(date -u '+%Y-%m-%d %H:%M UTC')"
echo
echo "| Mode | Sample | Wall (ms) | Connect (ms) | Request (ms) | Units | Mean per unit (ms) | Max per unit (ms) |"
echo "|---|---|---:|---:|---:|---:|---:|---:|"
printf '%s\n' "${rows[@]}"
echo
echo "| Server memory | GC heap | Working set | Counters |"
echo "|---|---|---|---|"
printf '%s\n' "${memory_rows[@]}"
echo
if [ ${#mathlib_rows[@]} -gt 0 ]; then
  echo "| Mathlib store ($(basename "$mathlib")) | Time | Size or memory |"
  echo "|---|---|---|"
  printf '%s\n' "${mathlib_rows[@]}"
else
  echo "Mathlib store: skipped (pass a Mathlib lean4export NDJSON file, or set MATHLIB_NDJSON)."
fi
