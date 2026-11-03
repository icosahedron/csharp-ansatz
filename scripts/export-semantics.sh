#!/usr/bin/env bash
# Export the Warrant semantics library (lean/) and the Init constants the
# translator emits, with their whole dependency closure, as the committed bundle
# tests/data/warrant-semantics.ndjson.gz (plan KTD2, docs/m4/01).
#
#   scripts/export-semantics.sh [OUTPUT.ndjson.gz] [WORKDIR]
#
# On Windows set LEAN_TOOLCHAIN_BIN to an elan toolchain's bin directory
# (REPRODUCING.md). The script fails if lean4export panics (a missing root makes
# it print PANIC and exit 0 otherwise) or if any exported declaration uses sorryAx.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/lib/lean-toolchain.sh

OUTPUT="$(realpath -m "${1:-tests/data/warrant-semantics.ndjson.gz}")"
WORKDIR="$(realpath -m "${2:-${TMPDIR:-/tmp}/warrant-lean}")"
ROOT="$PWD"

ensure_lean_toolchain "$WORKDIR"
if [ ! -d "$WORKDIR/lean4export" ]; then
  git clone -q https://github.com/leanprover/lean4export "$WORKDIR/lean4export"
fi
(cd "$WORKDIR/lean4export" && git checkout -q "$LEAN4EXPORT_COMMIT" && lake build >/dev/null)
exe="$WORKDIR/lean4export/.lake/build/bin/lean4export"
if [ -f "$exe.exe" ]; then exe="$(cygpath -m "$exe.exe")"; fi   # Windows: lake env needs a native path

mapfile -t roots < <(grep -v -E '^\s*(#|$)' "$ROOT/lean/bundle-roots.txt")

cd "$ROOT/lean"
lake build >/dev/null
raw="$WORKDIR/warrant-semantics.ndjson"
err="$WORKDIR/warrant-semantics.stderr"
set +e
LEAN_ABORT_ON_PANIC=1 lake env "$exe" Warrant -- "${roots[@]}" > "$raw" 2> "$err"
status=$?
set -e
if [ "$status" -ne 0 ] || grep -q PANIC "$err"; then
  cat "$err" >&2
  echo "lean4export failed (exit $status); is every name in lean/bundle-roots.txt a real constant?" >&2
  exit 1
fi
if grep -q '"sorryAx"' "$raw"; then
  echo "the bundle depends on sorryAx" >&2
  exit 1
fi
gzip -n -9 -c "$raw" > "$OUTPUT"
echo "wrote $OUTPUT (${#roots[@]} roots)"
