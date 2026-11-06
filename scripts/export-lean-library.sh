#!/usr/bin/env bash
# Export a Lean library (default: Init) to lean4export NDJSON, using the same
# toolchain pinned in lib/lean-toolchain.sh (lean4export format 3.1.0).
#
#   scripts/export-lean-library.sh [MODULE] [OUTPUT] [WORKDIR]
#
# Metadata (mdata) is exported, as scripts/export-semantics.sh exports the bundle, so the Init constants the
# bundle repeats are identical to this export's and `warrant import init.ndjson warrant-semantics.ndjson.gz`
# can build an Init + semantics store (M5b KTD20). Set EXPORT_MDATA=0 for an export without it.
#
# Then run the kernel over it:
#   WARRANT_INIT_EXPORT=$PWD/init.ndjson dotnet test --filter AcceptsFullInit
set -euo pipefail
source "$(dirname "$0")/lib/lean-toolchain.sh"

MODULE="${1:-Init}"
OUTPUT="$(realpath -m "${2:-init.ndjson}")"
WORKDIR="$(realpath -m "${3:-${TMPDIR:-/tmp}/warrant-lean}")"

ensure_lean_toolchain "$WORKDIR"
cd "$WORKDIR"
if [ ! -d lean4export ]; then
  git clone -q https://github.com/leanprover/lean4export lean4export
fi
cd lean4export
git checkout -q "$LEAN4EXPORT_COMMIT"
lake build
exe="$PWD/.lake/build/bin/lean4export"
if [ -f "$exe.exe" ]; then exe="$(cygpath -m "$exe.exe")"; fi   # Windows: lake env needs a native path
flags=()
if [ "${EXPORT_MDATA:-1}" != 0 ]; then flags+=(--export-mdata); fi
lake env "$exe" "${flags[@]}" "$MODULE" > "$OUTPUT"
echo "wrote $OUTPUT"
