#!/usr/bin/env bash
# Export a Lean library (default: Init) to lean4export NDJSON, using the same
# toolchain as the committed test corpus (Lean 4.33.1, lean4export 3.1.0).
#
#   scripts/export-lean-library.sh [MODULE] [OUTPUT] [WORKDIR]
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
lake env .lake/build/bin/lean4export "$MODULE" > "$OUTPUT"
echo "wrote $OUTPUT"
