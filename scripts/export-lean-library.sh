#!/usr/bin/env bash
# Export a Lean library (default: Init) to lean4export NDJSON, using the same
# toolchain as the committed test corpus (Lean 4.33.1, lean4export 3.1.0).
#
#   scripts/export-lean-library.sh [MODULE] [OUTPUT] [WORKDIR]
#
# Then run the kernel over it:
#   LEANSHARP_INIT_EXPORT=$PWD/init.ndjson dotnet test --filter AcceptsFullInit
set -euo pipefail

MODULE="${1:-Init}"
OUTPUT="$(realpath -m "${2:-init.ndjson}")"
WORKDIR="$(realpath -m "${3:-${TMPDIR:-/tmp}/leansharp-export}")"
LEAN_VERSION="4.33.1"
LEAN4EXPORT_COMMIT="15f6055"   # last lean4export commit pinned to Lean v4.33.x

mkdir -p "$WORKDIR"
cd "$WORKDIR"

if [ ! -x "lean-$LEAN_VERSION-linux/bin/lean" ]; then
  curl -sSfL -o lean.zip "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/lean-$LEAN_VERSION-linux.zip"
  unzip -q lean.zip && rm lean.zip
fi
export PATH="$WORKDIR/lean-$LEAN_VERSION-linux/bin:$PATH"

if [ ! -d lean4export ]; then
  git clone -q https://github.com/leanprover/lean4export lean4export
fi
cd lean4export
git checkout -q "$LEAN4EXPORT_COMMIT"
lake build
lake env .lake/build/bin/lean4export "$MODULE" > "$OUTPUT"
echo "wrote $OUTPUT"
