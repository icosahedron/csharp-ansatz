#!/usr/bin/env bash
# Export the Lean attributes of the semantics bundle's constants (simp, congr, instances,
# reducibility, defeq, matchers, classes, and mvcgen's @[spec] lemmas, M6 KTD15) as the committed sidecar
# tests/data/warrant-attributes.ndjson.gz (plan KTD9, docs/m5a/05), with
# tools/warrant-attrs/Main.lean on the same toolchain and library as export-semantics.sh.
#
#   scripts/export-attributes.sh [OUTPUT.ndjson.gz] [WORKDIR] [BUNDLE.ndjson.gz]
#
# Run it after export-semantics.sh: the sidecar keeps only constants in the bundle and its header
# records the bundle's SHA-256, which the loader checks. On Windows set LEAN_TOOLCHAIN_BIN to an
# elan toolchain's bin directory (REPRODUCING.md). The export is deterministic: an unchanged
# library and bundle give a byte-identical file.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/lib/lean-toolchain.sh

OUTPUT="$(realpath -m "${1:-tests/data/warrant-attributes.ndjson.gz}")"
WORKDIR="$(realpath -m "${2:-${TMPDIR:-/tmp}/warrant-lean}")"
BUNDLE="$(realpath -m "${3:-tests/data/warrant-semantics.ndjson.gz}")"
ROOT="$PWD"

native() { if command -v cygpath >/dev/null; then cygpath -m "$1"; else echo "$1"; fi; }

ensure_lean_toolchain "$WORKDIR"
raw_bundle="$WORKDIR/warrant-attributes-bundle.ndjson"
raw="$WORKDIR/warrant-attributes.ndjson"
gzip -d -c "$BUNDLE" > "$raw_bundle"
sha="$(sha256sum "$BUNDLE" | cut -d' ' -f1)"

cd "$ROOT/lean"
lake build >/dev/null
lake env lean --run "$(native "$ROOT/tools/warrant-attrs/Main.lean")" \
  "$(native "$raw_bundle")" "$sha" Init Std.Do Warrant > "$raw"
gzip -n -9 -c "$raw" > "$OUTPUT"
echo "wrote $OUTPUT ($(($(wc -l < "$raw") - 1)) entries)"
