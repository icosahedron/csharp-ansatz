# Shared by the scripts in scripts/: make the Lean toolchain used by the test corpus available.
#
#   source scripts/lib/lean-toolchain.sh
#   ensure_lean_toolchain WORKDIR     # puts lean/lake on PATH
#
# If LEAN_TOOLCHAIN_BIN is set, that directory is used instead of downloading.
LEAN_VERSION="4.33.1"
LEAN4EXPORT_COMMIT="15f6055e299ad5b89345e533cc2192f4cc00f659"   # last lean4export commit pinned to Lean v4.33

ensure_lean_toolchain() {
  local workdir="$1"
  if [ -n "${LEAN_TOOLCHAIN_BIN:-}" ]; then
    export PATH="$LEAN_TOOLCHAIN_BIN:$PATH"
    return
  fi
  mkdir -p "$workdir"
  if [ ! -x "$workdir/lean-$LEAN_VERSION-linux/bin/lean" ]; then
    echo "downloading Lean $LEAN_VERSION…" >&2
    curl -sSfL -o "$workdir/lean.zip" "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/lean-$LEAN_VERSION-linux.zip"
    (cd "$workdir" && unzip -q lean.zip && rm lean.zip)
  fi
  export PATH="$workdir/lean-$LEAN_VERSION-linux/bin:$PATH"
}
