# Shared by scripts/cross-kernel.sh: fetch the lean-kernel-arena tests and the verdicts it publishes.
#
#   source scripts/lib/arena.sh
#   fetch_arena WORKDIR     # sets ARENA_DIR and ARENA_COMMIT, and writes $ARENA_DIR/index.tsv
#
# The arena (https://arena.lean-lang.org/) runs many independent kernels on every test and publishes each
# verdict in results.json, so no other kernel has to be built here. The tarball holds the tests under 10 MB.
# Both files are downloaded once into WORKDIR/arena (set ARENA_REFRESH=1 to download again), and the arena
# commit they were published from (results.json meta.git_revision) is written to WORKDIR/arena/commit.txt.
#
# index.tsv has one tab-separated line per test whose SHA-256 matches the one in results.json:
#   FILE  NAME  OUTCOME  OFFICIAL  NANODA  LEAN4LEAN
# FILE is the extracted test, NAME the arena's test name (e.g. bugs/rec-k-lie), OUTCOME accept, reject or
# either, and each kernel column is accept, reject, decline, timeout, error or - (no published result).
# A test whose SHA-256 differs, or that results.json does not list, is skipped with a message on stderr.
ARENA_TESTS_URL="https://arena.lean-lang.org/lean-arena-tests.tar.gz"
ARENA_RESULTS_URL="https://arena.lean-lang.org/results.json"

arena_python() {
  if command -v python3 >/dev/null 2>&1 && python3 -c '' >/dev/null 2>&1; then echo python3; else echo python; fi
}

fetch_arena() {
  ARENA_DIR="$1/arena"
  local download="$ARENA_DIR/download" tests="$ARENA_DIR/tests"
  mkdir -p "$download"
  if [ -n "${ARENA_REFRESH:-}" ] || [ ! -s "$download/results.json" ] || [ ! -s "$download/lean-arena-tests.tar.gz" ]; then
    echo "downloading the lean-kernel-arena tests and results…" >&2
    curl -sSfL -o "$download/results.json" "$ARENA_RESULTS_URL"
    curl -sSfL -o "$download/lean-arena-tests.tar.gz" "$ARENA_TESTS_URL"
    rm -rf "$tests"
  fi
  if [ ! -d "$tests" ]; then
    mkdir -p "$tests"
    tar -xzf "$download/lean-arena-tests.tar.gz" -C "$tests"
  fi
  # The downloaded files are data: Python runs isolated (-I) and gets them as arguments.
  "$(arena_python)" -I -X utf8 - "$download/results.json" "$tests" "$ARENA_DIR/index.tsv" "$ARENA_DIR/commit.txt" <<'PY'
import hashlib, json, os, sys

results_path, tests_dir, index_path, commit_path = sys.argv[1:5]
with open(results_path, encoding="utf-8") as f:
    results = json.load(f)
meta = results["meta"]
with open(commit_path, "w", encoding="utf-8") as f:
    f.write(f"{meta['git_revision']}\t{meta['timestamp']}\n")

tests = {t["name"]: t for t in results["tests"]}
status = {"accepted": "accept", "rejected": "reject", "declined": "decline", "timeout": "timeout", "error": "error"}
verdicts = {}
for r in results["results"]:
    verdicts[(r["checker"], r["test"])] = status.get(r["status"], r["status"])

rows, skipped = [], 0
for root, _, files in os.walk(tests_dir):
    for name in files:
        if not name.endswith(".ndjson"):
            continue
        path = os.path.join(root, name)
        rel = os.path.relpath(path, tests_dir).replace(os.sep, "/")
        test_name = rel.split("/", 1)[1][: -len(".ndjson")]   # good/bugs/x.ndjson -> bugs/x
        test = tests.get(test_name)
        if test is None:
            print(f"skipping {rel}: not listed in results.json", file=sys.stderr)
            skipped += 1
            continue
        with open(path, "rb") as f:
            digest = hashlib.sha256(f.read()).hexdigest()
        if digest != test["sha256"]:
            print(f"skipping {rel}: SHA-256 {digest[:12]}… differs from results.json's {test['sha256'][:12]}…", file=sys.stderr)
            skipped += 1
            continue
        published = [verdicts.get((c, test_name), "-") for c in ("official", "nanoda", "lean4lean")]
        rows.append([path.replace(os.sep, "/"), test_name, test["outcome"], *published])

rows.sort(key=lambda r: r[1])
with open(index_path, "w", encoding="utf-8", newline="\n") as f:
    for r in rows:
        f.write("\t".join(r) + "\n")
print(f"arena commit {meta['git_revision'][:12]} ({meta['timestamp']}): {len(rows)} tests, {skipped} skipped", file=sys.stderr)
PY
  ARENA_COMMIT="$(cut -f1 "$ARENA_DIR/commit.txt")"
}
