#!/bin/bash
# Parallel version of run_v2_benchmarks.sh: runs pyAnalyzeV2 over the corpus with -P workers.
# Usage: run_v2_benchmarks_par.sh [sample_per_set] [parallelism]  (0/empty sample = all)
cd "$(dirname "$0")" || exit 1
BIN="$PWD/.lake/build/bin/pyAnalyzeV2"
BENCH=/Users/somayyas/workspace/StrataPythonBuildBackendWS/src/StrataInternalBenchmarks
RAW=/tmp/v2_bench_raw.txt
SAMPLE="${1:-0}"
JOBS="${2:-7}"
: > "$RAW"

# Build the file list (with set label), one "set|path" per line.
LIST=$(mktemp)
for set in aws_samples ecc_examples bash_party_examples service_benchmarks; do
  ions=$(find "$BENCH/$set" -name "*.python.st.ion" 2>/dev/null | sort)
  [ "$SAMPLE" -gt 0 ] 2>/dev/null && ions=$(echo "$ions" | head -"$SAMPLE")
  for ion in $ions; do [ -f "$ion" ] && echo "$set|$ion"; done
done > "$LIST"
total=$(wc -l < "$LIST" | tr -d ' ')

# Worker: analyze one file, append a single atomic block to $RAW.
run_one() {
  local line="$1" BIN="$2" RAW="$3"
  local set="${line%%|*}" ion="${line#*|}"
  local out code
  out=$(timeout 90 "$BIN" --solver z3 --check-mode bugFinding --check-level full "$ion" 2>&1)
  code=$?
  { echo "===== [$set] $(basename "$ion") (exit $code) ====="
    echo "$out" | grep -E '^DETAIL:|^RESULT:' | tail -2
    [ $code -ne 0 ] && ! echo "$out" | grep -q '^RESULT:' && echo "  -> CRASH/timeout $code"
  } >> "$RAW"
}
export -f run_one

# -P workers, each gets one "set|path" line.
cat "$LIST" | xargs -P "$JOBS" -I {} bash -c 'run_one "$@"' _ {} "$BIN" "$RAW"
rm -f "$LIST"

echo ""
echo "============ pyAnalyzeV2 over StrataInternalBenchmarks (sample=$SAMPLE, jobs=$JOBS, total=$total) ============"
echo "--- overall ---"
grep '^RESULT:' "$RAW" | sort | uniq -c | sort -rn
echo "crash/timeout (no RESULT): $(grep -c 'CRASH/timeout' "$RAW")"
echo "TOTAL benchmarks run: $total   (results: $(grep -c '^=====' "$RAW"))"
echo "Raw: $RAW"
