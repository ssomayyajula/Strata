#!/bin/bash
# =============================================================================
# Differential Testing Infrastructure for Python -> Laurel Refactor
# =============================================================================
#
# Usage:
#   ./diff_test.sh baseline                  Capture old pipeline outputs
#   ./diff_test.sh compare [command]         Compare new pipeline against baseline
#   ./diff_test.sh single <testname>         Run both pipelines on one test
#   ./diff_test.sh summary                   Show stored results summary
#
# The baseline command stores results from pyAnalyzeLaurel.
# The compare command runs pyAnalyzeLaurelRefactored (or specified command)
# and diffs against stored baseline.
#
# Exit codes:
#   0 - No regressions
#   1 - Regressions found (or usage error)
# =============================================================================

set -o pipefail

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../../.." && pwd)"
STRATA_BIN="$ROOT_DIR/.lake/build/bin/strata"
TEST_DIR="$SCRIPT_DIR/tests"
BASELINE_DIR="$SCRIPT_DIR/baseline"
RESULTS_DIR="$SCRIPT_DIR/results"

# Pipeline commands
OLD_PIPELINE="pyAnalyzeLaurel"
NEW_PIPELINE="pyAnalyzeLaurelRefactored"

# Timeout per test (seconds)
TIMEOUT=10

# Parallelism
PARALLEL_JOBS=4

# Add cvc5 to PATH
export PATH="/Users/somayyas/bin:$PATH"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# Colors for terminal output (disabled if not a tty)
if [ -t 1 ]; then
    RED='\033[0;31m'
    GREEN='\033[0;32m'
    YELLOW='\033[0;33m'
    BLUE='\033[0;34m'
    BOLD='\033[1m'
    RESET='\033[0m'
else
    RED='' GREEN='' YELLOW='' BLUE='' BOLD='' RESET=''
fi

die() {
    echo "ERROR: $*" >&2
    exit 1
}

usage() {
    echo "Usage: $0 <command> [args...]"
    echo ""
    echo "Commands:"
    echo "  baseline              Capture old pipeline (pyAnalyzeLaurel) results"
    echo "  compare [cmd]         Compare new pipeline against baseline"
    echo "                        Default cmd: pyAnalyzeLaurelRefactored"
    echo "  single <testname>     Run both pipelines on a single test"
    echo "  summary               Show summary of last comparison results"
    echo "  list                  List all available test files"
    echo ""
    echo "Examples:"
    echo "  $0 baseline"
    echo "  $0 compare"
    echo "  $0 compare pyAnalyzeLaurelRefactored"
    echo "  $0 single test_arithmetic"
    echo "  $0 summary"
    exit 1
}

# Extract test name from file path: test_foo.python.st.ion -> test_foo
testname_from_file() {
    local f="$1"
    basename "$f" .python.st.ion
}

# Get all test files
get_test_files() {
    find "$TEST_DIR" -name '*.python.st.ion' -type f | sort
}

# Run a pipeline command on a test file with timeout.
# Captures stdout, stderr, and exit code.
# Arguments: <strata_command> <test_file> <stdout_file> <stderr_file>
# Returns: exit code of the pipeline
run_pipeline() {
    local cmd="$1"
    local test_file="$2"
    local stdout_file="$3"
    local stderr_file="$4"

    # Run from the repo root so relative paths in strata work
    (cd "$ROOT_DIR" && \
        timeout "$TIMEOUT" "$STRATA_BIN" "$cmd" "$test_file" \
            >"$stdout_file" 2>"$stderr_file"
    )
    return $?
}

# Classify a pipeline result based on exit code and output.
# Prints one of: pass, fail, error, timeout, crash
classify_result() {
    local exit_code="$1"
    local stdout_file="$2"

    if [ "$exit_code" -eq 124 ]; then
        echo "timeout"
        return
    fi

    # Check for RESULT line in output (structured output from pyAnalyzeLaurel)
    local result_line
    result_line=$(grep '^RESULT:' "$stdout_file" 2>/dev/null | tail -1)

    if [ -n "$result_line" ]; then
        case "$result_line" in
            *"Analysis success"*)  echo "pass" ;;
            *"Inconclusive"*)      echo "inconclusive" ;;
            *"Failures found"*)    echo "fail" ;;
            *"User error"*)        echo "user_error" ;;
            *"Known limitation"*)  echo "known_limitation" ;;
            *"Internal error"*)    echo "internal_error" ;;
            *)                     echo "unknown" ;;
        esac
    elif [ "$exit_code" -eq 0 ]; then
        echo "pass"
    elif [ "$exit_code" -eq 1 ]; then
        echo "user_error"
    elif [ "$exit_code" -eq 2 ]; then
        echo "fail"
    elif [ "$exit_code" -eq 3 ]; then
        echo "internal_error"
    elif [ "$exit_code" -eq 4 ]; then
        echo "known_limitation"
    else
        echo "crash"
    fi
}

# ---------------------------------------------------------------------------
# Phase 1: Capture Baseline
# ---------------------------------------------------------------------------

cmd_baseline() {
    echo -e "${BOLD}=== Capturing Baseline (${OLD_PIPELINE}) ===${RESET}"
    echo ""

    # Verify strata binary exists
    [ -x "$STRATA_BIN" ] || die "Strata binary not found at: $STRATA_BIN"

    # Create baseline directory
    mkdir -p "$BASELINE_DIR"

    local total=0
    local succeeded=0
    local failed=0

    local test_files
    test_files=$(get_test_files)
    local file_count
    file_count=$(echo "$test_files" | wc -l | tr -d ' ')

    echo "Running $OLD_PIPELINE on $file_count test files..."
    echo ""

    for test_file in $test_files; do
        local name
        name=$(testname_from_file "$test_file")
        total=$((total + 1))

        local rel_path
        rel_path="${test_file#$ROOT_DIR/}"

        local stdout_file="$BASELINE_DIR/${name}.stdout"
        local stderr_file="$BASELINE_DIR/${name}.stderr"
        local meta_file="$BASELINE_DIR/${name}.meta"

        run_pipeline "$OLD_PIPELINE" "$rel_path" "$stdout_file" "$stderr_file"
        local exit_code=$?

        local category
        category=$(classify_result "$exit_code" "$stdout_file")

        # Write metadata
        echo "exit_code=$exit_code" > "$meta_file"
        echo "category=$category" >> "$meta_file"
        echo "command=$OLD_PIPELINE" >> "$meta_file"
        echo "file=$rel_path" >> "$meta_file"
        echo "timestamp=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$meta_file"

        # Display progress
        case "$category" in
            pass)
                echo -e "  ${GREEN}[PASS]${RESET} $name"
                succeeded=$((succeeded + 1))
                ;;
            fail)
                echo -e "  ${YELLOW}[FAIL]${RESET} $name (verification failures found)"
                succeeded=$((succeeded + 1))  # Still a valid run
                ;;
            inconclusive)
                echo -e "  ${YELLOW}[INCO]${RESET} $name"
                succeeded=$((succeeded + 1))
                ;;
            timeout)
                echo -e "  ${RED}[TIME]${RESET} $name"
                failed=$((failed + 1))
                ;;
            *)
                echo -e "  ${RED}[ERR ]${RESET} $name ($category)"
                failed=$((failed + 1))
                ;;
        esac
    done

    echo ""
    echo -e "${BOLD}Baseline captured:${RESET} $total tests"
    echo "  Ran successfully: $succeeded"
    echo "  Errored/Timeout:  $failed"
    echo "  Stored in: $BASELINE_DIR/"
    echo ""
}

# ---------------------------------------------------------------------------
# Phase 2: Differential Comparison
# ---------------------------------------------------------------------------

cmd_compare() {
    local pipeline="${1:-$NEW_PIPELINE}"

    echo -e "${BOLD}=== Differential Comparison ===${RESET}"
    echo "  Baseline: $OLD_PIPELINE (stored in baseline/)"
    echo "  Current:  $pipeline"
    echo ""

    # Verify prerequisites
    [ -x "$STRATA_BIN" ] || die "Strata binary not found at: $STRATA_BIN"
    [ -d "$BASELINE_DIR" ] || die "No baseline found. Run '$0 baseline' first."

    # Create results directory
    mkdir -p "$RESULTS_DIR"

    local total=0
    local same=0
    local improved=0
    local regression=0
    local different=0

    # Track lists for summary
    local regression_list=""
    local improved_list=""
    local different_list=""

    local test_files
    test_files=$(get_test_files)

    for test_file in $test_files; do
        local name
        name=$(testname_from_file "$test_file")
        total=$((total + 1))

        local rel_path
        rel_path="${test_file#$ROOT_DIR/}"

        # Check baseline exists
        local baseline_meta="$BASELINE_DIR/${name}.meta"
        if [ ! -f "$baseline_meta" ]; then
            echo -e "  ${YELLOW}[SKIP]${RESET} $name (no baseline)"
            continue
        fi

        # Read baseline category
        local baseline_category
        baseline_category=$(grep '^category=' "$baseline_meta" | cut -d= -f2)

        # Run new pipeline
        local new_stdout="$RESULTS_DIR/${name}.stdout"
        local new_stderr="$RESULTS_DIR/${name}.stderr"

        run_pipeline "$pipeline" "$rel_path" "$new_stdout" "$new_stderr"
        local new_exit_code=$?

        local new_category
        new_category=$(classify_result "$new_exit_code" "$new_stdout")

        # Write result metadata
        local result_meta="$RESULTS_DIR/${name}.meta"
        echo "exit_code=$new_exit_code" > "$result_meta"
        echo "category=$new_category" >> "$result_meta"
        echo "baseline_category=$baseline_category" >> "$result_meta"
        echo "command=$pipeline" >> "$result_meta"
        echo "file=$rel_path" >> "$result_meta"
        echo "timestamp=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$result_meta"

        # Classify the comparison
        local baseline_ok=false
        local new_ok=false

        # "ok" means the pipeline produced a meaningful result (pass, fail, or inconclusive)
        case "$baseline_category" in
            pass|fail|inconclusive) baseline_ok=true ;;
        esac
        case "$new_category" in
            pass|fail|inconclusive) new_ok=true ;;
        esac

        if [ "$baseline_ok" = true ] && [ "$new_ok" = true ]; then
            # Both ran successfully - compare outputs
            local baseline_stdout="$BASELINE_DIR/${name}.stdout"
            if diff -q "$baseline_stdout" "$new_stdout" >/dev/null 2>&1; then
                echo -e "  ${GREEN}[SAME]${RESET} $name"
                echo "verdict=same" >> "$result_meta"
                same=$((same + 1))
            else
                # Outputs differ - check if it's an improvement
                if [ "$baseline_category" = "fail" ] && [ "$new_category" = "pass" ]; then
                    echo -e "  ${GREEN}[IMPR]${RESET} $name (fail -> pass)"
                    echo "verdict=improved" >> "$result_meta"
                    improved=$((improved + 1))
                    improved_list="$improved_list  $name ($baseline_category -> $new_category)\n"
                elif [ "$baseline_category" = "pass" ] && [ "$new_category" = "fail" ]; then
                    echo -e "  ${RED}[REGR]${RESET} $name (pass -> fail)"
                    echo "verdict=regression" >> "$result_meta"
                    regression=$((regression + 1))
                    regression_list="$regression_list  $name ($baseline_category -> $new_category)\n"
                else
                    echo -e "  ${BLUE}[DIFF]${RESET} $name (same category: $new_category, different output)"
                    echo "verdict=different" >> "$result_meta"
                    different=$((different + 1))
                    different_list="$different_list  $name ($baseline_category -> $new_category)\n"
                fi
                # Store the diff
                diff -u "$baseline_stdout" "$new_stdout" > "$RESULTS_DIR/${name}.diff" 2>/dev/null
            fi
        elif [ "$baseline_ok" = false ] && [ "$new_ok" = true ]; then
            # New pipeline succeeds where old one errored
            echo -e "  ${GREEN}[IMPR]${RESET} $name ($baseline_category -> $new_category)"
            echo "verdict=improved" >> "$result_meta"
            improved=$((improved + 1))
            improved_list="$improved_list  $name ($baseline_category -> $new_category)\n"
        elif [ "$baseline_ok" = true ] && [ "$new_ok" = false ]; then
            # New pipeline errors where old one succeeded
            echo -e "  ${RED}[REGR]${RESET} $name ($baseline_category -> $new_category)"
            echo "verdict=regression" >> "$result_meta"
            regression=$((regression + 1))
            regression_list="$regression_list  $name ($baseline_category -> $new_category)\n"
        else
            # Both errored - compare error categories
            if [ "$baseline_category" = "$new_category" ]; then
                echo -e "  ${YELLOW}[SAME]${RESET} $name (both: $new_category)"
                echo "verdict=same" >> "$result_meta"
                same=$((same + 1))
            else
                echo -e "  ${BLUE}[DIFF]${RESET} $name ($baseline_category -> $new_category)"
                echo "verdict=different" >> "$result_meta"
                different=$((different + 1))
                different_list="$different_list  $name ($baseline_category -> $new_category)\n"
            fi
        fi
    done

    echo ""
    echo -e "${BOLD}=== Summary ===${RESET}"
    echo "  Total:       $total"
    echo -e "  Same:        ${GREEN}$same${RESET}"
    echo -e "  Improved:    ${GREEN}$improved${RESET}"
    echo -e "  Different:   ${BLUE}$different${RESET}"
    echo -e "  Regression:  ${RED}$regression${RESET}"
    echo ""

    if [ -n "$improved_list" ]; then
        echo -e "${GREEN}Improvements:${RESET}"
        echo -e "$improved_list"
    fi

    if [ -n "$different_list" ]; then
        echo -e "${BLUE}Differences (non-blocking):${RESET}"
        echo -e "$different_list"
    fi

    if [ -n "$regression_list" ]; then
        echo -e "${RED}REGRESSIONS (blocking):${RESET}"
        echo -e "$regression_list"
    fi

    # Write summary file
    cat > "$RESULTS_DIR/summary.txt" <<EOF
Differential Test Summary
=========================
Date: $(date -u +%Y-%m-%dT%H:%M:%SZ)
Baseline: $OLD_PIPELINE
Current:  $pipeline

Total:      $total
Same:       $same
Improved:   $improved
Different:  $different
Regression: $regression
EOF

    if [ "$regression" -gt 0 ]; then
        echo -e "${RED}BLOCKED: $regression regression(s) found.${RESET}"
        exit 1
    else
        echo -e "${GREEN}No regressions. Safe to proceed.${RESET}"
        exit 0
    fi
}

# ---------------------------------------------------------------------------
# Single Test Mode
# ---------------------------------------------------------------------------

cmd_single() {
    local testname="$1"
    [ -n "$testname" ] || die "Usage: $0 single <testname>"

    # Normalize: strip .python.st.ion suffix if provided
    testname="${testname%.python.st.ion}"

    local test_file="$TEST_DIR/${testname}.python.st.ion"
    [ -f "$test_file" ] || die "Test file not found: $test_file"

    local rel_path
    rel_path="${test_file#$ROOT_DIR/}"

    echo -e "${BOLD}=== Single Test: $testname ===${RESET}"
    echo "  File: $rel_path"
    echo ""

    # Verify strata binary
    [ -x "$STRATA_BIN" ] || die "Strata binary not found at: $STRATA_BIN"

    # Run old pipeline
    echo -e "${BOLD}--- Old Pipeline ($OLD_PIPELINE) ---${RESET}"
    local old_stdout
    old_stdout=$(mktemp)
    local old_stderr
    old_stderr=$(mktemp)

    run_pipeline "$OLD_PIPELINE" "$rel_path" "$old_stdout" "$old_stderr"
    local old_exit=$?
    local old_category
    old_category=$(classify_result "$old_exit" "$old_stdout")

    echo "  Exit code: $old_exit"
    echo "  Category:  $old_category"
    echo "  Output:"
    sed 's/^/    /' "$old_stdout"
    if [ -s "$old_stderr" ]; then
        echo "  Stderr:"
        sed 's/^/    /' "$old_stderr" | head -20
    fi
    echo ""

    # Run new pipeline
    echo -e "${BOLD}--- New Pipeline ($NEW_PIPELINE) ---${RESET}"
    local new_stdout
    new_stdout=$(mktemp)
    local new_stderr
    new_stderr=$(mktemp)

    run_pipeline "$NEW_PIPELINE" "$rel_path" "$new_stdout" "$new_stderr"
    local new_exit=$?
    local new_category
    new_category=$(classify_result "$new_exit" "$new_stdout")

    echo "  Exit code: $new_exit"
    echo "  Category:  $new_category"
    echo "  Output:"
    sed 's/^/    /' "$new_stdout"
    if [ -s "$new_stderr" ]; then
        echo "  Stderr:"
        sed 's/^/    /' "$new_stderr" | head -20
    fi
    echo ""

    # Compare
    echo -e "${BOLD}--- Comparison ---${RESET}"
    if diff -q "$old_stdout" "$new_stdout" >/dev/null 2>&1; then
        echo -e "  ${GREEN}IDENTICAL output${RESET}"
    else
        echo -e "  ${YELLOW}DIFFERENT output${RESET}"
        echo ""
        echo "  Diff (old vs new):"
        diff -u --label="old ($OLD_PIPELINE)" --label="new ($NEW_PIPELINE)" \
            "$old_stdout" "$new_stdout" | sed 's/^/    /'
    fi

    # Cleanup
    rm -f "$old_stdout" "$old_stderr" "$new_stdout" "$new_stderr"
}

# ---------------------------------------------------------------------------
# Summary (from stored results)
# ---------------------------------------------------------------------------

cmd_summary() {
    echo -e "${BOLD}=== Stored Results Summary ===${RESET}"
    echo ""

    if [ ! -d "$RESULTS_DIR" ]; then
        die "No results found. Run '$0 compare' first."
    fi

    if [ -f "$RESULTS_DIR/summary.txt" ]; then
        cat "$RESULTS_DIR/summary.txt"
        echo ""
    fi

    # Detailed breakdown by verdict
    local same=0 improved=0 regression=0 different=0

    for meta_file in "$RESULTS_DIR"/*.meta; do
        [ -f "$meta_file" ] || continue
        local verdict
        verdict=$(grep '^verdict=' "$meta_file" | cut -d= -f2)
        case "$verdict" in
            same) same=$((same + 1)) ;;
            improved) improved=$((improved + 1)) ;;
            regression) regression=$((regression + 1)) ;;
            different) different=$((different + 1)) ;;
        esac
    done

    echo "Breakdown:"
    echo -e "  Same:       ${GREEN}$same${RESET}"
    echo -e "  Improved:   ${GREEN}$improved${RESET}"
    echo -e "  Different:  ${BLUE}$different${RESET}"
    echo -e "  Regression: ${RED}$regression${RESET}"
    echo ""

    # List regressions
    if [ "$regression" -gt 0 ]; then
        echo -e "${RED}Regressions:${RESET}"
        for meta_file in "$RESULTS_DIR"/*.meta; do
            [ -f "$meta_file" ] || continue
            local verdict
            verdict=$(grep '^verdict=' "$meta_file" | cut -d= -f2)
            if [ "$verdict" = "regression" ]; then
                local name
                name=$(basename "$meta_file" .meta)
                local baseline_cat
                baseline_cat=$(grep '^baseline_category=' "$meta_file" | cut -d= -f2)
                local new_cat
                new_cat=$(grep '^category=' "$meta_file" | cut -d= -f2)
                echo "  $name ($baseline_cat -> $new_cat)"
            fi
        done
        echo ""
    fi

    # List improvements
    if [ "$improved" -gt 0 ]; then
        echo -e "${GREEN}Improvements:${RESET}"
        for meta_file in "$RESULTS_DIR"/*.meta; do
            [ -f "$meta_file" ] || continue
            local verdict
            verdict=$(grep '^verdict=' "$meta_file" | cut -d= -f2)
            if [ "$verdict" = "improved" ]; then
                local name
                name=$(basename "$meta_file" .meta)
                local baseline_cat
                baseline_cat=$(grep '^baseline_category=' "$meta_file" | cut -d= -f2)
                local new_cat
                new_cat=$(grep '^category=' "$meta_file" | cut -d= -f2)
                echo "  $name ($baseline_cat -> $new_cat)"
            fi
        done
        echo ""
    fi

    if [ "$regression" -gt 0 ]; then
        exit 1
    else
        exit 0
    fi
}

# ---------------------------------------------------------------------------
# List Tests
# ---------------------------------------------------------------------------

cmd_list() {
    echo -e "${BOLD}=== Available Test Files ===${RESET}"
    echo ""
    local count=0
    for test_file in $(get_test_files); do
        local name
        name=$(testname_from_file "$test_file")
        echo "  $name"
        count=$((count + 1))
    done
    echo ""
    echo "Total: $count test files"
}

# ---------------------------------------------------------------------------
# Main Dispatch
# ---------------------------------------------------------------------------

case "${1:-}" in
    baseline)
        cmd_baseline
        ;;
    compare)
        shift
        cmd_compare "$@"
        ;;
    single)
        shift
        cmd_single "$@"
        ;;
    summary)
        cmd_summary
        ;;
    list)
        cmd_list
        ;;
    --help|-h|help)
        usage
        ;;
    *)
        usage
        ;;
esac
