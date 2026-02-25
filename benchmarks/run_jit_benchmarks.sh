#!/usr/bin/env bash
# Selune JIT Benchmark Harness
# Measures JIT vs interpreter performance by comparing:
#   - Selune with JIT enabled (default, threshold=1000)
#   - PUC Lua 5.4 (interpreter only, as baseline)
#
# Each benchmark calls its hot function 1001+ times to trigger JIT compilation,
# then times 100 calls to the JIT-compiled native code.
#
# Usage: ./benchmarks/run_jit_benchmarks.sh [--runs N]

set -euo pipefail
cd "$(dirname "$0")/.."

# Configuration
RUNS=3
SELUNE="./target/release/selune"
PUC_LUA="/opt/homebrew/bin/lua"
SCRIPTS_DIR="benchmarks/scripts"

# Parse args
while [[ $# -gt 0 ]]; do
    case $1 in
        --runs) RUNS="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

# JIT benchmark list
JIT_BENCHMARKS=(
    jit_sum_loop
    jit_heavy_arith
    jit_float_arith
)

# Color output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

echo -e "${BOLD}Selune JIT Benchmark Suite${NC}"
echo "=============================="
echo ""

# Check binaries
HAVE_SELUNE=0
HAVE_PUC=0

if [[ -x "$SELUNE" ]]; then
    HAVE_SELUNE=1
    echo -e "  Selune:  ${GREEN}$SELUNE${NC}"
else
    echo -e "  Selune:  ${RED}NOT FOUND${NC} (run: cargo build --release)"
    exit 1
fi

if [[ -x "$PUC_LUA" ]]; then
    HAVE_PUC=1
    PUC_VERSION=$("$PUC_LUA" -v 2>&1 | head -1)
    echo -e "  PUC Lua: ${GREEN}$PUC_LUA${NC} ($PUC_VERSION)"
else
    echo -e "  PUC Lua: ${YELLOW}NOT FOUND${NC} (will skip comparison)"
fi

echo ""
echo "Runs per benchmark: $RUNS (best of N)"
echo "JIT threshold: 1000 calls"
echo ""

# Extract time from benchmark output
extract_time() {
    local output="$1"
    echo "$output" | grep '^RESULT:' | awk '{print $3}'
}

# Run a single benchmark N times and return the best time
run_benchmark() {
    local binary="$1"
    local script="$2"
    local runs="$3"
    local best=""

    for ((r = 1; r <= runs; r++)); do
        local output
        output=$("$binary" "$script" 2>&1) || true
        local time
        time=$(extract_time "$output")
        if [[ -z "$time" ]]; then
            echo "FAIL"
            return
        fi
        if [[ -z "$best" ]] || awk "BEGIN{exit !($time < $best)}"; then
            best="$time"
        fi
    done
    echo "$best"
}

printf "${BOLD}  %-20s %-14s %-14s %s${NC}\n" "Benchmark" "Selune JIT" "PUC Lua" "Speedup vs PUC"
echo "--------------------------------------------------------------"

for bench in "${JIT_BENCHMARKS[@]}"; do
    script="$SCRIPTS_DIR/${bench}.lua"
    if [[ ! -f "$script" ]]; then
        echo -e "  ${RED}SKIP${NC} $bench (script not found)"
        continue
    fi

    printf "  %-20s" "$bench"

    # Selune (JIT enabled)
    sel_time=$(run_benchmark "$SELUNE" "$script" "$RUNS")
    if [[ "$sel_time" == "FAIL" ]]; then
        printf "${RED}FAIL${NC}          "
    else
        printf "${CYAN}%8ss${NC}     " "$sel_time"
    fi

    # PUC Lua
    if [[ $HAVE_PUC -eq 1 ]]; then
        puc_time=$(run_benchmark "$PUC_LUA" "$script" "$RUNS")
        if [[ "$puc_time" == "FAIL" ]]; then
            printf "${RED}FAIL${NC}          "
            printf "—"
        else
            printf "%8ss     " "$puc_time"
            # Compute speedup
            if [[ "$sel_time" != "FAIL" ]]; then
                speedup=$(awk "BEGIN{printf \"%.1f\", $puc_time / $sel_time}")
                if awk "BEGIN{exit !($sel_time < $puc_time)}"; then
                    printf "${GREEN}%sx faster${NC}" "$speedup"
                else
                    ratio=$(awk "BEGIN{printf \"%.1f\", $sel_time / $puc_time}")
                    printf "${RED}%sx slower${NC}" "$ratio"
                fi
            fi
        fi
    else
        printf "N/A"
    fi

    echo ""
done

echo ""
echo -e "${BOLD}Note:${NC} Each benchmark calls its function 1001 times to trigger JIT"
echo "compilation (threshold=1000), then times 100 calls to the native code."
echo ""
echo -e "To compare interpreter-only performance, use: ${CYAN}./benchmarks/run_benchmarks.sh${NC}"
