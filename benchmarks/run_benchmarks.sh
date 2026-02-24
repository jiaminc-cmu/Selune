#!/usr/bin/env bash
# Selune Benchmark Harness
# Compares Selune, PUC Lua 5.4, and LuaJIT 2.1
# Usage: ./benchmarks/run_benchmarks.sh [--runs N]

set -euo pipefail
cd "$(dirname "$0")/.."

# Configuration
RUNS=3
SELUNE="./target/release/selune"
PUC_LUA="/opt/homebrew/bin/lua"
LUAJIT="/opt/homebrew/bin/luajit"
SCRIPTS_DIR="benchmarks/scripts"
RESULTS_DIR="benchmarks/results"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULT_FILE="$RESULTS_DIR/benchmark_${TIMESTAMP}.md"

# Parse args
while [[ $# -gt 0 ]]; do
    case $1 in
        --runs) RUNS="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

# Coroutines benchmark may hang on LuaJIT, skip it
LUAJIT_SKIP="coroutines"

# Color output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

echo -e "${BOLD}Selune Benchmark Suite${NC}"
echo "=============================="
echo ""

# Check binaries
HAVE_SELUNE=0
HAVE_PUC=0
HAVE_LUAJIT=0

if [[ -x "$SELUNE" ]]; then
    HAVE_SELUNE=1
    echo -e "  Selune:  ${GREEN}$SELUNE${NC}"
else
    echo -e "  Selune:  ${RED}NOT FOUND${NC} (run: cargo build --release)"
fi

if [[ -x "$PUC_LUA" ]]; then
    HAVE_PUC=1
    PUC_VERSION=$("$PUC_LUA" -v 2>&1 | head -1)
    echo -e "  PUC Lua: ${GREEN}$PUC_LUA${NC} ($PUC_VERSION)"
else
    echo -e "  PUC Lua: ${YELLOW}NOT FOUND${NC} (will skip)"
fi

if [[ -x "$LUAJIT" ]]; then
    HAVE_LUAJIT=1
    LJ_VERSION=$("$LUAJIT" -v 2>&1 | head -1)
    echo -e "  LuaJIT:  ${GREEN}$LUAJIT${NC} ($LJ_VERSION)"
else
    echo -e "  LuaJIT:  ${YELLOW}NOT FOUND${NC} (will skip)"
fi

if [[ $HAVE_SELUNE -eq 0 ]]; then
    echo -e "\n${RED}Error: Selune binary not found. Run 'cargo build --release' first.${NC}"
    exit 1
fi

echo ""
echo "Runs per benchmark: $RUNS"
echo "Results: $RESULT_FILE"
echo ""

mkdir -p "$RESULTS_DIR"

# Benchmark list (order matters for display)
BENCHMARKS=(
    arithmetic
    fibonacci
    ackermann
    table_array
    table_hash
    table_object
    string_concat
    string_match
    string_format
    closures
    method_calls
    coroutines
    gc_pressure
    binary_trees
    spectral_norm
    mandelbrot
)

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

# Declare associative arrays for results
declare -A RESULTS_SELUNE
declare -A RESULTS_PUC
declare -A RESULTS_LUAJIT

echo -e "${BOLD}Running benchmarks...${NC}"
echo ""

for bench in "${BENCHMARKS[@]}"; do
    script="$SCRIPTS_DIR/${bench}.lua"
    if [[ ! -f "$script" ]]; then
        echo -e "  ${RED}SKIP${NC} $bench (script not found)"
        continue
    fi

    printf "  %-20s" "$bench"

    # Selune
    t=$(run_benchmark "$SELUNE" "$script" "$RUNS")
    RESULTS_SELUNE[$bench]="$t"
    if [[ "$t" == "FAIL" ]]; then
        printf "${RED}FAIL${NC}     "
    else
        printf "${CYAN}%8ss${NC} " "$t"
    fi

    # PUC Lua
    if [[ $HAVE_PUC -eq 1 ]]; then
        t=$(run_benchmark "$PUC_LUA" "$script" "$RUNS")
        RESULTS_PUC[$bench]="$t"
        if [[ "$t" == "FAIL" ]]; then
            printf "${RED}FAIL${NC}     "
        else
            printf "%8ss " "$t"
        fi
    else
        RESULTS_PUC[$bench]="N/A"
        printf "  N/A     "
    fi

    # LuaJIT
    if [[ $HAVE_LUAJIT -eq 1 ]]; then
        if [[ "$LUAJIT_SKIP" == *"$bench"* ]]; then
            RESULTS_LUAJIT[$bench]="SKIP"
            printf "${YELLOW}  SKIP${NC}    "
        else
            t=$(run_benchmark "$LUAJIT" "$script" "$RUNS")
            RESULTS_LUAJIT[$bench]="$t"
            if [[ "$t" == "FAIL" ]]; then
                printf "${RED}FAIL${NC}     "
            else
                printf "%8ss " "$t"
            fi
        fi
    else
        RESULTS_LUAJIT[$bench]="N/A"
        printf "  N/A     "
    fi

    echo ""
done

echo ""

# Generate markdown report
{
    echo "# Selune Benchmark Results"
    echo ""
    echo "**Date:** $(date '+%Y-%m-%d %H:%M:%S')"
    echo "**Machine:** $(uname -m) $(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo "unknown")"
    echo "**OS:** $(sw_vers -productName 2>/dev/null || uname -s) $(sw_vers -productVersion 2>/dev/null || uname -r)"
    echo "**Runs per benchmark:** $RUNS (best of N)"
    echo ""
    echo "### Implementations"
    echo ""
    echo "- **Selune:** $SELUNE"
    [[ $HAVE_PUC -eq 1 ]] && echo "- **PUC Lua:** $PUC_VERSION"
    [[ $HAVE_LUAJIT -eq 1 ]] && echo "- **LuaJIT:** $LJ_VERSION"
    echo ""
    echo "---"
    echo ""
    echo "## Results"
    echo ""
    echo "| Benchmark | Selune (s) | PUC Lua (s) | LuaJIT (s) | Selune/PUC | Selune/LuaJIT |"
    echo "|-----------|-----------|-------------|------------|------------|---------------|"

    for bench in "${BENCHMARKS[@]}"; do
        sel="${RESULTS_SELUNE[$bench]:-N/A}"
        puc="${RESULTS_PUC[$bench]:-N/A}"
        lj="${RESULTS_LUAJIT[$bench]:-N/A}"

        # Compute ratios
        ratio_puc="—"
        ratio_lj="—"

        if [[ "$sel" != "FAIL" && "$sel" != "N/A" && "$puc" != "FAIL" && "$puc" != "N/A" ]]; then
            ratio_puc=$(awk "BEGIN{printf \"%.2fx\", $sel / $puc}")
        fi
        if [[ "$sel" != "FAIL" && "$sel" != "N/A" && "$lj" != "FAIL" && "$lj" != "N/A" && "$lj" != "SKIP" ]]; then
            ratio_lj=$(awk "BEGIN{printf \"%.2fx\", $sel / $lj}")
        fi

        # Format cells
        [[ "$sel" == "FAIL" ]] && sel="FAIL"
        [[ "$puc" == "FAIL" ]] && puc="FAIL"
        [[ "$lj" == "FAIL" ]] && lj="FAIL"

        echo "| $bench | $sel | $puc | $lj | $ratio_puc | $ratio_lj |"
    done

    echo ""
    echo "---"
    echo ""
    echo "**Legend:**"
    echo "- **Selune/PUC**: ratio of Selune time to PUC Lua time (lower is better for Selune; <1.0x means Selune is faster)"
    echo "- **Selune/LuaJIT**: ratio of Selune time to LuaJIT time (lower is better for Selune)"
    echo "- **SKIP**: benchmark not applicable for that implementation"
    echo "- **FAIL**: benchmark failed to run"
    echo ""

    # Compute geometric mean of ratios
    if [[ $HAVE_PUC -eq 1 ]]; then
        puc_ratios=()
        for bench in "${BENCHMARKS[@]}"; do
            sel="${RESULTS_SELUNE[$bench]:-N/A}"
            puc="${RESULTS_PUC[$bench]:-N/A}"
            if [[ "$sel" != "FAIL" && "$sel" != "N/A" && "$puc" != "FAIL" && "$puc" != "N/A" ]]; then
                r=$(awk "BEGIN{printf \"%.6f\", $sel / $puc}")
                puc_ratios+=("$r")
            fi
        done
        if [[ ${#puc_ratios[@]} -gt 0 ]]; then
            geo_puc=$(printf '%s\n' "${puc_ratios[@]}" | awk '{p += log($1)} END {printf "%.2f", exp(p/NR)}')
            echo "## Summary"
            echo ""
            echo "- **Geometric mean Selune/PUC Lua:** ${geo_puc}x (across ${#puc_ratios[@]} benchmarks)"
        fi
    fi

    if [[ $HAVE_LUAJIT -eq 1 ]]; then
        lj_ratios=()
        for bench in "${BENCHMARKS[@]}"; do
            sel="${RESULTS_SELUNE[$bench]:-N/A}"
            lj="${RESULTS_LUAJIT[$bench]:-N/A}"
            if [[ "$sel" != "FAIL" && "$sel" != "N/A" && "$lj" != "FAIL" && "$lj" != "N/A" && "$lj" != "SKIP" ]]; then
                r=$(awk "BEGIN{printf \"%.6f\", $sel / $lj}")
                lj_ratios+=("$r")
            fi
        done
        if [[ ${#lj_ratios[@]} -gt 0 ]]; then
            geo_lj=$(printf '%s\n' "${lj_ratios[@]}" | awk '{p += log($1)} END {printf "%.2f", exp(p/NR)}')
            echo "- **Geometric mean Selune/LuaJIT:** ${geo_lj}x (across ${#lj_ratios[@]} benchmarks)"
        fi
    fi

    echo ""
} > "$RESULT_FILE"

echo -e "${GREEN}Results written to: $RESULT_FILE${NC}"

# Copy to docs/PERFORMANCE.md
DOCS_FILE="docs/PERFORMANCE.md"
echo ""
echo -e "${BOLD}Generating $DOCS_FILE ...${NC}"

{
    echo "# Selune Performance Report"
    echo ""
    echo "> Auto-generated by \`benchmarks/run_benchmarks.sh\` on $(date '+%Y-%m-%d %H:%M:%S')"
    echo "> To regenerate: \`./benchmarks/run_benchmarks.sh\`"
    echo ""
    # Include the raw results
    cat "$RESULT_FILE"
    echo ""
    echo "---"
    echo ""
    echo "## Analysis"
    echo ""
    echo "### Category Breakdown"
    echo ""
    echo "| Category | Benchmarks | Notes |"
    echo "|----------|-----------|-------|"
    echo "| Arithmetic/Loops | arithmetic, fibonacci, ackermann | Core dispatch loop + integer/float ops |"
    echo "| Tables | table_array, table_hash, table_object | Array vs hash performance, metatable dispatch |"
    echo "| Strings | string_concat, string_match, string_format | String interning, pattern engine, formatting |"
    echo "| Functions | closures, method_calls | Closure creation, upvalue access, OOP dispatch |"
    echo "| Coroutines | coroutines | Yield/resume overhead (Selune vs PUC only) |"
    echo "| GC | gc_pressure, binary_trees | Allocation rate, GC pause time, tree traversal |"
    echo "| Math | spectral_norm, mandelbrot | Float-heavy tight loops |"
    echo ""
    echo "### Optimization Roadmap"
    echo ""
    echo "**Short-term (low-hanging fruit):**"
    echo "- NaN-boxing dispatch optimizations (reduce branching in hot paths)"
    echo "- Table array pre-allocation hints"
    echo "- String interning cache improvements"
    echo ""
    echo "**Medium-term:**"
    echo "- Inline caching for method calls and table lookups"
    echo "- Register allocation improvements in the compiler"
    echo "- Specialized fast paths for common patterns (e.g., \`for i=1,n\`)"
    echo ""
    echo "**Long-term:**"
    echo "- JIT compilation (selune-jit crate)"
    echo "- Generational GC (selune-core)"
    echo "- SIMD-accelerated string operations"
    echo ""
    echo "### How to Profile"
    echo ""
    echo "#### Using Instruments (macOS)"
    echo "\`\`\`bash"
    echo "# Time Profiler"
    echo "xcrun xctrace record --template 'Time Profiler' --launch ./target/release/selune benchmarks/scripts/fibonacci.lua"
    echo "\`\`\`"
    echo ""
    echo "#### Using cargo-flamegraph"
    echo "\`\`\`bash"
    echo "cargo install flamegraph"
    echo "cargo flamegraph --release -- benchmarks/scripts/fibonacci.lua"
    echo "\`\`\`"
    echo ""
    echo "#### Using perf (Linux)"
    echo "\`\`\`bash"
    echo "perf record -g ./target/release/selune benchmarks/scripts/fibonacci.lua"
    echo "perf report"
    echo "\`\`\`"
    echo ""
} > "$DOCS_FILE"

echo -e "${GREEN}Performance report written to: $DOCS_FILE${NC}"
echo ""
echo -e "${BOLD}Done!${NC}"
