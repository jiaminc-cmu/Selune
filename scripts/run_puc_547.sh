#!/usr/bin/env bash
#
# Run the official PUC-Rio Lua 5.4.7 test suite against Selune.
#
# Usage:
#   ./scripts/run_puc_547.sh [path/to/selune]
#
# Exit code: 0 if all tests pass, 1 if any fail.

set -euo pipefail

SELUNE="${1:-./target/release/selune}"
TEST_DIR="tests/lua54-tests"

if [ ! -x "$SELUNE" ]; then
  echo "ERROR: Selune binary not found at '$SELUNE'"
  echo "  Run 'cargo build --release' first."
  exit 2
fi

# The 28 applicable test files, in alphabetical order.
# Excluded: api (C API), main (CLI/port), heavy (memory stress), gengc (generational GC)
TESTS=(
  attrib big bitwise bwcoercion calls closure code constructs
  coroutine cstack db errors events files gc goto
  literals locals math nextvar pm sort strings tpack
  tracegc utf8 vararg verybig
)

TOTAL=${#TESTS[@]}
PASS=0
FAIL=0
FAIL_LIST=()

echo "========================================"
echo " PUC-Rio Lua 5.4.7 Official Test Suite"
echo " Binary: $SELUNE"
echo " Tests:  $TOTAL files"
echo "========================================"
echo ""

for f in "${TESTS[@]}"; do
  printf "  %-14s ... " "$f"
  output=$("$SELUNE" "$TEST_DIR/run_test.lua" "$TEST_DIR/$f.lua" 2>&1) && rc=0 || rc=$?
  if [ $rc -eq 0 ]; then
    echo "PASS"
    PASS=$((PASS + 1))
  else
    echo "FAIL"
    FAIL=$((FAIL + 1))
    # Capture first error line for summary
    err_line=$(echo "$output" | grep -E '(FAIL|error|Error|assert|panic)' | head -1)
    FAIL_LIST+=("  $f: $err_line")
  fi
done

echo ""
echo "========================================"
echo " Results: $PASS/$TOTAL PASS, $FAIL FAIL"
echo "========================================"

if [ $FAIL -gt 0 ]; then
  echo ""
  echo "Failures:"
  for line in "${FAIL_LIST[@]}"; do
    echo "$line"
  done
  exit 1
fi

echo ""
echo "All $TOTAL tests passed."
exit 0
