# QA Report: Selune Lua 5.4 JIT Compiler — PRD, Issue Board, and Progress

**Date:** 2026-02-21
**Branch:** `QA-PRD`
**Reviewer:** Claude (automated QA)

---

## Executive Summary

Selune is a well-designed, well-scoped project targeting a genuine gap in the ecosystem — there is no production-quality Lua 5.4 JIT compiler. The PRD is comprehensive, the architecture choices are sound, and Phase 1 + Phase 2a progress is solid.

### Current State

| Metric | Value |
|--------|-------|
| Total tests | 461 (140 compiler unit + 48 core + 273 VM E2E) |
| Pass rate | **100%** (461/461, 0 failed, 0 ignored) |
| Bugs found during QA | 6 |
| Bugs fixed | **6/6** |
| Open issues (before QA) | 13 |
| Open issues (after QA) | 12 (7 phase trackers + 5 stale → closed 7, created 7 new) |

---

## 1. PRD Review

### 1.1 Strengths

- **Gap analysis is accurate**: No other project fills the Lua 5.4 + JIT + Rust niche
- **Architecture decisions well-justified**: NaN-boxing, single-pass compiler, method-based JIT, Cranelift backend
- **Comprehensive scope**: 20 sections covering bit layouts to risk analysis, 83-opcode table, ExprDesc design, GC write barriers
- **Realistic timeline**: 60 weeks with phased milestones, MVP at Phase 3

### 1.2 Issues Found

| # | Issue | Severity | Details |
|---|-------|----------|---------|
| P1 | Phase 2 scope doesn't match actual work | MEDIUM | PRD's Phase 2 includes GC, coroutines, stdlib, metamethods. Actual Phase 2 only implemented VM dispatch + basic opcodes. |
| P2 | Performance targets vs Cranelift code quality | LOW | Cranelift generates code ~14% slower than LLVM. Achieving 70% of LuaJIT via Cranelift is ambitious but feasible for compute-heavy workloads. |
| P3 | Missing LBBV consideration | LOW | YJIT/ZJIT use Lazy Basic Block Versioning. Eliminates ~57% of type checks without program analysis. |
| P4 | Swiss Table vs hashbrown | INFORMATIONAL | Rust's `hashbrown` crate IS a Swiss Table. Could save implementation effort. |
| P5 | Coroutine yield-from-JIT complexity | LOW | "Don't JIT functions that yield" is what most runtimes use permanently (Luau does exactly this). |
| P6 | Missing Luau and Deegen/LJR from competitive analysis | MEDIUM | Most relevant modern comparisons absent from gap analysis table. |
| P7 | Interpreter performance target may be conservative | LOW | LJR's auto-generated interpreter hits 2.8x PUC. 1.5x target may undersell. |
| P8 | Copy-and-Patch not considered as Tier 1 alternative | INFORMATIONAL | CPython 3.13+ uses this; <0.1ms compile time, modest speedups. |

### 1.3 PRD Verdict

**PASS with minor revisions needed.** Amendments posted to issue #1.

---

## 2. Issue Board Review

### 2.1 Actions Taken

| Action | Issues | Details |
|--------|--------|---------|
| **Closed bug issues** | #9, #10, #11, #12, #13, #14 | All 6 bugs verified fixed, tests passing |
| **Closed Phase 1** | #2 | Phase 1 complete: 140 unit + 94 E2E tests |
| **Updated Phase 2 scope** | #3 | Added Phase 2a/2b/2c breakdown comment |
| **Created phase labels** | All issues | `phase-1` through `phase-6` + `qa` labels |
| **Created tracking issues** | #17-#23 | 7 new issues for unimplemented Phase 2 work |
| **Updated PRD** | #1 | Added competitive analysis amendments |

### 2.2 New Tracking Issues Created

| Issue | Title | Priority | Phase |
|-------|-------|----------|-------|
| #17 | Implement generic for loops (pairs/ipairs/next) | HIGH | 2b |
| #18 | Implement metamethods (27 metamethod types) | HIGH | 2b |
| #19 | Implement error handling (pcall, xpcall, error) | HIGH | 2b |
| #20 | Implement garbage collection (incremental mark-sweep) | MEDIUM | 2c |
| #21 | Implement coroutines (create, resume, yield) | MEDIUM | 2c |
| #22 | Implement standard library (basic, string, table, math) | MEDIUM | 2c |
| #23 | Implement to-be-closed variables (`<close>` attribute) | LOW | 2b |

---

## 3. Bug Report (All Fixed)

### BUG-1: Comparison-as-value always returns `true` (Issue #9)

**Severity:** HIGH | **Status:** FIXED

**Root cause:** The compiler only emitted `LOADTRUE` for comparison expressions used as values (`return a == b`).

**Fix:** Added `LOADTRUE + JMP + LOADFALSE` pattern with correct polarity — fall-through = TRUE, JMP target = FALSE.

**Verification:** `qa_eq_integer_float_not_equal`, `qa_eq_returns_false` pass.

### BUG-2: Multi-assignment corrupts temporaries (Issue #10)

**Severity:** HIGH | **Status:** FIXED

**Root cause:** In `a, b = b, a+b`, `free_reg` wasn't advanced between RHS discharges, causing second RHS to overwrite first RHS result.

**Fix:** Explicitly advance `free_reg` after each RHS discharge.

**Verification:** `qa_program_gcd`, `qa_multi_assign_swap`, `qa_fibonacci_iterative` pass.

### BUG-3: `repeat...until true` infinite loop (Issue #11)

**Severity:** MEDIUM | **Status:** FIXED

**Root cause:** Constant-true condition wasn't short-circuiting the loop exit.

**Fix:** Added constant-condition detection; loop exits after first iteration.

**Verification:** `qa_repeat_until_true_once` passes, 0 tests ignored.

### BUG-4: Infinite tail recursion not detected (Issue #12)

**Severity:** MEDIUM | **Status:** FIXED

**Root cause:** `return f()` compiled to `TailCall`, reusing the frame without growing the stack.

**Fix:** Test updated to `return f() + 0` to prevent tail-call optimization. Tail-call itself is correct.

**Verification:** `test_stack_overflow` passes.

### BUG-5: Multi-return in table constructor (Issue #13)

**Severity:** LOW | **Status:** FIXED

**Root cause:** `discharge_to_any_reg` added `MOVE` after `Call`, hiding it from last-instruction check.

**Fix:** Track multi-return via ExprDesc type; scan backward for Call/VarArg to patch.

**Verification:** `qa_multi_return_in_table` passes.

### BUG-6: Linked list traversal crash (Issue #14)

**Severity:** LOW | **Status:** FIXED

**Root cause:** Register management issues with field access in compound arithmetic.

**Fix:** Corrected register allocation for nested field access.

**Verification:** `qa_program_linked_list` passes.

---

## 4. Progress Assessment

### 4.1 Completed (Phase 1 + Phase 2a)

| Component | Status | Test Coverage |
|-----------|--------|---------------|
| Lexer (all Lua 5.4 tokens) | Complete | 140 unit tests |
| Single-pass compiler | Complete | 94 E2E tests |
| NaN-boxing TValue | Complete | 48 core tests |
| String interning + SSO | Complete | Tested |
| Bytecode (83 opcodes defined) | Complete | Encoding/decoding works |
| VM dispatch loop (~45 opcodes) | Complete | 273 E2E tests |
| Arithmetic (int, float, mixed) | Complete | Comprehensive |
| Comparisons (all types, as-value) | Complete | Including boolean materialization |
| Tables (array + hash) | Complete | CRUD, nesting, length |
| Closures + upvalues | Complete | Capture, mutation, counter pattern |
| Numeric for loops | Complete | Positive, negative, float step |
| While/repeat/break/goto | Complete | Including edge cases |
| Function calls + returns | Complete | Multi-return, tail call |
| Varargs | Complete | In functions and table constructors |
| Native functions | Partial | print, type, tostring, tonumber |

### 4.2 Remaining Work

Based on the PRD's Phase 2 definition, ~65-70% of scope remains:

**Phase 2b (Semantics & Error Handling):**
- Generic `for` loops (TFORPREP, TFORCALL, TFORLOOP + pairs/ipairs/next)
- Metamethods (~27 types)
- Error handling (pcall, xpcall, error)
- To-be-closed variables (TBC, CLOSE)

**Phase 2c (Runtime Infrastructure):**
- Garbage collection (incremental mark-sweep)
- Coroutines (create, resume, yield, close)
- Standard library (basic, string, table, math — ~100+ functions)

### 4.3 Technical Priority Order

1. **Metamethods** (#18) — unlocks OOP, stdlib, test suite
2. **Error handling** (#19) — required for any real Lua program
3. **Generic for** (#17) — `pairs()`/`ipairs()` used in virtually every program
4. **GC** (#20) — long-running programs will OOM without collection
5. **Stdlib** (#22) — can be added incrementally
6. **Coroutines** (#21) — important but can be deferred
7. **To-be-closed** (#23) — compliance feature

---

## 5. Competitive Landscape Validation

| Runtime | Lua Version | JIT? | Language | vs PUC Lua |
|---------|------------|------|----------|------------|
| PUC Lua 5.4 | 5.4 | No | C | 1.0x |
| Luau | 5.1 derivative | Method JIT | C++ | 2.5-4x |
| LuaJIT 2.1 | 5.1 | Trace JIT | C/ASM | 10-50x |
| LJR (Deegen) | 5.1 | Method JIT | C++ | 2.8x (interp only) |
| Ravi | 5.4 dialect | MIR JIT | C | 2-5x |
| Piccolo | 5.4 (partial) | No | Rust | ~0.5-1x |
| **Selune** | **5.4** | **Planned** | **Rust** | **TBD** |

**Selune fills a unique, validated niche.** No standard-compliant Lua 5.4 JIT exists in any language.

### Goal Feasibility

| Goal | Target | Feasibility |
|------|--------|-------------|
| Full Lua 5.4 compliance | 100% test suite | Achievable |
| Interpreter >= 1.5x PUC | Geomean | Likely achievable |
| Baseline JIT >= 5x PUC | Geomean | Achievable |
| Optimizing JIT >= 10x PUC | Hot loops | Challenging but feasible |
| Memory safety | Zero unaudited unsafe | Achievable (YJIT precedent) |
| Sub-10ms JIT compile | p99 per function | Very likely (Cranelift: 1-5ms) |

### Method-Based JIT Validated

The PRD's decision for method-based (not trace-based) JIT is confirmed by:
- Luau chose method-based for Lua
- YJIT/ZJIT (Ruby) chose method-based
- PyPy developers noted trace-based unpredictability (2025)
- Cranelift designed for function-at-a-time compilation
- Lua 5.4's integer/float dual subtype hurts trace-based approaches

---

## 6. Verification Commands

```bash
# All tests pass
cargo test --workspace
# Expected: 461 tests, 0 failed, 0 ignored

# Issue board state
gh issue list --state open
# Expected: 12 open issues (7 phase trackers + 5 new tracking issues remain)

# Specific bug verification tests
cargo test -p selune-vm qa_eq_integer_float_not_equal
cargo test -p selune-vm qa_program_gcd
cargo test -p selune-vm qa_repeat_until_true_once
cargo test -p selune-vm test_stack_overflow
cargo test -p selune-vm qa_multi_return_in_table
cargo test -p selune-vm qa_program_linked_list
```

---

## 7. Summary of QA Actions

| # | Action | Status |
|---|--------|--------|
| 1 | Close bug issues #9-#14 | Done |
| 2 | Close Phase 1 issue #2 | Done |
| 3 | Update Phase 2 issue #3 scope | Done |
| 4 | Create and apply labels to all issues | Done |
| 5 | Add competitive analysis to PRD issue #1 | Done |
| 6 | Create 7 tracking issues for unimplemented work | Done |
| 7 | Write QA report | Done |
