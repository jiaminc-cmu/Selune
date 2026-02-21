# Selune: A Modern Lua 5.4 JIT Compiler in Rust — Master Blueprint

> **Status:** Draft v1.0
> **Authors:** Project Team
> **Created:** 2026-02-21
> **Last Updated:** 2026-02-21

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Problem Statement & Motivation](#2-problem-statement--motivation)
3. [Goals & Non-Goals](#3-goals--non-goals)
4. [Technical Architecture](#4-technical-architecture)
5. [Value Representation](#5-value-representation)
6. [Bytecode & Compiler](#6-bytecode--compiler)
7. [VM / Interpreter](#7-vm--interpreter)
8. [JIT Compilation Pipeline](#8-jit-compilation-pipeline)
9. [Garbage Collection Design](#9-garbage-collection-design)
10. [Table & String Implementation](#10-table--string-implementation)
11. [Coroutine Implementation](#11-coroutine-implementation)
12. [FFI Design](#12-ffi-design)
13. [Standard Library](#13-standard-library)
14. [Cross-Platform Support](#14-cross-platform-support)
15. [Development Phases](#15-development-phases)
16. [Testing & Compliance](#16-testing--compliance)
17. [Performance Targets](#17-performance-targets)
18. [Risk Analysis](#18-risk-analysis)
19. [Success Criteria](#19-success-criteria)
20. [References](#20-references)

---

## 1. Executive Summary

### 1.1 Project Positioning

**Selune** is a from-scratch, production-quality **Lua 5.4 JIT compiler** written entirely in **Rust**. It targets the unfilled niche of a modern, memory-safe, embeddable Lua runtime that delivers near-LuaJIT performance while supporting the full Lua 5.4 specification — including integers, generational GC, and to-be-closed variables.

### 1.2 Gap Analysis

| Feature | PUC Lua 5.4 | LuaJIT 2.1 | Piccolo | mlua | Hematita | **Selune** |
|---|---|---|---|---|---|---|
| **Language Version** | 5.4 | 5.1 + ext | 5.4 (partial) | Binding | 5.3 (partial) | **5.4 full** |
| **Implementation Language** | C | C + ASM | Rust | Rust (binding) | Rust | **Rust** |
| **JIT Compiler** | No | Yes (trace) | No | N/A | No | **Yes (method)** |
| **Memory Safety** | No | No | Yes | Partial | Yes | **Yes** |
| **Integer Support** | Yes (5.4) | No (5.1) | Partial | N/A | Partial | **Yes** |
| **Generational GC** | Yes | No | No | N/A | No | **Yes** |
| **Embeddable** | Yes | Yes | Yes | Yes | Yes | **Yes** |
| **FFI** | Via C API | Built-in | No | Via Rust | No | **Built-in** |
| **Production Ready** | Yes | Yes | No | Yes | No | **Target** |
| **Active Development** | Maintenance | Maintenance | Active | Active | Stalled | **Active** |

### 1.3 Mission Priorities

1. **Correctness first** — Full Lua 5.4 compliance, pass official test suite
2. **Safety** — Memory-safe by default, no `unsafe` in hot paths without auditing
3. **Performance** — Competitive with LuaJIT on common workloads
4. **Embeddability** — Clean Rust API for embedding in Rust applications
5. **Maintainability** — Well-documented, modular codebase

---

## 2. Problem Statement & Motivation

### 2.1 The Lua 5.4 JIT Gap

Lua 5.4 introduced significant semantic changes over 5.1:

- **Native integer type** (`integer` subtype distinct from `float`)
- **Bitwise operators** (`&`, `|`, `~`, `<<`, `>>`)
- **Generational garbage collection** (in addition to incremental)
- **To-be-closed variables** (`<close>` attribute)
- **New integer division operator** (`//`)
- **Warning system** (`warn()`)
- **Unsigned integer hints** in standard library

LuaJIT implements Lua 5.1 with selected extensions and has been in maintenance mode since 2017. There is **no production JIT compiler** for Lua 5.4. This is the gap Selune fills.

### 2.2 The Rust Ecosystem Gap

The Rust ecosystem has:

- **mlua** — Excellent FFI bindings to PUC Lua/LuaJIT, but not a standalone runtime
- **Piccolo** — Promising Lua 5.4 interpreter in Rust, but no JIT and incomplete stdlib
- **Hematita** — Stalled Lua 5.3 interpreter, incomplete

There is no Rust-native Lua runtime suitable for production use with JIT compilation.

### 2.3 Why Rust?

| Concern | C (PUC/LuaJIT) | Rust (Selune) |
|---|---|---|
| Memory safety | Manual, CVE-prone | Compile-time guarantees |
| Concurrency | Global locks / careful design | Ownership model, fearless concurrency |
| Error handling | `longjmp` / error codes | `Result<T, E>`, no UB on error paths |
| Dependency management | Manual / Makefiles | Cargo ecosystem |
| Cross-compilation | Toolchain-specific | `rustup target add` |
| Embedding safety | Careful API discipline | Type-safe API by construction |
| Refactoring | Manual, error-prone | Compiler-assisted |

### 2.4 Why Cranelift?

| Criteria | LLVM | Cranelift | Hand-written ASM |
|---|---|---|---|
| **Compilation speed** | Slow (100ms+) | Fast (1-5ms) | Instant (template) |
| **Code quality** | Excellent | Good (80-90% of LLVM) | Variable |
| **Portability** | Excellent | Good (x86_64, aarch64, s390x, riscv64) | Per-architecture |
| **Maintenance burden** | External dep, huge | Rust-native, manageable | Enormous |
| **Rust integration** | Via C++ FFI | Native Rust | Via `unsafe` |
| **Memory safety** | No | Mostly safe API | No |
| **Suitable for JIT** | Possible but heavy | Designed for JIT | Designed for JIT |
| **Debug info** | Excellent | Good | Manual |

**Decision:** Cranelift is the optimal choice for a Rust-based JIT — fast compilation, native Rust API, designed for JIT use cases, and actively maintained by the Wasmtime team.

---

## 3. Goals & Non-Goals

### 3.1 Goals

| ID | Goal | Priority | Measurable Target |
|---|---|---|---|
| **G1** | Full Lua 5.4.7 compliance | P0 | Pass official test suite (100%) |
| **G2** | Interpreter performance ≥ 1.5x PUC Lua | P0 | Geometric mean across benchmarks |
| **G3** | JIT performance ≥ 5x PUC Lua (baseline) | P1 | Geometric mean across benchmarks |
| **G4** | JIT performance ≥ 10x PUC Lua (optimizing) | P1 | Geometric mean, hot loops |
| **G5** | Memory-safe implementation | P0 | Zero `unsafe` outside audited modules |
| **G6** | Embeddable in Rust applications | P0 | Clean public API with `selune` crate |
| **G7** | Cross-platform support (x86_64, aarch64) | P0 | CI passes on Linux, macOS, Windows |
| **G8** | C API compatibility layer | P2 | Drop-in for common embedding patterns |
| **G9** | Built-in FFI for calling C from Lua | P1 | Equivalent to LuaJIT FFI subset |
| **G10** | Sub-10ms JIT compilation latency | P1 | p99 per-function compilation time |

### 3.2 Non-Goals

| ID | Non-Goal | Rationale |
|---|---|---|
| **NG1** | Lua 5.1 / 5.2 / 5.3 compatibility modes | Scope explosion; use LuaJIT or PUC for older versions |
| **NG2** | LuaJIT extension compatibility (`ffi.*`, `jit.*`) | Different FFI design; compatibility shim is future work |
| **NG3** | Web/WASM target (initial release) | JIT requires native code gen; interpreter-only WASM is future |
| **NG4** | Built-in debugger UI | Provide debug hooks; UI is external tooling |
| **NG5** | Multi-threaded Lua execution | Lua semantics are single-threaded; provide multi-VM instead |
| **NG6** | AOT compilation to native binaries | JIT focus; AOT is a potential future extension |
| **NG7** | Custom language extensions beyond Lua 5.4 | Maintain spec compliance; extensions via embedding API |
| **NG8** | GPU/SIMD auto-vectorization | Out of scope for initial JIT; future optimization pass |

---

## 4. Technical Architecture

### 4.1 High-Level Data Flow

```
                    ┌──────────────────────────────────────────┐
                    │              Selune Runtime               │
                    │                                          │
  Lua Source ──────►│  ┌─────────┐   ┌──────────┐             │
                    │  │  Lexer  │──►│  Parser/ │             │
                    │  │         │   │ Compiler │             │
                    │  └─────────┘   └────┬─────┘             │
                    │                     │                    │
                    │                     ▼                    │
                    │              ┌──────────────┐            │
                    │              │   Bytecode   │            │
                    │              │    (Proto)   │            │
                    │              └──────┬───────┘            │
                    │                     │                    │
                    │         ┌───────────┼───────────┐       │
                    │         ▼           ▼           ▼       │
                    │  ┌────────────┐ ┌────────┐ ┌────────┐  │
                    │  │Interpreter │ │Baseline│ │  Opt   │  │
                    │  │  (Tier 0)  │ │  JIT   │ │  JIT   │  │
                    │  │            │ │(Tier 1)│ │(Tier 2)│  │
                    │  └─────┬──────┘ └───┬────┘ └───┬────┘  │
                    │        │            │          │        │
                    │        ▼            ▼          ▼        │
                    │  ┌─────────────────────────────────┐    │
                    │  │         Execution Engine         │    │
                    │  │  (Registers, Stack, Call Frames) │    │
                    │  └──────────────┬──────────────────┘    │
                    │                 │                        │
                    │        ┌────────┴────────┐              │
                    │        ▼                 ▼              │
                    │  ┌──────────┐     ┌───────────┐        │
                    │  │    GC    │     │  Stdlib   │        │
                    │  │(Inc+Gen) │     │ + FFI     │        │
                    │  └──────────┘     └───────────┘        │
                    └──────────────────────────────────────────┘
```

### 4.2 Cargo Workspace Organization

```
selune/
├── Cargo.toml                  # Workspace root
├── crates/
│   ├── selune-core/           # Value types, GC, tables, strings
│   │   ├── src/
│   │   │   ├── value.rs       # TValue, NaN-boxing
│   │   │   ├── gc.rs          # Garbage collector
│   │   │   ├── table.rs       # Table implementation
│   │   │   ├── string.rs      # String interning, SSO
│   │   │   ├── object.rs      # GC object headers
│   │   │   └── lib.rs
│   │   └── Cargo.toml
│   │
│   ├── selune-compiler/       # Lexer, parser, bytecode compiler
│   │   ├── src/
│   │   │   ├── lexer.rs       # Tokenizer
│   │   │   ├── parser.rs      # Single-pass parser/compiler
│   │   │   ├── codegen.rs     # Bytecode emission
│   │   │   ├── opcode.rs      # Instruction definitions
│   │   │   ├── proto.rs       # Function prototype
│   │   │   └── lib.rs
│   │   └── Cargo.toml
│   │
│   ├── selune-vm/             # Interpreter, dispatch loop
│   │   ├── src/
│   │   │   ├── dispatch.rs    # Main dispatch loop
│   │   │   ├── execute.rs     # Instruction handlers
│   │   │   ├── stack.rs       # VM stack management
│   │   │   ├── callinfo.rs    # Call frame management
│   │   │   ├── metamethod.rs  # Metamethod dispatch
│   │   │   └── lib.rs
│   │   └── Cargo.toml
│   │
│   ├── selune-jit/            # JIT compiler (Cranelift-based)
│   │   ├── src/
│   │   │   ├── baseline.rs    # Tier 1: baseline compiler
│   │   │   ├── optimize.rs    # Tier 2: optimizing compiler
│   │   │   ├── ir.rs          # JIT IR / Cranelift bridge
│   │   │   ├── profile.rs     # Profiling & tier-up decisions
│   │   │   ├── deopt.rs       # Deoptimization / OSR
│   │   │   ├── codebuffer.rs  # Executable memory management
│   │   │   └── lib.rs
│   │   └── Cargo.toml
│   │
│   ├── selune-stdlib/         # Standard library implementations
│   │   ├── src/
│   │   │   ├── base.rs        # Basic functions
│   │   │   ├── string.rs      # string library
│   │   │   ├── table.rs       # table library
│   │   │   ├── math.rs        # math library
│   │   │   ├── io.rs          # io library
│   │   │   ├── os.rs          # os library
│   │   │   ├── coroutine.rs   # coroutine library
│   │   │   ├── utf8.rs        # utf8 library
│   │   │   ├── debug.rs       # debug library
│   │   │   ├── package.rs     # package/require system
│   │   │   └── lib.rs
│   │   └── Cargo.toml
│   │
│   ├── selune-ffi/            # Foreign function interface
│   │   ├── src/
│   │   │   ├── cdef.rs        # C declaration parser
│   │   │   ├── call.rs        # Foreign call dispatch
│   │   │   ├── types.rs       # C type mapping
│   │   │   └── lib.rs
│   │   └── Cargo.toml
│   │
│   └── selune/                # Main crate (public API + CLI)
│       ├── src/
│       │   ├── state.rs       # Lua state (public API)
│       │   ├── api.rs         # Embedding API
│       │   ├── main.rs        # CLI entry point
│       │   └── lib.rs
│       └── Cargo.toml
│
├── tests/                     # Integration tests
│   ├── lua54-test-suite/      # Official Lua 5.4 tests
│   ├── benchmarks/            # Performance benchmarks
│   └── fuzz/                  # Fuzz testing harnesses
│
└── docs/                      # Documentation
    ├── architecture.md
    ├── embedding.md
    └── internals.md
```

### 4.3 Dependency Graph

```
selune (CLI + API)
├── selune-vm
│   ├── selune-core
│   ├── selune-compiler
│   └── selune-jit
│       └── cranelift-*
├── selune-stdlib
│   ├── selune-core
│   └── selune-vm
└── selune-ffi
    ├── selune-core
    └── libffi-sys (interpreter mode)
```

---

## 5. Value Representation

### 5.1 NaN-Boxing Scheme

All Lua values are represented as a single 64-bit `TValue` using NaN-boxing. This provides:

- **Compact representation** — 8 bytes per value (same as a `double`)
- **Fast type checks** — Bit masking instead of branching
- **Unboxed floats** — No allocation for number values
- **Small integer fast path** — 47-bit integers without allocation

### 5.2 Bit Layout

```
Float (any non-NaN double):
  [seeeeeee eeeemmmm mmmmmmmm mmmmmmmm mmmmmmmm mmmmmmmm mmmmmmmm mmmmmmmm]
  Standard IEEE 754 double, stored as-is

Quiet NaN space (tag bits in upper 16 bits + 1):
  [11111111 11111xxx yyyyyyyy yyyyyyyy yyyyyyyy yyyyyyyy yyyyyyyy yyyyyyyy]
                 ^^^--- tag bits (3 bits = 8 tags)
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^--- payload (47 bits)

Tag assignments:
  Tag 000 = (reserved, actual NaN / canonical NaN)
  Tag 001 = Nil
  Tag 010 = Boolean (payload bit 0: 0=false, 1=true)
  Tag 011 = Small Integer (payload: 47-bit signed integer, range ±70 trillion)
  Tag 100 = GC Pointer (payload: 47-bit pointer to GC object)
  Tag 101 = Light Userdata (payload: 47-bit pointer)
  Tag 110 = (reserved for future use)
  Tag 111 = (reserved for future use)
```

### 5.3 Small Integer Fast Path

The 47-bit signed integer range is `[-70_368_744_177_664, +70_368_744_177_663]` (approximately ±70 trillion). This covers the vast majority of integer usage in Lua programs. For the rare case where a full 64-bit integer is needed, we fall back to a boxed (GC-allocated) integer.

```
Integer representation strategy:
  1. If value fits in 47 bits → store as Small Integer tag (no allocation)
  2. If value exceeds 47 bits → allocate BoxedInt on GC heap, store as GC Pointer
  3. Arithmetic operations check for overflow and promote as needed
```

### 5.4 TValue Rust Sketch

```rust
/// A Lua value, NaN-boxed into 64 bits.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct TValue(u64);

// Tag constants (upper bits after NaN prefix)
const NAN_PREFIX: u64  = 0x7FF8_0000_0000_0000; // Quiet NaN
const TAG_SHIFT: u32   = 47;
const TAG_NIL: u64     = 0x1;  // 001
const TAG_BOOL: u64    = 0x2;  // 010
const TAG_INT: u64     = 0x3;  // 011
const TAG_GC: u64      = 0x4;  // 100
const TAG_LIGHT: u64   = 0x5;  // 101
const PAYLOAD_MASK: u64 = (1u64 << 47) - 1;

impl TValue {
    /// Create a nil value.
    pub const NIL: Self = Self(NAN_PREFIX | (TAG_NIL << TAG_SHIFT));

    /// Create a boolean value.
    pub const fn from_bool(b: bool) -> Self {
        Self(NAN_PREFIX | (TAG_BOOL << TAG_SHIFT) | (b as u64))
    }

    /// Create a float value (any non-NaN double).
    pub fn from_float(f: f64) -> Self {
        if f.is_nan() {
            // Canonical NaN
            Self(NAN_PREFIX)
        } else {
            Self(f.to_bits())
        }
    }

    /// Create an integer value (small or boxed).
    pub fn from_integer(i: i64, gc: &mut Gc) -> Self {
        let small = i as i128;
        if small >= -(1i128 << 46) && small < (1i128 << 46) {
            // Fits in 47 bits (signed)
            let payload = (i as u64) & PAYLOAD_MASK;
            Self(NAN_PREFIX | (TAG_INT << TAG_SHIFT) | payload)
        } else {
            // Boxed integer — allocate on GC heap
            let ptr = gc.alloc_boxed_int(i);
            Self::from_gc_ptr(ptr)
        }
    }

    /// Check if this is a float.
    pub fn is_float(self) -> bool {
        // A float is any value that is NOT in the NaN tag space
        (self.0 & NAN_PREFIX) != NAN_PREFIX || self.0 == NAN_PREFIX
    }

    /// Extract tag bits.
    fn tag(self) -> u64 {
        (self.0 >> TAG_SHIFT) & 0x7
    }

    /// Check if this is a small integer.
    pub fn is_small_int(self) -> bool {
        (self.0 & NAN_PREFIX) == NAN_PREFIX && self.tag() == TAG_INT
    }

    /// Extract small integer (sign-extended from 47 bits).
    pub fn as_small_int(self) -> Option<i64> {
        if self.is_small_int() {
            let raw = (self.0 & PAYLOAD_MASK) as i64;
            // Sign extend from bit 46
            let extended = (raw << 17) >> 17;
            Some(extended)
        } else {
            None
        }
    }
}
```

### 5.5 Fast-Path Arithmetic Pseudocode

```
fn add(a: TValue, b: TValue) -> Result<TValue, MetamethodCall> {
    // Fast path 1: both small integers
    if a.is_small_int() && b.is_small_int() {
        let (result, overflow) = a.small_int().overflowing_add(b.small_int());
        if !overflow && fits_in_47_bits(result) {
            return Ok(TValue::from_small_int(result));
        }
        // Overflow: promote to boxed or convert to float
        return Ok(TValue::from_integer(result, gc));
    }

    // Fast path 2: both floats
    if a.is_float() && b.is_float() {
        return Ok(TValue::from_float(a.as_float() + b.as_float()));
    }

    // Fast path 3: mixed int/float → convert int to float
    if a.is_number() && b.is_number() {
        return Ok(TValue::from_float(a.to_float() + b.to_float()));
    }

    // Slow path: metamethod __add
    Err(MetamethodCall::Add(a, b))
}
```

---

## 6. Bytecode & Compiler

### 6.1 Instruction Formats

Selune uses a Lua 5.4-compatible instruction set with 32-bit fixed-width instructions. The instruction formats are:

```
Format iABC:   [  B:8  ][  C:8  ][ A:8  ][ Op:7 ][k:1]
Format iABx:   [    Bx:17       ][ A:8  ][ Op:7 ][0:1]
Format iAsBx:  [   sBx:17       ][ A:8  ][ Op:7 ][0:1]
Format iAx:    [         Ax:25          ][ Op:7  ][0:1]
Format isJ:    [         sJ:25          ][ Op:7  ][0:1]

Fields:
  Op  — 7-bit opcode (0-127, 83 used)
  k   — 1-bit flag (used for various purposes per opcode)
  A   — 8-bit register/argument (0-255)
  B   — 8-bit register/argument (0-255)
  C   — 8-bit register/argument (0-255)
  Bx  — 17-bit unsigned argument (0-131071)
  sBx — 17-bit signed argument (-65536 to 65535)
  Ax  — 25-bit unsigned argument
  sJ  — 25-bit signed jump offset
```

### 6.2 Opcode Table (All 83 Opcodes)

#### Loading & Moving

| Opcode | Format | Description |
|---|---|---|
| `OP_MOVE` | iABC | `R[A] := R[B]` |
| `OP_LOADI` | iAsBx | `R[A] := sBx` (integer) |
| `OP_LOADF` | iAsBx | `R[A] := (float)sBx` |
| `OP_LOADK` | iABx | `R[A] := K[Bx]` (constant) |
| `OP_LOADKX` | iABx | `R[A] := K[extra arg]` |
| `OP_LOADFALSE` | iABC | `R[A] := false` |
| `OP_LFALSESKIP` | iABC | `R[A] := false; pc++` |
| `OP_LOADTRUE` | iABC | `R[A] := true` |
| `OP_LOADNIL` | iABC | `R[A], ..., R[A+B] := nil` |

#### Upvalue Operations

| Opcode | Format | Description |
|---|---|---|
| `OP_GETUPVAL` | iABC | `R[A] := UpValue[B]` |
| `OP_SETUPVAL` | iABC | `UpValue[B] := R[A]` |

#### Table Operations

| Opcode | Format | Description |
|---|---|---|
| `OP_GETTABUP` | iABC | `R[A] := UpValue[B][K[C]:string]` |
| `OP_GETTABLE` | iABC | `R[A] := R[B][R[C]]` |
| `OP_GETI` | iABC | `R[A] := R[B][C]` (integer key) |
| `OP_GETFIELD` | iABC | `R[A] := R[B][K[C]:string]` |
| `OP_SETTABUP` | iABC | `UpValue[A][K[B]:string] := RK(C)` |
| `OP_SETTABLE` | iABC | `R[A][R[B]] := RK(C)` |
| `OP_SETI` | iABC | `R[A][B] := RK(C)` (integer key) |
| `OP_SETFIELD` | iABC | `R[A][K[B]:string] := RK(C)` |
| `OP_NEWTABLE` | iABC | `R[A] := {}` (array=B, hash=C hints) |
| `OP_SETLIST` | iABC | `R[A][C+i] := R[A+i], 1 <= i <= B` |

#### Arithmetic (two-register)

| Opcode | Format | Description |
|---|---|---|
| `OP_ADD` | iABC | `R[A] := R[B] + R[C]` |
| `OP_SUB` | iABC | `R[A] := R[B] - R[C]` |
| `OP_MUL` | iABC | `R[A] := R[B] * R[C]` |
| `OP_MOD` | iABC | `R[A] := R[B] % R[C]` |
| `OP_POW` | iABC | `R[A] := R[B] ^ R[C]` |
| `OP_DIV` | iABC | `R[A] := R[B] / R[C]` (float div) |
| `OP_IDIV` | iABC | `R[A] := R[B] // R[C]` (integer div) |
| `OP_BAND` | iABC | `R[A] := R[B] & R[C]` |
| `OP_BOR` | iABC | `R[A] := R[B] \| R[C]` |
| `OP_BXOR` | iABC | `R[A] := R[B] ~ R[C]` |
| `OP_SHL` | iABC | `R[A] := R[B] << R[C]` |
| `OP_SHR` | iABC | `R[A] := R[B] >> R[C]` |

#### Arithmetic (register + constant)

| Opcode | Format | Description |
|---|---|---|
| `OP_ADDK` | iABC | `R[A] := R[B] + K[C]` |
| `OP_SUBK` | iABC | `R[A] := R[B] - K[C]` |
| `OP_MULK` | iABC | `R[A] := R[B] * K[C]` |
| `OP_MODK` | iABC | `R[A] := R[B] % K[C]` |
| `OP_POWK` | iABC | `R[A] := R[B] ^ K[C]` |
| `OP_DIVK` | iABC | `R[A] := R[B] / K[C]` |
| `OP_IDIVK` | iABC | `R[A] := R[B] // K[C]` |
| `OP_BANDK` | iABC | `R[A] := R[B] & K[C]:integer` |
| `OP_BORK` | iABC | `R[A] := R[B] \| K[C]:integer` |
| `OP_BXORK` | iABC | `R[A] := R[B] ~ K[C]:integer` |

#### Arithmetic (register + immediate)

| Opcode | Format | Description |
|---|---|---|
| `OP_ADDI` | iABC | `R[A] := R[B] + sC` (signed imm) |
| `OP_SHRI` | iABC | `R[A] := R[B] >> sC` |
| `OP_SHLI` | iABC | `R[A] := sC << R[B]` |

#### Unary Operations

| Opcode | Format | Description |
|---|---|---|
| `OP_UNM` | iABC | `R[A] := -R[B]` |
| `OP_BNOT` | iABC | `R[A] := ~R[B]` |
| `OP_NOT` | iABC | `R[A] := not R[B]` |
| `OP_LEN` | iABC | `R[A] := #R[B]` (length) |
| `OP_CONCAT` | iABC | `R[A] := R[A] .. ... .. R[A+B-1]` |

#### Comparison & Testing

| Opcode | Format | Description |
|---|---|---|
| `OP_EQ` | iABC | `if (R[A] == R[B]) ~= k then pc++` |
| `OP_LT` | iABC | `if (R[A] < R[B]) ~= k then pc++` |
| `OP_LE` | iABC | `if (R[A] <= R[B]) ~= k then pc++` |
| `OP_EQK` | iABC | `if (R[A] == K[B]) ~= k then pc++` |
| `OP_EQI` | iABC | `if (R[A] == sB) ~= k then pc++` |
| `OP_LTI` | iABC | `if (R[A] < sB) ~= k then pc++` |
| `OP_LEI` | iABC | `if (R[A] <= sB) ~= k then pc++` |
| `OP_GTI` | iABC | `if (R[A] > sB) ~= k then pc++` |
| `OP_GEI` | iABC | `if (R[A] >= sB) ~= k then pc++` |
| `OP_TEST` | iABC | `if (not R[A]) == k then pc++` |
| `OP_TESTSET` | iABC | `if (not R[B]) == k then pc++ else R[A] := R[B]` |

#### Control Flow

| Opcode | Format | Description |
|---|---|---|
| `OP_JMP` | isJ | `pc += sJ` |
| `OP_CALL` | iABC | `R[A], ..., R[A+C-2] := R[A](R[A+1], ..., R[A+B-1])` |
| `OP_TAILCALL` | iABC | `return R[A](R[A+1], ..., R[A+B-1])` |
| `OP_RETURN` | iABC | `return R[A], ..., R[A+B-2]` |
| `OP_RETURN0` | iABC | `return` (no values) |
| `OP_RETURN1` | iABC | `return R[A]` (single value) |

#### For Loops

| Opcode | Format | Description |
|---|---|---|
| `OP_FORLOOP` | iABx | `R[A] += R[A+2]; if R[A] <?= R[A+1] then pc -= Bx; R[A+3] = R[A]` |
| `OP_FORPREP` | iABx | `if R[A] <type check>; R[A] -= R[A+2]; pc += Bx` |
| `OP_TFORPREP` | iABx | `create upvalue for R[A+3]; pc += Bx` |
| `OP_TFORCALL` | iABC | `R[A+4], ..., R[A+3+C] := R[A](R[A+1], R[A+2])` |
| `OP_TFORLOOP` | iABx | `if R[A+4] ~= nil then R[A+2] = R[A+4] else pc += Bx` |

#### Closure & Vararg

| Opcode | Format | Description |
|---|---|---|
| `OP_CLOSURE` | iABx | `R[A] := closure(KPROTO[Bx])` |
| `OP_VARARG` | iABC | `R[A], ..., R[A+C-2] := vararg` |
| `OP_VARARGPREP` | iABC | `(adjust varargs)` |

#### Miscellaneous

| Opcode | Format | Description |
|---|---|---|
| `OP_SELF` | iABC | `R[A+1] := R[B]; R[A] := R[B][RK(C)]` |
| `OP_CLOSE` | iABC | `close upvalues >= R[A]` |
| `OP_TBC` | iABC | `mark R[A] as to-be-closed` |
| `OP_EXTRAARG` | iAx | `extra argument for previous opcode` |
| `OP_MMBIN` | iABC | `call metamethod for binary op` |
| `OP_MMBINI` | iABC | `call metamethod for binary op with immediate` |
| `OP_MMBINK` | iABC | `call metamethod for binary op with constant` |

### 6.3 Single-Pass Compiler

The compiler is a single-pass recursive descent parser that directly emits bytecode, following the same approach as PUC Lua 5.4:

```
Source → Lexer → Parser/Compiler → Proto (bytecode + constants + debug info)
```

#### Expression Descriptors (ExprDesc)

```rust
/// Describes where an expression's value can be found.
/// Used during compilation to defer code generation.
enum ExprDesc {
    /// Void expression (statement or call with no value)
    Void,
    /// Nil literal
    Nil,
    /// Boolean literal
    True,
    False,
    /// Integer constant
    Integer(i64),
    /// Float constant
    Float(f64),
    /// String constant
    Str(StringId),
    /// Value in register
    Register(RegIndex),
    /// Value in upvalue
    Upvalue(UpvalIndex),
    /// Value in constant table
    Constant(ConstIndex),
    /// Table field: R[table][RK(key)]
    Indexed {
        table: RegIndex,
        key: ExprKey,
    },
    /// Relocatable: result register not yet assigned
    Relocatable(InstrIndex),
    /// Jump: conditional expression encoded as jumps
    Jump {
        true_list: JumpList,
        false_list: JumpList,
    },
    /// Function call (result count not yet fixed)
    Call(InstrIndex),
    /// Vararg expression
    Vararg(InstrIndex),
}
```

#### Backpatching

Jump targets are resolved using linked lists threaded through the jump offset fields of instructions:

```
Backpatching process:
  1. Emit conditional jump with placeholder offset (pointing to itself)
  2. Chain multiple jumps into a linked list (each jump's offset points to previous)
  3. When target is known, walk the list and patch all offsets

Example - compiling `if a and b then ... end`:
  EMIT: TEST R[a], 0           # if not a, skip
  EMIT: JMP  →(self)           # placeholder, add to false_list
  EMIT: TEST R[b], 0           # if not b, skip
  EMIT: JMP  →(prev_jmp)       # chain to false_list
  EMIT: ... (then block) ...
  PATCH: walk false_list, set all JMP targets to here
```

### 6.4 Proto Struct

```rust
/// Function prototype — the compiled representation of a Lua function.
pub struct Proto {
    /// Bytecode instructions
    pub code: Vec<Instruction>,
    /// Constant pool
    pub constants: Vec<TValue>,
    /// Nested function prototypes
    pub protos: Vec<Box<Proto>>,
    /// Upvalue descriptors
    pub upvalues: Vec<UpvalDesc>,
    /// Number of fixed parameters
    pub num_params: u8,
    /// Whether this function uses varargs
    pub is_vararg: bool,
    /// Maximum stack size (registers) needed
    pub max_stack_size: u8,
    /// Source file name
    pub source: Option<StringId>,
    /// Line number mapping (instruction index → line number)
    pub line_info: Vec<i8>,         // relative line info
    pub abs_line_info: Vec<AbsLineInfo>,  // absolute (for large functions)
    /// Local variable debug info
    pub local_vars: Vec<LocalVar>,

    // === JIT metadata (populated during execution) ===
    /// Execution count (for JIT tier-up decisions)
    pub exec_count: Cell<u32>,
    /// Compiled native code pointer (if JIT'd)
    pub jit_code: Cell<Option<*const u8>>,
    /// JIT tier level (0=interpreted, 1=baseline, 2=optimized)
    pub jit_tier: Cell<u8>,
}
```

---

## 7. VM / Interpreter

### 7.1 Register-Based Design

The Selune VM uses a register-based architecture (like Lua 5.4, unlike stack-based VMs like CPython or JVM):

**Advantages:**
- Fewer instructions needed (operands encoded in instruction)
- Better data flow for JIT (registers map naturally to SSA values)
- Less stack manipulation overhead

**Stack Layout:**
```
┌────────────────────────────────────────────────┐
│  R[0]  R[1]  R[2] ... R[N]  │ args for call │ │
│  ←── current frame ──────→  │←── next frame──→│
│  base                        │  new base       │
└────────────────────────────────────────────────┘
```

### 7.2 Dispatch Strategy: Tail-Call Threading

The interpreter uses **tail-call threading** (also called "musttail dispatch") for instruction dispatch:

```rust
// Conceptual dispatch loop (actual implementation uses computed gotos or tail calls)
type DispatchFn = fn(&mut VmState) -> DispatchResult;

static DISPATCH_TABLE: [DispatchFn; NUM_OPCODES] = [
    op_move,
    op_loadi,
    op_loadf,
    // ...
];

fn op_move(state: &mut VmState) -> DispatchResult {
    let instr = state.fetch();
    let (a, b, _) = instr.abc();
    state.regs[a] = state.regs[b];

    // Tail-call to next handler
    let next = state.fetch_opcode();
    DISPATCH_TABLE[next](state)
}
```

**Benefits:**
- Better branch prediction (indirect branch per handler, not central switch)
- Pipeline-friendly (each handler is a small, focused function)
- Easy to instrument (wrap individual handlers for profiling)

### 7.3 Inline Caching with Shape System

For fast property access on tables, we use **inline caches** backed by a **shape (hidden class) system**:

```
Shape System:
  - Each table has a "shape" that describes its key layout
  - Tables with the same set of string keys (in the same order) share a shape
  - Property access checks shape match → direct offset lookup

Inline Cache Structure:
  ┌──────────────┐
  │  shape_id    │  ← expected shape
  │  offset      │  ← cached property offset
  └──────────────┘

GETFIELD R[A], R[B], "name"
  1. Load IC for this instruction
  2. If R[B].shape == IC.shape_id:
       R[A] = R[B].values[IC.offset]     # fast path (1 comparison + 1 load)
  3. Else:
       result = full_table_lookup(R[B], "name")  # slow path
       Update IC with new shape + offset          # repatch
       R[A] = result
```

### 7.4 Metamethod Dispatch

```rust
/// Metamethod event types (matching Lua 5.4).
#[repr(u8)]
pub enum Metamethod {
    Add = 0,    // __add
    Sub,        // __sub
    Mul,        // __mul
    Mod,        // __mod
    Pow,        // __pow
    Div,        // __div
    Idiv,       // __idiv
    Band,       // __band
    Bor,        // __bor
    Bxor,       // __bxor
    Shl,        // __shl
    Shr,        // __shr
    Unm,        // __unm
    Bnot,       // __bnot
    Eq,         // __eq
    Lt,         // __lt
    Le,         // __le
    Index,      // __index
    Newindex,   // __newindex
    Call,       // __call
    Concat,     // __concat
    Len,        // __len
    Close,      // __close
    Gc,         // __gc
    Tostring,   // __tostring
    Name,       // __name
    Pairs,      // __pairs
    Count,      // sentinel
}

/// Dispatch flow for metamethods:
///
/// 1. Check if operation has fast path (both operands are numbers, etc.)
/// 2. If not, get metatable of first operand (or second for commutative ops)
/// 3. Look up metamethod field (e.g., __add)
/// 4. If found, call it: metamethod(operand1, operand2)
/// 5. If not found, try second operand's metatable
/// 6. If still not found, raise error
```

### 7.5 Error Handling

Selune uses Rust's `Result` type instead of C's `setjmp/longjmp`:

```rust
/// VM error type.
pub enum LuaError {
    /// Runtime error with message
    Runtime(String),
    /// Error in error handler (double fault)
    ErrorHandler(String),
    /// Memory allocation failure
    Memory,
    /// Explicit error() call from Lua
    Explicit(TValue),
    /// Yield from coroutine
    Yield,
}

/// Protected call implementation.
fn pcall(state: &mut LuaState, func: TValue, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    // Rust's Result naturally provides protected call semantics
    // No setjmp/longjmp needed — stack unwinding is safe
    match state.call(func, args) {
        Ok(results) => Ok(results),
        Err(e) => {
            // Stack is automatically cleaned up by Rust's drop semantics
            Err(e)
        }
    }
}
```

### 7.6 Profiling for JIT

The interpreter collects execution profiles to inform JIT compilation decisions:

```
Profiling Data Collected:
  - Function call count (per Proto) → trigger method compilation
  - Loop back-edge count (per loop header) → trigger loop compilation
  - Type feedback (per instruction) → specialize JIT code
    - Arithmetic: int+int, float+float, mixed
    - Table access: shape encountered, hit/miss ratio
    - Comparison: types compared, common results

Tier-Up Thresholds:
  - Tier 0 → Tier 1 (baseline):  function called 100 times OR loop iterated 1000 times
  - Tier 1 → Tier 2 (optimizing): function called 10,000 times with stable type profile
```

---

## 8. JIT Compilation Pipeline

### 8.1 Three-Tier Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Execution Tiers                           │
│                                                             │
│  Tier 0: Interpreter                                        │
│  ├── All code starts here                                   │
│  ├── Collects type profiles and execution counts            │
│  └── Triggers tier-up to Tier 1                             │
│                                                             │
│  Tier 1: Baseline JIT                                       │
│  ├── Fast compilation (< 1ms per function)                  │
│  ├── 1:1 bytecode-to-native translation                     │
│  ├── No optimizations (simple register allocation)          │
│  ├── Includes type guards based on profiling data           │
│  └── Triggers tier-up to Tier 2 for hot functions           │
│                                                             │
│  Tier 2: Optimizing JIT                                     │
│  ├── Slower compilation (1-10ms per function)               │
│  ├── Full Cranelift optimization pipeline                   │
│  ├── Type specialization, inlining, constant folding        │
│  ├── Loop-invariant code motion, dead code elimination      │
│  └── Deoptimization back to Tier 0 on guard failure         │
└─────────────────────────────────────────────────────────────┘
```

### 8.2 Method-Based JIT Rationale

**Why method-based (not trace-based like LuaJIT)?**

| Aspect | Trace-Based (LuaJIT) | Method-Based (Selune) |
|---|---|---|
| Compilation unit | Linear trace (hot path) | Entire function |
| Side exits | Frequent, need stitching | Natural (branches in IR) |
| Nested loops | Problematic (trace explosion) | Natural |
| Inlining | Implicit (trace follows calls) | Explicit (call graph analysis) |
| Cranelift fit | Poor (expects function IR) | Excellent |
| Implementation complexity | High (trace recording, linking) | Moderate |
| Polymorphic code | Poor (trace per path) | Good (type guards + fallback) |

**Decision:** Method-based JIT aligns with Cranelift's function-at-a-time compilation model. Trace-based would require building a custom trace IR and stitching layer, negating Cranelift's benefits.

### 8.3 Cranelift Integration

```rust
/// JIT compile a Lua function using Cranelift.
fn jit_compile_function(
    proto: &Proto,
    profile: &TypeProfile,
    tier: JitTier,
) -> Result<CompiledCode, JitError> {
    let mut module = JITModule::new(default_isa()?);
    let mut ctx = module.make_context();
    let mut builder_ctx = FunctionBuilderContext::new();

    // 1. Create Cranelift function signature
    //    All Lua functions have the same native signature:
    //    fn(state: *mut VmState, base: *mut TValue, nargs: u32) -> u32
    let sig = create_lua_signature(&mut module);

    // 2. Build Cranelift IR from bytecode
    let func_id = module.declare_function("lua_func", Linkage::Local, &sig)?;
    ctx.func.signature = sig;

    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);

        // Create entry block
        let entry = builder.create_block();
        builder.switch_to_block(entry);
        builder.append_block_params_for_function_params(entry);

        // Translate each bytecode instruction to Cranelift IR
        let translator = match tier {
            JitTier::Baseline => BaselineTranslator::new(&mut builder, proto),
            JitTier::Optimizing => OptimizingTranslator::new(&mut builder, proto, profile),
        };
        translator.translate()?;

        builder.seal_all_blocks();
        builder.finalize();
    }

    // 3. Compile and get native code
    module.define_function(func_id, &mut ctx)?;
    module.finalize_definitions()?;

    let code_ptr = module.get_finalized_function(func_id);

    Ok(CompiledCode {
        ptr: code_ptr,
        tier,
    })
}
```

### 8.4 Baseline JIT (Tier 1) Design

The baseline JIT performs a straightforward 1:1 translation of bytecode to native code:

```
Bytecode: OP_ADD R[3], R[1], R[2]

Baseline JIT output (pseudo-assembly):
  ; Load operands from register array
  mov rax, [reg_base + 1*8]    ; rax = R[1]
  mov rcx, [reg_base + 2*8]    ; rcx = R[2]

  ; Type check: both small integers?
  mov rdx, rax
  and rdx, rcx
  and rdx, NAN_INT_MASK
  cmp rdx, NAN_INT_TAG
  jne slow_path

  ; Fast path: integer add
  and rax, PAYLOAD_MASK         ; extract integer payload
  and rcx, PAYLOAD_MASK
  add rax, rcx
  jo  overflow                   ; check overflow
  or  rax, NAN_INT_TAG          ; re-tag as integer
  mov [reg_base + 3*8], rax    ; store R[3]
  jmp next_instruction

slow_path:
  ; Call interpreter helper for metamethod dispatch
  call vm_add_slow
  jmp next_instruction
```

### 8.5 Optimizing JIT (Tier 2) Design

The optimizing JIT leverages type profiles and Cranelift's optimization passes:

```
Optimizations applied:
  1. Type Specialization
     - If profile says "R[1] is always integer" → remove type check
     - Insert deoptimization guard for type changes

  2. Inlining
     - Inline small, frequently-called Lua functions
     - Inline known metamethods
     - Budget: max 500 IR nodes per inline site

  3. Constant Folding / Propagation
     - Fold operations on constants
     - Propagate known upvalue values

  4. Loop Optimizations
     - Loop-invariant code motion (LICM)
     - Strength reduction for loop counters
     - Range check elimination for array accesses

  5. Allocation Sinking
     - Delay table allocations past branches where they may not be needed
     - Scalar replacement for short-lived tables

  6. Dead Code Elimination
     - Remove unused computations
     - Remove unreachable branches based on type specialization
```

### 8.6 Deoptimization & On-Stack Replacement (OSR)

```
Deoptimization (JIT → Interpreter):
  Triggers:
    - Type guard failure (value is not the specialized type)
    - Shape guard failure (table shape changed)
    - Overflow in specialized integer arithmetic
    - Uncommon trap (rarely-taken branch)

  Process:
    1. JIT code hits a guard failure
    2. Save current native state (registers, stack)
    3. Map native state back to bytecode state using "deopt info"
       - Each deopt point has a map: native register → bytecode register
       - Includes the bytecode PC to resume at
    4. Reconstruct interpreter stack frame
    5. Resume execution in interpreter at the correct bytecode PC
    6. Record deopt reason for future JIT decisions
       - Too many deopts → blacklist this specialization
       - Recompile with less aggressive assumptions

OSR (Interpreter → JIT, mid-function):
  Triggers:
    - Long-running loop detected in interpreter
    - Function was JIT-compiled while already executing

  Process:
    1. At loop back-edge, check if JIT code is available
    2. Map interpreter state to JIT entry point
    3. Build OSR entry stub that loads interpreter values into native registers
    4. Jump to JIT code at the loop header
```

### 8.7 GC Interaction with JIT Code

```
JIT-compiled code must cooperate with the garbage collector:

  1. Write Barriers
     - JIT code emits write barrier calls after pointer stores
     - Barrier is a function call: barrier(container, value)
     - JIT can optimize: skip barrier if value is not a GC object

  2. Safe Points
     - GC can only run at safe points where all roots are visible
     - JIT code inserts safe point checks at:
       - Function entry/exit
       - Loop back-edges
       - Allocation sites
     - Safe point = poll a flag + conditional call to GC

  3. Stack Maps
     - At each safe point, JIT emits a "stack map" describing:
       - Which native registers/stack slots contain GC pointers
       - Which contain unboxed integers/floats (not pointers)
     - GC reads stack maps to find all roots in JIT frames

  4. Code Patching
     - When GC moves objects (if compacting), need to patch JIT code
     - Design decision: non-moving GC → no code patching needed
     - Trade-off: some fragmentation vs. simpler JIT
```

---

## 9. Garbage Collection Design

### 9.1 Overview

Selune implements both **incremental** and **generational** garbage collection modes, matching Lua 5.4's dual-mode GC:

- **Incremental mode**: Tri-color mark-sweep with incremental steps
- **Generational mode**: Two-generation collector (young + old) with occasional full sweeps
- **Default**: Generational mode (Lua 5.4 default since 5.4.0)

### 9.2 Tri-Color Mark-Sweep

```
Object Colors:
  WHITE  — Not yet visited (potential garbage)
  GRAY   — Visited but children not yet scanned
  BLACK  — Visited and all children scanned (definitely alive)

Invariant (incremental):
  A BLACK object never points directly to a WHITE object.
  Enforced by write barriers.

GC Phases:
  1. PAUSE      — Waiting for next cycle
  2. PROPAGATE  — Scan gray objects (incremental steps)
  3. ATOMIC     — Final mark phase (stop-the-world, brief)
  4. SWEEP      — Reclaim white objects (incremental steps)

Incremental Stepping:
  - GC work is proportional to allocation
  - gcstepmul controls ratio (default: 100 = 1:1 with allocation)
  - Each allocation triggers a small amount of GC work
```

### 9.3 Generational GC

```
Two Generations:
  YOUNG — Recently allocated objects (most garbage is young)
  OLD   — Objects that survived at least one minor collection

Minor Collection (frequent):
  1. Only scan YOUNG objects
  2. Objects referenced by OLD are roots (tracked via write barrier)
  3. Surviving YOUNG objects are promoted to OLD
  4. Very fast (proportional to young set size)

Major Collection (infrequent):
  1. Full mark-sweep of all objects
  2. Triggered when:
     - Minor collections aren't freeing enough memory
     - Explicitly requested via `collectgarbage("collect")`
  3. Reset generation markers

Generational Write Barrier:
  When an OLD object is modified to point to a YOUNG object:
    - Mark the OLD object as "touched" (needs re-scanning)
    - This is a "back barrier" (move old object backward to gray)
```

### 9.4 Write Barriers

```rust
/// Forward barrier: when a BLACK object gains a reference to a WHITE object,
/// mark the WHITE object gray (push it forward in the marking).
fn barrier_forward(gc: &mut Gc, container: GcPtr, value: GcPtr) {
    if gc.is_black(container) && gc.is_white(value) {
        gc.mark_gray(value);  // push value forward
    }
}

/// Back barrier: when a BLACK object is modified, mark it gray
/// (push it backward for re-scanning).
/// Used in generational mode for old→young references.
fn barrier_back(gc: &mut Gc, container: GcPtr) {
    if gc.is_black(container) {
        gc.mark_gray(container);  // push container backward
        if gc.is_generational() {
            gc.mark_touched(container);  // track for minor collection
        }
    }
}

/// Barrier decision:
/// - Table modifications → back barrier (table is re-scanned)
/// - Other objects → forward barrier (new reference is marked)
///
/// Rationale: Tables are modified frequently; re-scanning them
/// once is cheaper than forward-barriering every write.
```

### 9.5 Arena Allocation

```
Memory Allocation Strategy:
  - Small objects (≤ 256 bytes): Arena allocator with size classes
  - Large objects (> 256 bytes): Direct allocation via system allocator

Arena Design:
  ┌─────────────────────────────────────────┐
  │  Size Class: 32 bytes                   │
  │  ┌──────┬──────┬──────┬──────┬─────┐   │
  │  │ obj1 │ obj2 │ free │ obj4 │ ... │   │
  │  └──────┴──────┴──────┴──────┴─────┘   │
  │  Free list: free → ...                  │
  ├─────────────────────────────────────────┤
  │  Size Class: 64 bytes                   │
  │  ┌──────┬──────┬──────┬──────┬─────┐   │
  │  │ obj1 │ free │ obj3 │ free │ ... │   │
  │  └──────┴──────┴──────┴──────┴─────┘   │
  │  Free list: free → free → ...           │
  ├─────────────────────────────────────────┤
  │  Size Class: 128 bytes                  │
  │  ...                                    │
  └─────────────────────────────────────────┘

Size Classes: 16, 32, 48, 64, 80, 96, 128, 192, 256
  - Covers most Lua objects (TString, Table headers, Closure, etc.)
  - 12.5% maximum internal fragmentation
```

### 9.6 Finalizers and To-Be-Closed

```
Finalizer (__gc metamethod):
  1. Objects with __gc are placed on a "finalization" list
  2. During sweep, instead of freeing, move to "finalize" list
  3. At safe points, call __gc methods in reverse order of creation
  4. After __gc runs, object is freed in the next GC cycle
  5. Resurrections: __gc can make the object reachable again
     → Object survives this cycle, __gc won't be called again

To-Be-Closed (<close> attribute, Lua 5.4):
  1. Variables marked with <close> trigger __close on scope exit
  2. __close is called even on error (like RAII / defer)
  3. Implementation:
     - Compiler emits OP_TBC when a <close> variable is created
     - OP_CLOSE instruction at scope exit triggers __close
     - Error paths also call __close (Rust's Drop-like semantics)
  4. Multiple to-be-closed variables: called in reverse order
```

---

## 10. Table & String Implementation

### 10.1 Hybrid Array + Hash Table

Lua tables serve as both arrays and dictionaries. Selune uses a hybrid representation:

```
Table Layout:
  ┌──────────────────────────────────────────────────┐
  │  Table Header                                     │
  │  ├── GC header (color, type tag, etc.)           │
  │  ├── shape: ShapeId        ← for inline caching  │
  │  ├── metatable: Option<TablePtr>                  │
  │  ├── array: Vec<TValue>    ← integer keys 1..N   │
  │  ├── hash: SwissTable      ← string/other keys   │
  │  ├── array_len: u32        ← logical array length │
  │  └── flags: TableFlags     ← has_metatable, etc.  │
  └──────────────────────────────────────────────────┘

Array Part:
  - Stores values for integer keys 1, 2, 3, ..., N
  - Grows/shrinks as needed
  - Access: O(1) direct index
  - boundary (#t): binary search for nil boundary

Hash Part (Swiss Table):
  - Stores all non-integer keys and sparse integer keys
  - Swiss Table (based on Google's flat_hash_map / hashbrown)
  - Benefits:
    - SIMD-accelerated lookup (SSE2/NEON)
    - Excellent cache locality (flat layout)
    - Low memory overhead (~1 byte metadata per slot)
    - Robin Hood-like probing without the deletion complexity
```

### 10.2 Swiss Table Detail

```
Swiss Table Layout:
  ┌─────────────────────────────────────────┐
  │ Control bytes (1 byte per slot):        │
  │ [H7][H7][H7][EMPTY][H7][DEL][H7]...   │
  │  H7 = top 7 bits of hash               │
  │  EMPTY = 0xFF                            │
  │  DELETED = 0x80                          │
  ├─────────────────────────────────────────┤
  │ Slots (key-value pairs):                │
  │ [(key, value)] [(key, value)] ...       │
  └─────────────────────────────────────────┘

Lookup:
  1. Compute hash of key
  2. Use lower bits to find group (16 slots)
  3. SIMD compare H7 byte against all 16 control bytes simultaneously
  4. Check matching slots for full key equality
  5. If no match in group, probe next group

Performance:
  - Successful lookup: ~1.0-1.5 probes average
  - Unsuccessful lookup: ~1.0 probes average
  - Cache-friendly: control bytes fit in SIMD register
```

### 10.3 Shape System for Inline Caching

```
Shape Transition Tree:

  Empty Shape (id=0)
       │
       ├── + "x" → Shape(id=1, {x: offset 0})
       │              │
       │              ├── + "y" → Shape(id=2, {x: 0, y: 1})
       │              │              │
       │              │              └── + "z" → Shape(id=3, {x: 0, y: 1, z: 2})
       │              │
       │              └── + "name" → Shape(id=4, {x: 0, name: 1})
       │
       └── + "name" → Shape(id=5, {name: offset 0})

Tables with the same shape share structure:
  t1 = {x=1, y=2}  → shape_id=2, values=[1, 2]
  t2 = {x=5, y=8}  → shape_id=2, values=[5, 8]

Inline cache matches on shape_id → direct array offset access.
```

### 10.4 String Interning with SSO

```
String Representation:
  ┌──────────────────────────────────┐
  │  Short Strings (≤ 40 bytes)      │
  │  ├── Interned (deduplicated)     │
  │  ├── Hash cached in header       │
  │  ├── Equality = pointer compare  │
  │  └── Stored in global intern set │
  ├──────────────────────────────────┤
  │  Long Strings (> 40 bytes)       │
  │  ├── NOT interned (lazy hash)    │
  │  ├── Hash computed on first use  │
  │  ├── Equality = hash + memcmp   │
  │  └── GC-allocated normally       │
  └──────────────────────────────────┘

Small String Optimization (SSO):
  TString struct:
    ┌────────────────────────────────────┐
    │  GC header         (8 bytes)       │
    │  hash: u32         (4 bytes)       │
    │  len: u32          (4 bytes)       │
    │  ┌─── union ──────────────────┐    │
    │  │  short: [u8; 40]  (inline) │    │
    │  │  long: *const u8  (pointer)│    │
    │  └────────────────────────────┘    │
    └────────────────────────────────────┘

  For strings ≤ 40 bytes:
    - Data stored directly in the struct (no extra allocation)
    - Single cache line for header + data
    - Covers ~95% of strings in typical Lua programs

  For strings > 40 bytes:
    - Pointer to separately allocated data
    - Lazy hashing (hash computed when first needed)
```

### 10.5 String Interning Implementation

```rust
/// Global string intern table.
pub struct StringInterner {
    /// Hash set of interned short strings.
    /// Key = hash, Value = linked list of TString with same hash.
    buckets: Vec<Option<GcPtr<TString>>>,
    /// Number of interned strings.
    count: usize,
    /// Resize threshold.
    threshold: usize,
}

impl StringInterner {
    /// Intern a short string, returning existing or creating new.
    pub fn intern(&mut self, bytes: &[u8], gc: &mut Gc) -> GcPtr<TString> {
        debug_assert!(bytes.len() <= SHORT_STRING_MAX);

        let hash = string_hash(bytes);
        let bucket = (hash as usize) % self.buckets.len();

        // Search existing strings in bucket
        let mut current = self.buckets[bucket];
        while let Some(ptr) = current {
            let s = gc.deref(ptr);
            if s.hash == hash && s.as_bytes() == bytes {
                return ptr;  // Found existing
            }
            current = s.next_intern;
        }

        // Not found — create and intern
        let new_str = gc.alloc_short_string(bytes, hash);
        new_str.next_intern = self.buckets[bucket];
        self.buckets[bucket] = Some(new_str);
        self.count += 1;

        if self.count > self.threshold {
            self.resize();
        }

        new_str
    }
}
```

---

## 11. Coroutine Implementation

### 11.1 Stackful Asymmetric Coroutines

Lua 5.4 coroutines are **stackful** (can yield from any depth) and **asymmetric** (explicit resume/yield, not symmetric switching):

```
Coroutine State Machine:
  SUSPENDED ──resume──► RUNNING ──yield──► SUSPENDED
       │                    │
       │                    └──return/error──► DEAD
       │
       └──(initial)──► SUSPENDED (created but not started)

States:
  SUSPENDED — Created or yielded, waiting for resume
  RUNNING   — Currently executing
  NORMAL    — Resumed another coroutine (parent)
  DEAD      — Finished execution (returned or errored)
```

### 11.2 Implementation Design

```rust
/// Lua coroutine (thread).
pub struct Thread {
    /// GC header
    gc_header: GcHeader,
    /// Coroutine status
    status: ThreadStatus,
    /// The stack for this coroutine
    stack: Vec<TValue>,
    /// Call info chain (linked list of active function calls)
    call_info: CallInfo,
    /// Base of current call frame
    base: usize,
    /// Top of stack (first free slot)
    top: usize,
    /// Open upvalues pointing into this stack
    open_upvalues: Option<GcPtr<UpValue>>,
    /// To-be-closed variable indices
    tbc_list: Vec<usize>,
    /// Error recovery info
    error_jmp: Option<ErrorJump>,
    /// Global state reference
    global: *mut GlobalState,
}

/// Resume a coroutine.
pub fn coroutine_resume(
    caller: &mut Thread,
    callee: &mut Thread,
    args: &[TValue],
) -> Result<Vec<TValue>, LuaError> {
    assert!(callee.status == ThreadStatus::Suspended);

    callee.status = ThreadStatus::Running;
    caller.status = ThreadStatus::Normal;

    // Push arguments onto callee's stack
    callee.push_values(args);

    // Execute callee until yield or return
    match callee.execute() {
        Ok(results) => {
            callee.status = ThreadStatus::Dead;
            caller.status = ThreadStatus::Running;
            Ok(results)
        }
        Err(LuaError::Yield) => {
            // callee.status already set to Suspended by yield
            caller.status = ThreadStatus::Running;
            Ok(callee.pop_yield_values())
        }
        Err(e) => {
            callee.status = ThreadStatus::Dead;
            caller.status = ThreadStatus::Running;
            Err(e)
        }
    }
}
```

### 11.3 Yield from JIT

Yielding from within JIT-compiled code requires deoptimization:

```
Yield-from-JIT Process:
  1. Lua code calls coroutine.yield() inside JIT-compiled function
  2. yield() is recognized as a special function by the JIT
  3. JIT emits a "yield point" which:
     a. Saves all live values to the interpreter stack
     b. Records the current bytecode position
     c. Triggers deoptimization (JIT frame → interpreter frame)
  4. Control returns to the resume point as if interpreter had yielded
  5. On resume, execution continues in the interpreter
     - If the function is still hot, it may be re-entered via OSR

Alternative (simpler, Phase 1):
  - Functions containing yield are never JIT-compiled
  - Only the inner loops (that don't yield) get JIT'd
  - Acceptable performance trade-off for initial release
```

---

## 12. FFI Design

### 12.1 Two-Phase FFI Architecture

```
Phase 1 (Interpreter mode):
  - Use libffi for dynamic foreign function calls
  - Parse C declarations to understand function signatures
  - Marshal Lua values ↔ C values at runtime
  - Works everywhere libffi works
  - Performance: ~100ns per call overhead

Phase 2 (JIT-inlined):
  - JIT compiler generates direct native calls
  - C function pointer called with correct ABI
  - No marshaling overhead for compatible types
  - Performance: ~5ns per call overhead (same as C→C)
  - Requires knowing exact signature at JIT time
```

### 12.2 C Declaration Parser

```
Supported C declarations:
  ffi.cdef[[
    typedef struct { int x, y; } Point;
    int printf(const char *fmt, ...);
    double sqrt(double x);
    void *malloc(size_t size);
    void free(void *ptr);
    typedef void (*callback_t)(int, void*);
  ]]

Parser output:
  - Function signatures (name, return type, parameter types, varargs)
  - Struct/union layouts (fields, offsets, alignment, size)
  - Typedef aliases
  - Enum values
  - Pointer types with pointed-to type info
```

### 12.3 Type Mapping

| C Type | Lua Type | TValue Representation | Notes |
|---|---|---|---|
| `int8_t`, `int16_t`, `int32_t`, `int64_t` | `integer` | Small int or boxed | Sign-extended |
| `uint8_t`, `uint16_t`, `uint32_t` | `integer` | Small int | Zero-extended |
| `uint64_t` | `integer` | Boxed int (may overflow) | Warning on > 2^63-1 |
| `float`, `double` | `number` | IEEE 754 float | Direct bitcast for double |
| `bool` / `_Bool` | `boolean` | NaN-boxed bool | 0=false, else true |
| `char *` / `const char *` | `string` | GC string pointer | Null-terminated copy |
| `void *` | `lightuserdata` | NaN-boxed pointer | No ownership |
| `struct T` | `cdata` (userdata) | Userdata with layout | FFI-managed memory |
| `T *` (typed pointer) | `cdata` | Userdata with type info | Supports arithmetic |
| `T[N]` (array) | `cdata` | Userdata with array layout | Bounds-checked |
| `function pointer` | `cdata` or `function` | Callable userdata | Auto-wrapped |
| `enum` | `integer` | Small int | Named constants |

---

## 13. Standard Library

### 13.1 Module Overview

| Module | Priority | Key Functions | Notes |
|---|---|---|---|
| **basic** | P0 | `print`, `type`, `tostring`, `tonumber`, `error`, `pcall`, `xpcall`, `assert`, `select`, `pairs`, `ipairs`, `next`, `rawget`, `rawset`, `rawequal`, `rawlen`, `setmetatable`, `getmetatable`, `require`, `load`, `dofile`, `loadfile`, `collectgarbage`, `warn` | Core functions |
| **string** | P0 | `string.byte`, `string.char`, `string.find`, `string.format`, `string.gmatch`, `string.gsub`, `string.len`, `string.lower`, `string.upper`, `string.match`, `string.rep`, `string.reverse`, `string.sub`, `string.dump`, `string.pack`, `string.unpack`, `string.packsize` | Pattern matching engine |
| **table** | P0 | `table.concat`, `table.insert`, `table.remove`, `table.sort`, `table.move`, `table.pack`, `table.unpack` | Array operations |
| **math** | P0 | `math.abs`, `math.ceil`, `math.floor`, `math.sqrt`, `math.sin`, `math.cos`, `math.tan`, `math.log`, `math.exp`, `math.random`, `math.randomseed`, `math.maxinteger`, `math.mininteger`, `math.tointeger`, `math.type`, `math.huge`, `math.pi` | IEEE 754 compliance |
| **io** | P1 | `io.open`, `io.close`, `io.read`, `io.write`, `io.lines`, `io.input`, `io.output`, `io.tmpfile`, `io.type`, `io.flush`, `io.popen` | File I/O |
| **os** | P1 | `os.clock`, `os.date`, `os.difftime`, `os.time`, `os.execute`, `os.getenv`, `os.remove`, `os.rename`, `os.tmpname`, `os.exit`, `os.setlocale` | OS interaction |
| **coroutine** | P0 | `coroutine.create`, `coroutine.resume`, `coroutine.yield`, `coroutine.status`, `coroutine.wrap`, `coroutine.isyieldable`, `coroutine.close` | Coroutine control |
| **utf8** | P1 | `utf8.char`, `utf8.codes`, `utf8.codepoint`, `utf8.len`, `utf8.offset`, `utf8.charpattern` | UTF-8 support |
| **debug** | P2 | `debug.getinfo`, `debug.getlocal`, `debug.setlocal`, `debug.getupvalue`, `debug.setupvalue`, `debug.traceback`, `debug.sethook`, `debug.gethook`, `debug.getmetatable`, `debug.setmetatable`, `debug.getregistry`, `debug.getuservalue`, `debug.setuservalue`, `debug.upvalueid`, `debug.upvaluejoin` | Debugging support |
| **package** | P0 | `require`, `package.loaded`, `package.path`, `package.cpath`, `package.preload`, `package.searchpath`, `package.config` | Module system |

### 13.2 Pattern Matching Engine

Lua uses its own pattern matching syntax (not regular expressions). Key features:

```
Pattern Classes:
  .   — any character
  %a  — letters
  %d  — digits
  %l  — lowercase
  %u  — uppercase
  %w  — alphanumeric
  %s  — whitespace
  %p  — punctuation
  %c  — control characters
  %x  — hexadecimal digits
  [set]   — character set
  [^set]  — complement set

Quantifiers:
  *   — 0 or more (greedy)
  +   — 1 or more (greedy)
  -   — 0 or more (lazy)
  ?   — 0 or 1

Anchors:
  ^   — start of string
  $   — end of string

Captures:
  ()      — positional capture
  (pat)   — substring capture
  %n      — back-reference (n = 1-9)

Implementation:
  - Recursive backtracking (like PUC Lua)
  - Stack depth limit to prevent catastrophic backtracking
  - NFA-based alternative considered for v2
```

### 13.3 Rust Function Signature

```rust
/// Signature for Rust functions callable from Lua.
///
/// Takes a mutable reference to the Lua state and returns:
/// - Ok(n): number of return values pushed on the stack
/// - Err(e): Lua error to be raised
pub type RustFunction = fn(&mut LuaState) -> Result<u32, LuaError>;

/// Example: implementing print()
fn lua_print(state: &mut LuaState) -> Result<u32, LuaError> {
    let nargs = state.get_top();
    for i in 1..=nargs {
        if i > 1 {
            print!("\t");
        }
        // Call tostring on each argument
        let s = state.to_string(i)?;
        print!("{}", s);
    }
    println!();
    Ok(0)  // print returns no values
}
```

---

## 14. Cross-Platform Support

### 14.1 Platform Support Matrix

| Platform | Architecture | Interpreter | Baseline JIT | Optimizing JIT | Priority |
|---|---|---|---|---|---|
| **Linux** | x86_64 | Yes | Yes | Yes | P0 |
| **Linux** | aarch64 | Yes | Yes | Yes | P0 |
| **macOS** | x86_64 | Yes | Yes | Yes | P0 |
| **macOS** | aarch64 (Apple Silicon) | Yes | Yes | Yes | P0 |
| **Windows** | x86_64 | Yes | Yes | Yes | P1 |
| **Windows** | aarch64 | Yes | Planned | Planned | P2 |
| **FreeBSD** | x86_64 | Yes | Yes | Yes | P2 |
| **iOS** | aarch64 | Yes | **No** (policy) | **No** (policy) | P2 |
| **Android** | aarch64 | Yes | Yes | Yes | P2 |
| **WASM** | wasm32 | Yes | **No** (no native codegen) | **No** | P3 |

### 14.2 W^X Compliance

Modern operating systems enforce **Write XOR Execute (W^X)**: memory cannot be simultaneously writable and executable. JIT compilers must comply:

#### macOS (Apple Silicon)

```rust
// macOS on Apple Silicon uses MAP_JIT + pthread_jit_write_protect_np
use libc::{mmap, MAP_JIT, MAP_PRIVATE, MAP_ANON, PROT_READ, PROT_WRITE, PROT_EXEC};

fn alloc_jit_memory(size: usize) -> *mut u8 {
    unsafe {
        let ptr = mmap(
            std::ptr::null_mut(),
            size,
            PROT_READ | PROT_WRITE | PROT_EXEC,  // Allowed with MAP_JIT
            MAP_PRIVATE | MAP_ANON | MAP_JIT,
            -1,
            0,
        );
        ptr as *mut u8
    }
}

fn write_jit_code(ptr: *mut u8, code: &[u8]) {
    unsafe {
        // Switch thread to write mode
        pthread_jit_write_protect_np(0);  // 0 = writable

        std::ptr::copy_nonoverlapping(code.as_ptr(), ptr, code.len());

        // Switch back to execute mode
        pthread_jit_write_protect_np(1);  // 1 = executable

        // Clear instruction cache
        sys_icache_invalidate(ptr as *mut _, code.len());
    }
}
```

#### Linux

```rust
// Linux uses mprotect to toggle between W and X
use libc::{mmap, mprotect, MAP_PRIVATE, MAP_ANON, PROT_READ, PROT_WRITE, PROT_EXEC};

fn alloc_jit_memory(size: usize) -> *mut u8 {
    unsafe {
        let ptr = mmap(
            std::ptr::null_mut(),
            size,
            PROT_READ | PROT_WRITE,  // Start writable
            MAP_PRIVATE | MAP_ANON,
            -1,
            0,
        );
        ptr as *mut u8
    }
}

fn finalize_jit_code(ptr: *mut u8, size: usize) {
    unsafe {
        // Switch from writable to executable
        mprotect(ptr as *mut _, size, PROT_READ | PROT_EXEC);
    }
}
```

#### Windows

```rust
// Windows uses VirtualAlloc / VirtualProtect
use windows_sys::Win32::System::Memory::*;

fn alloc_jit_memory(size: usize) -> *mut u8 {
    unsafe {
        VirtualAlloc(
            std::ptr::null(),
            size,
            MEM_COMMIT | MEM_RESERVE,
            PAGE_READWRITE,  // Start writable
        ) as *mut u8
    }
}

fn finalize_jit_code(ptr: *mut u8, size: usize) {
    unsafe {
        let mut old_protect = 0u32;
        VirtualProtect(
            ptr as *const _,
            size,
            PAGE_EXECUTE_READ,  // Switch to executable
            &mut old_protect,
        );
        FlushInstructionCache(GetCurrentProcess(), ptr as *const _, size);
    }
}
```

### 14.3 Calling Conventions

| Platform | Convention | Register args | Stack alignment | Notes |
|---|---|---|---|---|
| Linux x86_64 | System V AMD64 | rdi, rsi, rdx, rcx, r8, r9 | 16-byte | Red zone: 128 bytes |
| macOS x86_64 | System V AMD64 | Same as Linux | 16-byte | Same ABI |
| macOS aarch64 | AAPCS64 | x0-x7 (int), d0-d7 (float) | 16-byte | Apple variant |
| Windows x86_64 | Microsoft x64 | rcx, rdx, r8, r9 | 16-byte | Shadow space: 32 bytes |
| Linux aarch64 | AAPCS64 | x0-x7 (int), d0-d7 (float) | 16-byte | Standard ARM64 |

---

## 15. Development Phases

### Phase 1: Foundation (Weeks 1-8)

> **Goal:** Lexer, parser, bytecode compiler, basic value types

- [ ] Set up Cargo workspace with all crate stubs
- [ ] Implement lexer (all Lua 5.4 tokens, string escapes, long strings, numerals)
- [ ] Implement NaN-boxed TValue (nil, boolean, integer, float)
- [ ] Implement string type with interning and SSO
- [ ] Implement single-pass compiler (expressions, statements, locals)
- [ ] Implement control flow compilation (if/elseif/else, while, repeat, for)
- [ ] Implement function compilation (closures, upvalues, varargs)
- [ ] Implement constant folding in compiler
- [ ] Bytecode serialization (dump/undump compatible with PUC format)
- [ ] Unit tests for lexer, compiler, value types
- [ ] **Milestone:** Can compile any valid Lua 5.4 source to bytecode

### Phase 2: Interpreter (Weeks 9-18)

> **Goal:** Working interpreter that can run Lua programs

- [ ] Implement register-based VM dispatch loop
- [ ] Implement all 83 opcodes (arithmetic, comparison, control flow, table, closure)
- [ ] Implement table type (hybrid array + hash)
- [ ] Implement metamethod dispatch for all operations
- [ ] Implement closure and upvalue handling
- [ ] Implement coroutine create/resume/yield
- [ ] Implement to-be-closed variables (`<close>`)
- [ ] Implement error handling (pcall, xpcall, error)
- [ ] Implement garbage collector (incremental mode)
- [ ] Implement basic standard library (print, type, tostring, tonumber, assert, error, pcall, select)
- [ ] Implement string library (basic operations + pattern matching)
- [ ] Implement table library
- [ ] Implement math library
- [ ] **Milestone:** Can run simple Lua programs end-to-end

### Phase 3: Compliance (Weeks 19-28)

> **Goal:** Full Lua 5.4 compliance, pass official test suite

- [ ] Implement generational GC mode
- [ ] Implement io library
- [ ] Implement os library
- [ ] Implement debug library
- [ ] Implement package/require system (Lua and C module loading)
- [ ] Implement utf8 library
- [ ] Implement coroutine library (full: close, isyieldable)
- [ ] Implement `string.dump` / `load` with bytecode
- [ ] Implement `collectgarbage()` with all options
- [ ] Implement `warn()` system
- [ ] Run and pass official Lua 5.4 test suite
- [ ] Fix all compliance issues found by test suite
- [ ] Implement CLI (REPL, file execution, `-e`, `-l`, `-i` flags)
- [ ] **Milestone (MVP):** 100% Lua 5.4 test suite pass rate

### Phase 4: JIT Baseline (Weeks 29-38)

> **Goal:** Baseline JIT compiler with measurable speedup

- [ ] Implement executable memory management (W^X compliant)
- [ ] Implement Cranelift integration (function signature, module creation)
- [ ] Implement baseline JIT translator (bytecode → Cranelift IR, 1:1)
- [ ] Implement type guards for NaN-boxed values
- [ ] Implement fast paths for integer/float arithmetic
- [ ] Implement fast paths for table access (array part)
- [ ] Implement profiling counters (function call count, loop back-edges)
- [ ] Implement tier-up logic (interpreter → baseline JIT)
- [ ] Implement deoptimization (JIT → interpreter fallback)
- [ ] Implement GC safe points in JIT code
- [ ] Implement stack maps for GC root scanning
- [ ] Benchmark against PUC Lua: target ≥5x on numeric benchmarks
- [ ] **Milestone:** Baseline JIT working on x86_64 and aarch64

### Phase 5: JIT Optimization (Weeks 39-48)

> **Goal:** Optimizing JIT with advanced optimizations

- [ ] Implement type specialization based on profiling data
- [ ] Implement function inlining (small callees, hot call sites)
- [ ] Implement inline caching for table access (shape-based)
- [ ] Implement loop optimizations (LICM, strength reduction)
- [ ] Implement constant propagation through upvalues
- [ ] Implement dead code elimination
- [ ] Implement allocation sinking (delay/eliminate table allocations)
- [ ] Implement on-stack replacement (interpreter → JIT mid-function)
- [ ] Implement OSR for long-running loops
- [ ] Tune deoptimization heuristics (avoid deopt spirals)
- [ ] Benchmark against LuaJIT: target competitive on common benchmarks
- [ ] **Milestone:** Optimizing JIT achieving ≥10x PUC Lua on hot paths

### Phase 6: Polish & FFI (Weeks 49-56+)

> **Goal:** Production readiness, FFI, embedding API

- [ ] Implement FFI Phase 1 (libffi-based dynamic calls)
- [ ] Implement C declaration parser
- [ ] Implement FFI Phase 2 (JIT-inlined foreign calls)
- [ ] Implement clean Rust embedding API (`selune` crate)
- [ ] Implement C API compatibility layer (for existing C Lua libraries)
- [ ] Comprehensive benchmark suite (12+ benchmarks)
- [ ] Performance optimization pass (profile-guided)
- [ ] Documentation (embedding guide, internals, API reference)
- [ ] Fuzz testing campaign (grammar-based + coverage-guided)
- [ ] Security audit of `unsafe` code
- [ ] Cross-platform CI (Linux, macOS, Windows × x86_64, aarch64)
- [ ] **Milestone (v1.0):** Production-ready release

### Realistic Timeline

| Phase | Optimistic | Realistic | Pessimistic |
|---|---|---|---|
| Phase 1: Foundation | 6 weeks | 8 weeks | 12 weeks |
| Phase 2: Interpreter | 8 weeks | 10 weeks | 14 weeks |
| Phase 3: Compliance | 8 weeks | 10 weeks | 16 weeks |
| Phase 4: JIT Baseline | 8 weeks | 10 weeks | 14 weeks |
| Phase 5: JIT Optimize | 8 weeks | 10 weeks | 14 weeks |
| Phase 6: Polish & FFI | 8 weeks | 12 weeks | 16 weeks |
| **Total** | **46 weeks** | **60 weeks** | **86 weeks** |

---

## 16. Testing & Compliance

### 16.1 Test Pyramid

```
                 ┌───────────────┐
                 │   End-to-End  │  ← Official Lua 5.4 test suite
                 │    Tests      │     lua-Harness compliance tests
                 ├───────────────┤
                 │  Integration  │  ← Multi-component tests
                 │    Tests      │     (compiler + VM, GC + tables)
                 ├───────────────┤
                 │     Unit      │  ← Per-module tests
                 │    Tests      │     (lexer, compiler, VM, GC, etc.)
                 ├───────────────┤
                 │   Property    │  ← QuickCheck-style
                 │    Tests      │     (value roundtrips, GC invariants)
                 ├───────────────┤
                 │     Fuzz      │  ← AFL/libFuzzer harnesses
                 │    Tests      │     (parser, compiler, VM, GC)
                 └───────────────┘
```

### 16.2 Official Lua 5.4 Test Suite

- Source: https://www.lua.org/tests/
- Coverage: All language features, standard library, edge cases
- Target: **100% pass rate** (Phase 3 milestone)
- Known challenges:
  - Tests that depend on specific error message format
  - Tests that depend on garbage collection timing
  - Tests that check debug.getinfo for specific fields
  - Resolution: Exact PUC-compatible behavior where spec mandates it

### 16.3 lua-Harness

- Additional test suite with broader coverage
- Tests edge cases not covered by official suite
- Performance regression tests

### 16.4 Benchmark Suite

| # | Benchmark | Category | What it Tests |
|---|---|---|---|
| 1 | `nbody` | Numeric | Float arithmetic, array access |
| 2 | `spectral-norm` | Numeric | Float arithmetic, nested loops |
| 3 | `mandelbrot` | Numeric | Integer/float arithmetic, tight loops |
| 4 | `fasta` | String | String concatenation, I/O |
| 5 | `binary-trees` | GC | Allocation, tree traversal, GC pressure |
| 6 | `fannkuch-redux` | Integer | Integer arithmetic, permutations |
| 7 | `richards` | OOP | Table-based OOP, method dispatch |
| 8 | `deltablue` | OOP | Constraint solver, heavy metamethods |
| 9 | `havlak` | Graph | Graph algorithms, tables as maps |
| 10 | `json-parse` | Parsing | String processing, table construction |
| 11 | `coroutine-ring` | Coroutine | Coroutine create/resume/yield throughput |
| 12 | `table-sort` | Table | table.sort with various comparators |

### 16.5 Fuzz Testing

```
Fuzz Targets:
  1. Lexer — Random byte sequences → tokenize without panic
  2. Parser — Random token sequences → parse without panic
  3. Compiler — Valid Lua AST mutations → compile without panic
  4. VM — Random bytecode sequences → execute without UB
  5. GC — Random allocation/free patterns → no memory corruption
  6. String — Random string operations → consistent results
  7. Table — Random table operations → consistent results

Tools:
  - cargo-fuzz (libFuzzer-based)
  - AFL++ for structure-aware fuzzing
  - Grammar-based fuzzer (generate valid Lua programs)

Target: 100M+ iterations, zero panics, zero UB (Miri-verified)
```

### 16.6 Differential Testing

```
Compare Selune output against PUC Lua 5.4 for:
  - Same Lua program → same output (stdout)
  - Same errors → same error messages (where spec defines them)
  - Same math operations → same numeric results (IEEE 754)
  - Same string operations → same string results
  - Same table operations → same iteration order (where defined)

Tool: Custom harness that runs both interpreters and diffs output
```

---

## 17. Performance Targets

### 17.1 Quantitative Targets

| Metric | Target | Baseline (PUC Lua 5.4) | LuaJIT 2.1 Reference |
|---|---|---|---|
| **Interpreter throughput** | ≥ 1.5x PUC | 1.0x | ~5-8x |
| **Baseline JIT (Tier 1)** | ≥ 5x PUC | — | — |
| **Optimizing JIT (Tier 2)** | ≥ 10x PUC | — | ~10-30x |
| **JIT compilation latency** | < 10ms p99 | — | ~1-5ms |
| **GC pause time** | < 1ms p99 | ~1-5ms | ~0.5-2ms |
| **Memory overhead per value** | 8 bytes | 16 bytes (tagged union) | 8 bytes (NaN-boxed) |
| **Startup time** | < 5ms | ~1ms | ~2ms |
| **Function call overhead** | < 20ns | ~50ns | ~5-10ns |
| **Table lookup (cached)** | < 10ns | ~30ns | ~5ns |
| **String interning** | < 50ns | ~100ns | ~50ns |

### 17.2 Comparison Targets vs LuaJIT

| Benchmark | Target vs LuaJIT | Rationale |
|---|---|---|
| `nbody` | 70-100% | Heavy float arithmetic, Cranelift competitive |
| `spectral-norm` | 70-100% | Similar to nbody |
| `mandelbrot` | 60-90% | Integer math, LuaJIT excels here |
| `binary-trees` | 80-120% | GC-bound, generational GC advantage |
| `fannkuch-redux` | 60-90% | Integer compute, LuaJIT hand-tuned ASM |
| `richards` | 70-100% | OOP dispatch, inline caching helps |
| `coroutine-ring` | 50-80% | LuaJIT has very optimized coroutines |
| **Geometric mean** | **≥ 70%** | Competitive with LuaJIT overall |

### 17.3 Methodology

```
Benchmarking Methodology:
  1. Each benchmark run 10 times, report median
  2. Warm-up run discarded
  3. Measure wall-clock time (not CPU time)
  4. Pin to single core to avoid scheduling variance
  5. Disable frequency scaling (performance governor)
  6. Report geometric mean across all benchmarks
  7. CI runs benchmarks on every PR to detect regressions
  8. Compare against specific versions: PUC Lua 5.4.7, LuaJIT 2.1.ROLLING
```

---

## 18. Risk Analysis

### 18.1 Technical Risks

| # | Risk | Probability | Impact | Mitigation |
|---|---|---|---|---|
| **T1** | Cranelift code quality insufficient for targets | Low | High | Fallback to LLVM backend; contribute optimizations upstream |
| **T2** | NaN-boxing edge cases cause subtle bugs | Medium | High | Extensive property testing; differential testing vs PUC |
| **T3** | GC pauses exceed targets in generational mode | Medium | Medium | Tune generational thresholds; incremental fallback |
| **T4** | Deoptimization overhead negates JIT gains | Low | High | Careful guard placement; profile-guided guard elimination |
| **T5** | Shape system memory overhead too high | Low | Medium | Limit shape tree depth; periodic shape GC |
| **T6** | Coroutine yield-from-JIT too complex | Medium | Medium | Phase 1: don't JIT functions that yield; OSR in Phase 2 |
| **T7** | `unsafe` code introduces memory safety bugs | Medium | High | Minimize unsafe; Miri testing; dedicated audit |
| **T8** | W^X compliance breaks on new OS versions | Low | Medium | Abstraction layer; test on beta OS releases |
| **T9** | Pattern matching engine has exponential blowup | Low | Medium | Stack depth limit (like PUC); fuzz testing |
| **T10** | FFI C declaration parser incomplete | Medium | Low | Subset of C declarations; grow based on user needs |

### 18.2 Project Risks

| # | Risk | Probability | Impact | Mitigation |
|---|---|---|---|---|
| **P1** | Scope creep beyond Lua 5.4 spec | High | Medium | Strict non-goals; defer extensions to post-v1.0 |
| **P2** | Burnout from estimated 60+ week timeline | Medium | High | Phased milestones; MVP at Phase 3 is useful standalone |
| **P3** | Cranelift API breaking changes | Medium | Medium | Pin Cranelift version; update periodically |
| **P4** | Community expects LuaJIT compatibility | Low | Medium | Clear positioning as Lua 5.4 (not 5.1) from day one |

---

## 19. Success Criteria

### 19.1 MVP Definition (Phase 3 Complete)

The Minimum Viable Product is reached when:

- [ ] **Lua 5.4 Test Suite**: 100% pass rate on official Lua 5.4.7 test suite
- [ ] **Standard Library**: All Lua 5.4 standard library functions implemented
- [ ] **Interpreter Performance**: ≥ 1.5x PUC Lua 5.4 on benchmark geometric mean
- [ ] **Memory Safety**: Zero known memory safety issues; Miri-clean on test suite
- [ ] **CLI**: Functional REPL and script execution (`selune`, `selune script.lua`)
- [ ] **Platforms**: Passes tests on Linux x86_64, macOS aarch64 (minimum)
- [ ] **GC**: Both incremental and generational modes working correctly
- [ ] **Coroutines**: Full coroutine support including to-be-closed variables
- [ ] **Documentation**: Basic embedding guide and API documentation

### 19.2 v1.0 Definition (Phase 6 Complete)

Version 1.0 is reached when all MVP criteria plus:

- [ ] **JIT Performance**: ≥ 10x PUC Lua on optimizing JIT benchmarks
- [ ] **JIT Stability**: Zero JIT-related crashes in 100M fuzz iterations
- [ ] **FFI**: Working FFI for calling C functions from Lua
- [ ] **Embedding API**: Clean, documented Rust API for embedding Selune
- [ ] **Cross-Platform**: CI passes on Linux, macOS, Windows (x86_64 + aarch64)
- [ ] **C API**: Compatibility layer for loading existing C Lua libraries
- [ ] **Benchmarks**: Published benchmark results vs PUC Lua and LuaJIT
- [ ] **Security**: Audit of all `unsafe` blocks completed
- [ ] **Documentation**: Complete internals documentation, API reference, embedding guide
- [ ] **Performance**: Geometric mean ≥ 70% of LuaJIT across benchmark suite

---

## 20. References

### Specifications
1. [Lua 5.4 Reference Manual](https://www.lua.org/manual/5.4/)
2. [Lua 5.4 Source Code](https://www.lua.org/source/5.4/)
3. [Lua 5.4 Test Suite](https://www.lua.org/tests/)

### Papers & Design Documents
4. [The Implementation of Lua 5.0 — Ierusalimschy et al.](https://www.lua.org/doc/jucs05.pdf)
5. [A No-Frills Introduction to Lua 5.1 VM Instructions](https://www.lua.org/source/5.1/lopcodes.h.html)
6. [LuaJIT 2.0 Internals — Mike Pall](https://web.archive.org/web/2021/http://wiki.luajit.org/Internals)
7. [Trace-based JIT Compilation — Gal et al.](https://dl.acm.org/doi/10.1145/1542476.1542528)
8. [Cranelift Design — Bytecode Alliance](https://cranelift.dev/)

### Related Projects
9. [PUC Lua 5.4](https://github.com/lua/lua)
10. [LuaJIT](https://github.com/LuaJIT/LuaJIT)
11. [Piccolo (Rust Lua)](https://github.com/kyren/piccolo)
12. [mlua (Rust Lua Bindings)](https://github.com/mlua-rs/mlua)
13. [Hematita (Rust Lua)](https://github.com/hematita-lang/hematita)

### Runtime Implementation References
14. [V8 JavaScript Engine — Hidden Classes / Shapes](https://v8.dev/blog/fast-properties)
15. [JavaScriptCore — B3 Compiler](https://webkit.org/blog/5852/introducing-the-b3-jit-compiler/)
16. [SpiderMonkey — IonMonkey JIT](https://firefox-source-docs.mozilla.org/js/index.html)
17. [Ruby YJIT — Method-based JIT in Rust](https://shopify.engineering/yjit-just-in-time-compiler-cruby)
18. [Swiss Tables — Abseil](https://abseil.io/about/design/swisstables)

### GC References
19. [Incremental GC in Lua 5.4 — Roberto Ierusalimschy](https://www.lua.org/wshop18/Ierusalimschy.pdf)
20. [Generational GC for Lua — Roberto Ierusalimschy](https://www.inf.puc-rio.br/~roberto/docs/ry08-06.pdf)
21. [Tri-Color Marking — Dijkstra et al.](https://dl.acm.org/doi/10.1145/359642.359655)

### Cranelift
22. [Cranelift Documentation](https://cranelift.dev/docs/)
23. [Cranelift GitHub](https://github.com/bytecodealliance/wasmtime/tree/main/cranelift)
24. [Cranelift IR Reference](https://cranelift.readthedocs.io/en/latest/ir.html)
25. [Using Cranelift for JIT — Wasmtime Examples](https://docs.wasmtime.dev/)

### NaN-Boxing
26. [NaN-Boxing — Sean Barrett](https://sean.cm/a/nan-boxing)
27. [Value Representation in JavaScript Engines](https://webkit.org/blog/7846/type-confusion-in-the-jsc-jit/)
28. [Mozilla SpiderMonkey NaN-Boxing](https://phabricator.services.mozilla.com/D26677)

---

> **Note:** This PRD is a living document. As implementation progresses, specific sections will be refined based on learnings from actual development. Phase boundaries and timeline estimates are approximations and should be re-evaluated at each phase gate.
