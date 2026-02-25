# Selune

A modern Lua 5.4 JIT compiler written in Rust.

## Overview

Selune is a high-performance, fully-compatible implementation of the Lua 5.4
programming language. It passes **all 28** applicable official PUC-Rio Lua 5.4.7 test
suite files (100%), making it the most conformant pure-Rust Lua 5.4 implementation
available. Built from scratch with no C dependencies.

## Official Test Suite Compliance

Selune is validated against the [official Lua 5.4.7 test suite](https://www.lua.org/tests/) from PUC-Rio:

| Test File | Status | | Test File | Status |
|-----------|--------|-|-----------|--------|
| attrib | PASS | | literals | PASS |
| big | PASS | | locals | PASS |
| bitwise | PASS | | math | PASS |
| bwcoercion | PASS | | nextvar | PASS |
| calls | PASS | | pm | PASS |
| closure | PASS | | sort | PASS |
| code | PASS | | strings | PASS |
| constructs | PASS | | tpack | PASS |
| coroutine | PASS | | tracegc | PASS |
| cstack | PASS | | utf8 | PASS |
| db | PASS | | vararg | PASS |
| errors | PASS | | verybig | PASS |
| events | PASS | | files | PASS |
| gc | PASS | | goto | PASS |

**4 tests excluded** (not applicable): `api` (C API only), `main` (CLI-specific, skipped by `_port`), `heavy` (memory stress), `gengc` (generational GC, planned)

### Test Mode

The test suite runs in Lua's standard **portable mode** via `run_test.lua`, which sets:

| Global | Value | Purpose |
|--------|-------|---------|
| `_port` | `true` | Skip platform-specific / OS-dependent tests |
| `_soft` | `true` | Use smaller limits (fewer iterations, smaller tables) |
| `_nomsg` | `true` | Suppress "not testing X" messages |
| `T` | `nil` | Disable internal C API tests (not applicable) |

This is the same configuration used by the official test suite for portable Lua implementations. See [`tests/lua54-tests/ORIGIN.md`](tests/lua54-tests/ORIGIN.md) for full provenance details.

## Features

### Phase 1 — Compiler
- NaN-boxed 8-byte TValue (all Lua values packed into a single 64-bit word)
- Single-pass compiler with no intermediate AST (tokens directly to bytecode)
- All 83 Lua 5.4 opcodes across 5 instruction formats (iABC, iABx, iAsBx, iAx, isJ)
- String interning with small-string optimization (SSO at 40 bytes)
- Complete lexer supporting all Lua 5.4 tokens, numbers, and string literals
- ExprDesc-based code generation with 15+ expression variants
- Constant folding for unary operations on literals
- Upvalue resolution across nested function scopes
- Bytecode disassembler for debugging and inspection

### Phase 2 — Virtual Machine
- Stack-based bytecode VM executing all 83 opcodes
- Full arithmetic: `+`, `-`, `*`, `/`, `//`, `%`, `^` with proper Lua 5.4 integer/float semantics
- Bitwise operations: `&`, `|`, `~`, `<<`, `>>`, `~` (unary)
- Comparisons: `==`, `<`, `<=`, `>`, `>=` across types (int, float, string)
- Control flow: `if`/`elseif`/`else`, `while`, `repeat...until`, numeric `for`, generic `for...in`, `break`, `goto`/labels
- Tables: construction (array, hash, mixed, nested), field/index access, dynamic keys, `#` length
- Functions: calls with arguments and returns, multiple return values, variadic functions (`...`)
- Closures: upvalue capture, mutation, shared upvalues, nested closures, closure escape
- Tail call optimization
- Metamethods: full dispatch for all 30+ metamethods including arithmetic, comparison, index, newindex, call, concat, tostring, len, close, pairs, and metatable protection
- Error handling: `error()`, `pcall()`, `xpcall()` with proper error propagation
- Generic for loops with `pairs()`, `ipairs()`, `next()` iterator protocol
- To-be-closed variables (`<close>` attribute) with `__close` metamethod
- Coroutines: `create`, `resume`, `yield`, `wrap`, `close`, `status`, `isyieldable`, `running` with yield across pcall/xpcall boundaries
- Mark-sweep garbage collection with weak tables (`__mode`), finalizers (`__gc`), and `collectgarbage()` API
- Arena-based GC heap with typed indices (`GcIdx<T>`) supporting tables, closures, upvalues, boxed integers, strings, and userdata
- Open/closed upvalue management with proper scope closing

### Phase 3 — Full Lua 5.4 Compliance
- `load`, `dofile`, `loadfile` with string and function readers
- `require` with `package.loaded`, `package.preload`, `package.path`, `package.searchers`
- Complete string library: `format`, `pack`/`unpack`/`packsize`, `find`, `match`, `gmatch`, `gsub`, `rep`, `reverse`, `sub`, `byte`, `char`, `upper`, `lower`, `len`, `dump`
- Complete table library: `insert`, `remove`, `sort`, `concat`, `move`, `pack`, `unpack` (all with metamethod support)
- Complete math library: 25+ functions including `random`/`randomseed`, `tointeger`, `type`, `maxinteger`, `mininteger`
- IO library: `open`, `close`, `read`, `write`, `lines`, `input`, `output`, `tmpfile`, `type`, `flush`, `popen` + file methods
- OS library: `clock`, `time`, `difftime`, `date`, `execute`, `getenv`, `remove`, `rename`, `tmpname`, `exit`, `setlocale`
- Debug library: `getinfo`, `getlocal`, `setlocal`, `getupvalue`, `setupvalue`, `upvalueid`, `upvaluejoin`, `sethook`, `gethook`, `traceback`, `getmetatable`, `setmetatable`, `getuservalue`, `setuservalue`
- UTF-8 library: `char`, `codes`, `codepoint`, `len`, `offset`, `charpattern`
- Userdata with per-instance metatables
- Binary chunk loading (Lua 5.4 bytecode format)
- Syntax error messages with "near \<token\>" context
- Resource limits: 200 local variables, 255 upvalues, 200 nesting levels, 249 registers
- `_VERSION`, `_G`, `warn()`, `select()`, `rawget`, `rawset`, `rawequal`, `rawlen`

### Phase 4 — JIT Compiler (In Progress)
- Method-based JIT compilation via [Cranelift](https://cranelift.dev/) code generator
- Automatic tier-up: functions compiled to native code after 1000 calls
- 55+ bytecode opcodes translated to native code
- Integer and float type specialization with NaN-box type guards
- Register allocation with slot caching and deferred stores
- Loop-carried type propagation via Cranelift block parameters
- Runtime helpers for function calls, upvalues, table access, and string operations
- Side-exit to interpreter for unsupported patterns (metamethods, coroutines)
- 7-11x speedup over interpreter on numeric-heavy code

## Project Structure

```
selune/
├── crates/
│   ├── selune-core/     # Core types: TValue (NaN-boxed), TString, StringInterner, GC heap
│   ├── selune-compiler/ # Lexer, parser, bytecode compiler
│   ├── selune-vm/       # Stack-based virtual machine
│   ├── selune-jit/      # JIT compiler via Cranelift (55+ opcodes, int+float specialization)
│   ├── selune-stdlib/   # Standard library (math, string, table, io, os, debug, utf8, coroutine, package)
│   ├── selune-ffi/      # C API compatibility layer (planned)
│   └── selune/          # CLI binary
├── tests/
│   ├── lua_samples/     # Sample Lua programs for testing
│   └── lua54-tests/     # Official Lua 5.4.7 test suite
└── docs/                # Architecture and design documentation
```

## Getting Started

```sh
# Build all crates
cargo build

# Run a Lua file
cargo run -- path/to/script.lua

# Run the full Rust test suite
cargo test --workspace

# Run official Lua 5.4.7 test suite (all 28 files)
cargo build --release
./scripts/run_puc_547.sh

# Run a single official test file
./target/release/selune tests/lua54-tests/run_test.lua tests/lua54-tests/math.lua
```

## Architecture

Lua source is processed through a multi-stage pipeline:

1. **Lexer** — byte-by-byte scanning producing a stream of tokens
2. **Compiler** — single-pass recursive descent with Pratt parsing (precedence climbing) for expressions
3. **Proto** — bytecode output with constants, nested prototypes, and debug info
4. **VM** — stack-based interpreter dispatching opcodes against a NaN-boxed value stack and arena-allocated GC heap

Key design details are documented in [docs/architecture.md](docs/architecture.md).

## Performance

Benchmarked on arm64 Apple M3, comparing against PUC Lua 5.4.8 and LuaJIT 2.1:

### Interpreter Benchmarks

These benchmarks measure interpreter throughput (each function called once, below JIT threshold):

| Benchmark | Selune/PUC | Category |
|-----------|-----------|----------|
| binary_trees | 1.19x | GC/allocation |
| table_hash | 1.27x | Hash table ops |
| gc_pressure | 1.37x | GC stress |
| spectral_norm | 1.38x | Float math |
| string_concat | 1.61x | String ops |
| closures | 1.68x | Function/upvalue |
| ackermann | 2.31x | Deep recursion |
| mandelbrot | 2.37x | Float math |
| table_array | 2.50x | Array ops |
| arithmetic | 3.51x | Integer math |
| fibonacci | 3.74x | Recursion |
| method_calls | 6.23x | OOP dispatch |

**Interpreter geometric mean: 2.51x PUC Lua** (across 16 benchmarks). Lower is better; <1.0x means Selune is faster.

### JIT Performance

When the JIT activates (functions called 1000+ times), Selune generates native code via Cranelift that is significantly faster than PUC Lua:

| Benchmark | Selune JIT (s) | PUC Lua (s) | vs PUC Lua |
|-----------|---------------|-------------|------------|
| jit_sum_loop | 2.83 | 4.32 | **1.5x faster** |
| jit_heavy_arith | 0.61 | 1.99 | **3.3x faster** |
| jit_float_arith | 0.50 | 1.58 | **3.2x faster** |

The JIT currently supports 55+ opcodes including integer/float arithmetic, comparisons, control flow, loops, function calls, upvalues, and table access with integer and float type specialization.

To reproduce: `./benchmarks/run_jit_benchmarks.sh`

See [docs/PERFORMANCE.md](docs/PERFORMANCE.md) for interpreter benchmark results. To regenerate: `./benchmarks/run_benchmarks.sh`

## Roadmap

| Phase | Scope | Status |
|-------|-------|--------|
| 1 | Lexer, compiler, bytecode, core types | Done |
| 2 | Stack-based VM, metamethods, error handling, coroutines, GC, stdlib | Done |
| 3 | Full Lua 5.4 compliance (28/28 official tests) | Done |
| 3.5 | Interpreter performance optimization (3.27x → 2.61x vs PUC) | Done |
| 4 | JIT compilation (Cranelift backend) | In Progress |
| 5 | C API / FFI compatibility | Planned |

## Testing

1,570+ tests across the workspace:

- **1,122** VM end-to-end tests (4 ignored for known gaps)
- **140** compiler unit tests
- **127** JIT compiler tests
- **95** compiler end-to-end integration tests
- **48** core type tests (TValue roundtrips, string interning, property tests)
- **36** standard library tests
- **2** integration tests (disassembler, debug)
- **28/28** official Lua 5.4.7 test suite files passing (100%)

## License

MIT License. See [LICENSE](LICENSE) for details.
