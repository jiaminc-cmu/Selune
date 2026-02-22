# Selune

A modern Lua 5.4 JIT compiler written in Rust.

## Overview

Selune aims to be a high-performance, fully-compatible implementation of the Lua 5.4
programming language. It prioritizes spec compliance, execution speed rivaling existing
JIT implementations, and cross-platform support (x86_64 and ARM64).

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
- Stack-based bytecode VM executing 80+ opcodes
- Full arithmetic: `+`, `-`, `*`, `/`, `//`, `%`, `^` with proper Lua 5.4 integer/float semantics
- Bitwise operations: `&`, `|`, `~`, `<<`, `>>`, `~` (unary)
- Comparisons: `==`, `<`, `<=`, `>`, `>=` across types (int, float, string)
- Control flow: `if`/`elseif`/`else`, `while`, `repeat...until`, numeric `for`, generic `for...in`, `break`, `goto`/labels
- Tables: construction (array, hash, mixed, nested), field/index access, dynamic keys, `#` length
- Functions: calls with arguments and returns, multiple return values, variadic functions (`...`)
- Closures: upvalue capture, mutation, shared upvalues, nested closures, closure escape
- Tail call optimization with infinite recursion detection
- Metamethods: full dispatch for arithmetic, comparison, index, newindex, call, concat, tostring, len, close, and metatable protection
- Error handling: `error()`, `pcall()`, `xpcall()` with proper error propagation
- Generic for loops with `pairs()`, `ipairs()`, `next()` iterator protocol
- To-be-closed variables (`<close>` attribute) with `__close` metamethod
- Coroutines: `create`, `resume`, `yield`, `wrap`, `close`, `status`, `isyieldable` with yield across pcall/xpcall boundaries
- Mark-sweep garbage collection with `collectgarbage()` API
- Standard library: math (25+ functions), string (15 functions + pattern matching), table (7 functions including sort with Lua comparator)
- Arena-based GC heap with typed indices (`GcIdx<T>`) supporting tables, closures, upvalues, boxed integers, and strings
- Open/closed upvalue management with proper scope closing
- Built-in native functions: `print`, `type`, `tostring`, `tonumber`, `assert`, `select`, `rawget`, `rawset`, `rawequal`, `rawlen`, `setmetatable`, `getmetatable`, `error`, `pcall`, `xpcall`, `pairs`, `ipairs`, `next`, `unpack`

## Project Structure

```
selune/
├── crates/
│   ├── selune-core/     # Core types: TValue (NaN-boxed), TString, StringInterner, GC heap
│   ├── selune-compiler/ # Lexer, parser, bytecode compiler
│   ├── selune-vm/       # Stack-based virtual machine
│   ├── selune-jit/      # JIT compilation via Cranelift (Phase 3)
│   ├── selune-stdlib/   # Standard library (math, string, table)
│   ├── selune-ffi/      # C API compatibility layer (Phase 5)
│   └── selune/          # CLI binary and REPL
├── fuzz/                # Fuzz testing targets
├── tests/
│   └── lua_samples/     # Sample Lua programs for testing
└── docs/                # Architecture and design documentation
```

## Getting Started

```sh
# Build all crates
cargo build

# Run the full test suite
cargo test --workspace

# Run benchmarks
cargo bench
```

## Architecture

Lua source is processed through a multi-stage pipeline:

1. **Lexer** — byte-by-byte scanning producing a stream of tokens
2. **Compiler** — single-pass recursive descent with precedence climbing for expressions
3. **Proto** — bytecode output with constants, nested prototypes, and debug info
4. **VM** — stack-based interpreter dispatching opcodes against a NaN-boxed value stack and arena-allocated GC heap

Key design details are documented in [docs/architecture.md](docs/architecture.md).

## Roadmap

| Phase | Scope | Status |
|-------|-------|--------|
| 1 | Lexer, compiler, bytecode, core types | Done |
| 2 | Stack-based VM, metamethods, error handling, coroutines, GC, stdlib | Done |
| 3 | Full Lua 5.4 compliance, test suite | Planned |
| 4 | JIT compilation (Cranelift backend) | Planned |
| 5 | C API / FFI compatibility | Planned |

### Phase 2 — Known Limitations
- No `require`, `dofile`, `loadfile`, `load` (dynamic code loading)
- No IO or OS library
- No `string.format` (printf-style formatting)
- No weak tables (`__mode`)
- No `__gc` finalizer metamethod
- String type does not have a shared metatable (`("hello"):upper()` syntax not supported)

## Testing

1,302 tests across the workspace:

- **981** VM end-to-end tests (2 ignored for known gaps)
- **140** compiler unit tests
- **94** compiler end-to-end integration tests
- **48** core type tests (TValue roundtrips, string interning, property tests)
- **36** standard library tests
- **1** disassembler integration test
- Fuzz targets for lexer and compiler (no panics on arbitrary input)
- Criterion benchmarks for lexer, compiler, and TValue operations

## License

TBD
