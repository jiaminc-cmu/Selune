# Selune

A modern Lua 5.4 JIT compiler written in Rust.

## Overview

Selune aims to be a high-performance, fully-compatible implementation of the Lua 5.4
programming language. It prioritizes spec compliance, execution speed rivaling existing
JIT implementations, and cross-platform support (x86_64 and ARM64).

## Features (Phase 1)

- NaN-boxed 8-byte TValue (all Lua values packed into a single 64-bit word)
- Single-pass compiler with no intermediate AST (tokens directly to bytecode)
- All 83 Lua 5.4 opcodes across 5 instruction formats (iABC, iABx, iAsBx, iAx, isJ)
- String interning with small-string optimization (SSO at 40 bytes)
- Complete lexer supporting all Lua 5.4 tokens, numbers, and string literals
- ExprDesc-based code generation with 15 expression variants
- Constant folding for unary operations on literals
- Upvalue resolution across nested function scopes
- Bytecode disassembler for debugging and inspection

## Project Structure

```
selune/
├── crates/
│   ├── selune-core/     # Core types: TValue (NaN-boxed), TString, StringInterner
│   ├── selune-compiler/ # Lexer, parser, bytecode compiler
│   ├── selune-vm/       # Stack-based virtual machine (Phase 2)
│   ├── selune-jit/      # JIT compilation via Cranelift (Phase 3)
│   ├── selune-stdlib/   # Standard library implementation (Phase 4)
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

Lua source is processed through a three-stage pipeline:

1. **Lexer** -- byte-by-byte scanning producing a stream of tokens
2. **Compiler** -- single-pass recursive descent with precedence climbing for expressions
3. **Proto** -- bytecode output with constants, nested prototypes, and debug info

Key design details are documented in [docs/architecture.md](docs/architecture.md).

## Roadmap

| Phase | Scope | Status |
|-------|-------|--------|
| 1 | Lexer, compiler, bytecode, core types | Done |
| 2 | Stack-based VM execution | Planned |
| 3 | JIT compilation (Cranelift backend) | Planned |
| 4 | Standard library | Planned |
| 5 | C API / FFI compatibility | Planned |

## Testing

282 tests across the workspace:

- **140** compiler unit tests
- **94** end-to-end integration tests covering all implemented language features
- **48** core type tests (TValue roundtrips, string interning, property tests)
- Fuzz targets for lexer and compiler (no panics on arbitrary input)
- Criterion benchmarks for lexer, compiler, and TValue operations

## License

TBD
