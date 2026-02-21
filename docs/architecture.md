# Selune Architecture

## Overview

Selune is a Lua 5.4 JIT compiler written in Rust. It aims to be a high-performance,
fully-compatible implementation of the Lua programming language.

## Crate Structure

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

## Data Flow

```
Lua Source Code
      │
      ▼
┌─────────────┐
│    Lexer     │  Byte-by-byte scanning, token generation
│  (token.rs,  │  All Lua 5.4 tokens, numbers, strings, long strings
│   lexer.rs)  │  Pull-based: advance()/current()
└──────┬──────┘
       │ Stream of SpannedTokens
       ▼
┌─────────────┐
│  Compiler   │  Single-pass recursive descent
│  (compiler/ │  Precedence climbing for expressions
│   mod.rs)   │  ExprDesc-based code generation
└──────┬──────┘
       │ Proto (function prototype)
       ▼
┌─────────────┐
│    Proto     │  Bytecode instructions (83 opcodes)
│  (proto.rs)  │  Constants, nested protos, upvalue descriptors
│              │  Debug info (line numbers, local variable names)
└─────────────┘
```

## Key Design Decisions

### NaN-Boxing (selune-core/value.rs)

All Lua values are represented in 8 bytes using IEEE 754 NaN-boxing:

- **Layout**: QNAN prefix (0x7FF8) + 3 tag bits (47-49) + 47-bit payload
- **Tags**: Nil(001), Bool(010), SmallInt(011), GC(100), LightUserdata(101)
- **Floats**: Stored as raw f64 bits; NaN inputs canonicalized to QNAN
- **Integers**: 47-bit signed integers stored inline (range: -2^46 to 2^46-1)
- **GC pointers**: Tagged pointer in 47-bit payload (Phase 2)

### String Interning (selune-core/string.rs)

- **SSO**: Strings <= 40 bytes stored inline (no heap allocation)
- **Short strings**: Interned (deduplicated) via hash map lookup
- **Long strings**: Not interned; each instance gets a unique StringId
- **Hash**: PUC Lua-compatible hash function (luaS_hash algorithm)
- **Handles**: `StringId(u32)` — opaque index into the interner

### Single-Pass Compilation (selune-compiler/compiler/)

The compiler is a single-pass recursive descent compiler (no AST):

- **ExprDesc**: 15-variant enum representing expression states before
  register assignment (Nil, True, False, Integer, Float, Str, Register,
  Upvalue, Constant, Indexed, Relocatable, Jump, Call, Vararg, Global)
- **Register allocation**: Linear allocator with scope-based freeing
- **Backpatching**: Jump targets resolved when blocks/labels complete
- **Constant folding**: Unary operations on literals folded at compile time
- **Upvalue resolution**: Walk up FuncState stack to find captured variables

### Instruction Encoding (selune-compiler/opcode.rs)

All 83 Lua 5.4 opcodes in 5 instruction formats:

- **iABC**: 7-bit opcode, 1-bit k, 8-bit A, 8-bit B, 8-bit C
- **iABx**: 7-bit opcode, 1-bit k, 8-bit A, 16-bit Bx (unsigned)
- **iAsBx**: Same layout as iABx but Bx is signed (offset by MAX_BX/2)
- **iAx**: 7-bit opcode, 1-bit k, 24-bit Ax
- **isJ**: 7-bit opcode, 1-bit k, 24-bit sJ (signed jump offset)

## Testing Strategy

- **Unit tests**: Each module has comprehensive unit tests (140+ in compiler)
- **Property tests**: TValue roundtrip properties via proptest
- **E2E tests**: 94 integration tests covering all language features
- **Lua samples**: 10 sample programs compiled from disk
- **Fuzz targets**: Lexer and compiler fuzz targets (no panics on any input)
- **Benchmarks**: Criterion benchmarks for lexer, compiler, and TValue operations
