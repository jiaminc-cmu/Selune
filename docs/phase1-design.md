# Phase 1 Design Decisions

## Scope

Phase 1 implements the foundation: lexer, compiler, and bytecode generation.
The milestone is compiling any valid Lua 5.4 source to a `Proto` bytecode structure.

## Key Trade-offs

### Single-Pass vs AST-Based Compilation

**Decision**: Single-pass (no AST).

**Rationale**: Matches PUC Lua's approach. Simpler, faster, lower memory usage.
The ExprDesc system provides the necessary flexibility for code generation without
materializing an entire AST. The downside is that optimizations requiring global
analysis are deferred to a later pass or the JIT.

### NaN-Boxing vs Tagged Union

**Decision**: NaN-boxing (8 bytes per value).

**Rationale**: Cache-friendly (half the size of a 16-byte tagged union), no
branch mispredictions on type checks. The 47-bit integer range (-2^46 to 2^46-1)
covers most practical Lua integer usage. Values outside this range will use GC-boxed
integers (Phase 2).

### SSO Threshold at 40 Bytes

**Decision**: Short String Optimization for strings <= 40 bytes.

**Rationale**: Matches PUC Lua's LUAI_MAXSHORTLEN default. Most identifiers and
short string literals fit within 40 bytes. SSO avoids heap allocation for these
common cases.

### ExprDesc with 15 Variants

**Decision**: Rich ExprDesc enum instead of always discharging to registers.

**Rationale**: Enables constant folding, deferred register allocation, and
specialized opcodes (AddI, AddK, etc.). The Global variant was added specifically
to handle `_ENV` table access correctly for both reads and writes.

### Concat Chain Optimization

**Decision**: Collect all concat operands into consecutive registers, emit single
Concat instruction.

**Rationale**: Lua 5.4's Concat instruction operates on a range of consecutive
registers. Pairwise concat would produce incorrect code when operands aren't
naturally consecutive. The compiler now flattens `a .. b .. c` into three
consecutive registers + one Concat.

## Known Limitations (Phase 1)

1. **No runtime**: Proto structures are generated but cannot be executed
2. **Integer overflow**: `TValue::from_integer()` panics for values outside 47-bit range
3. **No GC boxing**: Large integers and other GC types deferred to Phase 2
4. **Limited constant folding**: Only unary operations on literals
5. **No optimization passes**: All optimizations deferred to JIT (Phase 3)

## Verification

Phase 1 is verified by:
- 282 total tests (140 unit + 94 E2E + 48 core)
- All Lua 5.4 syntax features compile successfully
- 10 sample Lua programs from disk compile without errors
- Property tests ensure TValue and StringInterner invariants
- Fuzz targets ensure no panics on arbitrary input
