# Selune — Lua 5.4 JIT Compiler in Rust

## Your Task

You are implementing the **baseline JIT compiler** for Selune using Cranelift. The interpreter is complete (28/28 official tests passing, 2.61x PUC Lua performance). Your job is to add JIT compilation to the `selune-jit` crate so that hot functions are compiled to native code.

## THE #1 RULE

**Work incrementally.** Get the simplest possible JIT working first (compile a function that does `return 1`), then expand opcode coverage one at a time. Every step must pass the full test suite.

Your workflow:
1. Implement one piece of JIT infrastructure or one opcode group
2. Write tests that verify JIT-compiled code matches interpreter output
3. Build and run `cargo test --workspace` — must pass
4. Run official test suite to check for regressions
5. Tell the user what you implemented and what's next
6. STOP. Wait for direction.

**Do NOT:**
- Try to implement all opcodes at once
- Skip testing after each change
- Break the interpreter (JIT must be opt-in, interpreter is the fallback)
- Introduce `unsafe` without clear justification

## How to Run Tests

```bash
# ALWAYS set PATH first
export PATH="$HOME/.rustup/toolchains/stable-aarch64-apple-darwin/bin:$PATH"

# Build (do this after every code change)
cargo build --release

# Run the full Rust test suite
cargo test --workspace

# Run ONE official test file
./target/release/selune tests/lua54-tests/run_test.lua tests/lua54-tests/<name>.lua

# Run all 28 official test files
for f in big verybig code bwcoercion bitwise constructs calls events literals math pm sort strings tpack tracegc utf8 closure nextvar errors locals files attrib goto vararg coroutine gc cstack db; do
  ./target/release/selune tests/lua54-tests/run_test.lua tests/lua54-tests/$f.lua 2>&1 && echo "PASS: $f" || echo "FAIL: $f"
done

# Run benchmarks (requires PUC Lua and LuaJIT installed)
./benchmarks/run_benchmarks.sh
```

## Current Status

### Interpreter (complete)
- **28/28** official Lua 5.4.7 test files passing
- **1,443** workspace tests, 0 failures, 4 ignored
- **2.61x** geometric mean vs PUC Lua (16 benchmarks)
- 11 skipped sections across 6 test files (~85-90% true compliance)

### JIT (not started)
- `selune-jit` crate exists but is empty (1-line docstring)
- No Cranelift dependencies in workspace yet
- No profiling counters, no tier-up logic, no executable memory management

## JIT Architecture Plan

### Method-based JIT with Cranelift
- **Compilation unit:** Whole function (matches Cranelift's function-at-a-time model)
- **Strategy:** 1:1 bytecode → Cranelift IR translation (baseline)
- **Tier-up:** Per-function call counter in interpreter → compile when hot
- **Deopt:** Side exit → reconstruct interpreter frame → resume in interpreter
- **GC integration:** Poll flag at safe points (function entry, loop back-edges)

### Native function signature
```
fn(state: *mut VmState, base: *mut TValue, nargs: u32) -> u32
```

### Key Cranelift crates needed
- `cranelift-codegen` — IR and code generation
- `cranelift-frontend` — SSA construction helper
- `cranelift-module` — function definition/linking
- `cranelift-jit` — in-process JIT compilation

## Project Structure

```
crates/selune-core/src/      — Values (value.rs), GC (gc.rs), tables, strings
crates/selune-compiler/src/  — Lexer (lexer.rs), compiler (compiler/mod.rs, expr.rs, scope.rs)
crates/selune-vm/src/        — VM (vm.rs), dispatch (dispatch.rs), arithmetic, metamethods
crates/selune-jit/src/       — JIT compiler (EMPTY — this is where you work)
crates/selune-stdlib/src/    — math.rs, string_lib.rs, table_lib.rs, io_lib.rs, os_lib.rs, debug_lib.rs, utf8_lib.rs, package_lib.rs
crates/selune/src/           — CLI (main.rs)
```

## Key Architecture (Interpreter)

Understanding these is critical for JIT — JIT code must produce identical semantics.

1. **NaN-boxing:** 8-byte TValue, QNAN prefix, 3 tag bits, 47-bit payload. Floats stored as-is. Integers >47 bits are GC-boxed.
2. **Arena-based GC:** `Vec<Option<T>>` per object type with free lists, typed `GcIdx<T>(u32, PhantomData)`
3. **Dispatch:** `match op` in a flat loop with local `pc` variable. Lua-to-Lua calls are partially flattened.
4. **Inline fast paths:** Add/Sub/Mul/Div/Mod/IDiv have inline integer+float fast paths in dispatch. Comparisons (Lt/Le/Eq/LtI/LeI/GtI/GeI/EqI) also inline.
5. **Table access:** GetI/SetI/GetField/SetField skip metamethod chain when table has no metatable. Self_ does raw lookup + one-level __index table check.
6. **Coroutines:** State saved/restored via `std::mem::swap`. Open upvalues remapped on yield.
7. **Proto storage:** `vm.protos: Vec<Proto>` with flat child indices. Closure opcode uses pre-computed `child_flat_indices`.
8. **CallInfo:** ~80 bytes per frame. Boolean flags packed into u8. TBC slots use `Option<Vec>`.

## Key Patterns for JIT

- **Integer arithmetic overflow:** Results may exceed 47-bit small int range → must call `from_full_integer(gc)` which may GC-box
- **Metamethod fallback:** Every arithmetic/comparison/table op has a slow path that calls metamethods. JIT must emit guards + side exits.
- **ForLoop:** Count-based integer iteration (no per-iteration overflow check). Float loops use direct comparison.
- **Upvalue access:** Open upvalues point to stack slots. Closed upvalues are heap-allocated. JIT must handle both.
- **GC interaction:** Any allocation (string concat, table creation, boxed int) can trigger GC. JIT code must have stack maps at allocation sites.

## Environment

- macOS ARM64 (Apple M3)
- Rust toolchain at ~/.rustup/toolchains/stable-aarch64-apple-darwin/bin
- Always prefix cargo commands with the PATH export above

## Reference

- Lua 5.4 manual: https://www.lua.org/manual/5.4/
- Cranelift docs: https://cranelift.dev/
- Issue #5: Phase 4 JIT task checklist
- Issue #48: Interpreter performance roadmap (completed optimizations)
- docs/PERFORMANCE.md: Current benchmark results
