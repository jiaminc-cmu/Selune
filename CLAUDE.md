# Selune — Lua 5.4 Compiler/VM in Rust

## Your Task

You are fixing the Selune Lua 5.4 implementation to pass the **official Lua 5.4.7 test suite**. The compiler, VM, and most standard libraries already work. You are fixing edge cases and filling gaps.

## THE #1 RULE

**Work on exactly ONE test file at a time.** Do not move to the next file until the current one passes. This is non-negotiable.

Your workflow for each file:
1. Run the test file
2. Find the first failure
3. Fix it (minimal change)
4. Rebuild and re-run the SAME test file
5. If it still fails, go to step 2
6. When it passes, run `cargo test --workspace` to check for regressions
7. Tell the user the file passes and what you fixed
8. STOP. Wait for the user to tell you which file to work on next.

**Do NOT:**
- Work on multiple test files at once
- "Fix" things speculatively for other test files
- Report a test as passing without actually running it and seeing `PASS` in the output
- Move to the next file without the user telling you to

## How to Run Tests

```bash
# ALWAYS set PATH first
export PATH="$HOME/.rustup/toolchains/stable-aarch64-apple-darwin/bin:$PATH"

# Build (do this after every code change)
cargo build --release

# Run ONE test file
./target/release/selune tests/lua54-tests/run_test.lua tests/lua54-tests/<name>.lua

# Output will be either:
#   PASS: tests/lua54-tests/<name>.lua
# or:
#   FAIL: tests/lua54-tests/<name>.lua
#     <error message>
#   (exits with code 1)

# Check for regressions (run after a test file passes)
cargo test --workspace
```

## Current Status

**PASSING (28/28):** big, verybig, code, bwcoercion, bitwise, constructs, calls, events, literals, math, pm, sort, strings, tpack, tracegc, utf8, closure, nextvar, errors, locals, files, attrib, goto, vararg, coroutine, gc, cstack, db
**SKIPPED (4):** api.lua (needs C API), main.lua (needs CLI), heavy.lua (stress test), gengc.lua (needs generational GC)

**Note:** 12 of the 28 test files have sections skipped where the implementation has known gaps (yield across C boundaries, weak table/ephemeron GC, some debug hook accuracy tests). Estimated true compliance: ~85-90%.

## Debugging "assertion failed!" With No Details

When a test fails with just "assertion failed!" and no line number, add temporary prints to narrow it down:
```lua
-- Add at top of the test .lua file temporarily:
local old_assert = assert
assert = function(v, msg)
  if not v then
    print("ASSERT FAILED:", msg or "no message", debug.traceback())
  end
  return old_assert(v, msg)
end
```
Or add `print("checkpoint N")` between sections. **Remove all debug prints after fixing.**

## Project Structure

```
crates/selune-core/src/      — Values (value.rs), GC (gc.rs), tables, strings
crates/selune-compiler/src/  — Lexer (lexer.rs), compiler (compiler/mod.rs, expr.rs, scope.rs)
crates/selune-vm/src/        — VM (vm.rs), dispatch (dispatch.rs), arithmetic, metamethods
crates/selune-stdlib/src/    — math.rs, string_lib.rs, table_lib.rs, io_lib.rs, os_lib.rs, debug_lib.rs, utf8_lib.rs, package_lib.rs
crates/selune/src/           — CLI (main.rs)
```

## Key Architecture Rules

1. **free_reg_to only LOWERS** — use `scope.free_reg = target` when target > free_reg
2. **Yield in call_function** — when execute_from returns Err(Yield), do NOT truncate call_stack, reset stack_top, or unwind TBC
3. **Native redirect list** — when adding special natives needing &mut Vm, update BOTH Call handler AND TailCall handler in dispatch.rs
4. **Userdata metamethods** — get_metamethod() and table_index() both handle userdata metatables

## Environment

- macOS ARM64
- Rust toolchain at ~/.rustup/toolchains/stable-aarch64-apple-darwin/bin
- No clippy/rustfmt locally (CI only)
- Always prefix cargo commands with the PATH export above

## Reference

- Lua 5.4 manual: https://www.lua.org/manual/5.4/
- Full guide with bug patterns and missing features: see GitHub issue #27
