# Lua 5.4.7 Official Test Suite — Provenance

## Source

These test files are from the **official PUC-Rio Lua 5.4.7 test suite**, distributed at:

- https://www.lua.org/tests/
- Direct download: https://www.lua.org/tests/lua-5.4.7-tests.tar.gz

## Modifications

Some test files have minor modifications to work with Selune's portable mode:

- **Skipped sections** guarded by `if not _port then` or `if T then` are naturally excluded
  (Selune sets `_port=true` and `T=nil` in `run_test.lua`)
- A small number of test assertions were adjusted where they test implementation-specific
  behavior (e.g., exact GC collection counts, specific memory addresses) that differs
  between PUC-Rio's C implementation and Selune's Rust implementation
- No test logic was removed to make tests pass — adjustments only affect
  implementation-specific details, not language semantics

## Test Adapter

`run_test.lua` configures the test environment:

| Global | Value | Purpose |
|--------|-------|---------|
| `_port` | `true` | Skip platform-specific / OS-dependent tests |
| `_soft` | `true` | Use smaller limits (fewer iterations, smaller tables) |
| `_nomsg` | `true` | Suppress "not testing X" messages |
| `T` | `nil` | Disable internal C API tests (not applicable to Selune) |

## Excluded Test Files

4 files from the suite are not applicable to Selune:

| File | Reason |
|------|--------|
| `api.lua` | Tests the C embedding API (`lua_pushinteger`, etc.). Selune is pure Rust. |
| `main.lua` | Tests CLI flags (`-e`, `-l`, `-i`). Skipped by `_port=true`. |
| `heavy.lua` | Memory exhaustion stress test. Not a correctness test. |
| `gengc.lua` | Tests generational GC mode. Selune uses incremental mark-sweep. |
