# Selune Benchmark Scripts

Lua benchmark scripts for comparing Selune against PUC Lua 5.4 and LuaJIT 2.1.

## Running Benchmarks

```bash
# Build Selune first
export PATH="$HOME/.rustup/toolchains/stable-aarch64-apple-darwin/bin:$PATH"
cargo build --release

# Run all benchmarks (requires PUC Lua and LuaJIT installed)
./benchmarks/run_benchmarks.sh

# Run a single benchmark
./target/release/selune benchmarks/scripts/particle_sim.lua
```

Each script prints a `RESULT: <name> <seconds>` line used by the harness.

## Benchmark Descriptions

### Arithmetic & Loops
| Script | Description |
|--------|-------------|
| `arithmetic.lua` | Integer and float arithmetic in tight loops |
| `fibonacci.lua` | Recursive Fibonacci (function call overhead) |
| `ackermann.lua` | Deeply recursive Ackermann function |

### Tables
| Script | Description |
|--------|-------------|
| `table_array.lua` | Array-style table insert/access |
| `table_hash.lua` | Hash-style table insert/lookup |
| `table_object.lua` | OOP-style table usage with metatables |

### Strings
| Script | Description |
|--------|-------------|
| `string_concat.lua` | String concatenation performance |
| `string_match.lua` | Pattern matching engine |
| `string_format.lua` | `string.format` throughput |

### Functions & Coroutines
| Script | Description |
|--------|-------------|
| `closures.lua` | Closure creation and upvalue access |
| `method_calls.lua` | OOP method dispatch via `:` syntax |
| `coroutines.lua` | Coroutine yield/resume overhead |

### GC & Allocation
| Script | Description |
|--------|-------------|
| `gc_pressure.lua` | High allocation rate, GC stress |
| `binary_trees.lua` | Tree allocation and traversal (GC benchmark) |

### Numeric / Scientific
| Script | Description |
|--------|-------------|
| `spectral_norm.lua` | Float-heavy nested loops (spectral norm computation) |
| `mandelbrot.lua` | Mandelbrot set: tight float loops, comparisons |
| `nbody.lua` | N-body gravitational simulation (struct-of-tables, `math.sqrt`) |
| `raytracer.lua` | Simple raytracer (float math, table-as-vector) |
| `particle_sim.lua` | 2D particle system: gravity, attractors, wall bounce |

## Showcase: particle_sim

`particle_sim.lua` is a **game-engine-style** 2D particle physics simulation designed to highlight Selune's JIT strengths. It models 2,000 particles over 4,000 physics timesteps each, with:

- Gravitational pull toward two attractor points (inverse-square force)
- Velocity drag and wall-bounce reflections
- Kinetic energy accumulation for correctness verification

### Why it's fast on Selune

The inner `attract_and_step()` function is pure float arithmetic in local variables with no table access, string ops, or allocations in the hot path. After 1,000 calls it gets JIT-compiled to native AArch64 code via Cranelift. This maps directly to Selune's JIT sweet spot:

- `fadd`, `fsub`, `fmul` compiled to single ARM NEON instructions
- `fdiv` with NaN canonicalization (3 extra ops, negligible overhead)
- Integer for-loop counter in a register
- Conditional wall-bounce branches compiled to native `cmp` + `b.cond`
- No `extern "C"` runtime helper calls in the hot loop

### Performance (Apple M3, best of 3 runs)

| Runtime | Time | vs PUC Lua |
|---------|------|------------|
| **Selune JIT** | **0.26s** | **6.4x faster** |
| PUC Lua 5.4 | 1.68s | 1.0x (baseline) |
| LuaJIT 2.1 | 0.19s | 8.8x faster |

All three runtimes produce bit-identical results (`energy = 185811.7433435723`).
