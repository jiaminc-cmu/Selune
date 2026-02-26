-- Benchmark: math builtin inlining
-- Tests: JIT inline emission of math.sqrt, math.abs, math.floor, math.ceil, math.sin, math.cos
local clock = os.clock

local sqrt = math.sqrt
local abs = math.abs
local floor = math.floor
local ceil = math.ceil
local sin = math.sin
local cos = math.cos

local N = 5000000

-- Test math.sqrt in hot loop
local function bench_sqrt()
    local sum = 0.0
    for i = 1, N do
        sum = sum + sqrt(i * 1.0)
    end
    return sum
end

-- Test math.abs in hot loop (float)
local function bench_abs()
    local sum = 0.0
    for i = 1, N do
        sum = sum + abs(-i * 1.0)
    end
    return sum
end

-- Test math.floor in hot loop
local function bench_floor()
    local sum = 0.0
    for i = 1, N do
        sum = sum + floor(i * 1.1)
    end
    return sum
end

-- Test math.ceil in hot loop
local function bench_ceil()
    local sum = 0.0
    for i = 1, N do
        sum = sum + ceil(i * 1.1)
    end
    return sum
end

-- Test math.sin + math.cos in hot loop
local function bench_sincos()
    local sum = 0.0
    for i = 1, N do
        sum = sum + sin(i * 0.001) + cos(i * 0.001)
    end
    return sum
end

local t0 = clock()
local r1 = bench_sqrt()
local r2 = bench_abs()
local r3 = bench_floor()
local r4 = bench_ceil()
local r5 = bench_sincos()
local elapsed = clock() - t0

-- Prevent dead code elimination
if r1 + r2 + r3 + r4 + r5 == 0 then print("impossible") end
print(string.format("RESULT: jit_math_builtins %.6f", elapsed))
