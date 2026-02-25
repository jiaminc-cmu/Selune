-- Benchmark: jit_float_arith
-- Tests: JIT performance on float arithmetic (add, mul, div)
-- The inner function is called 1100 times (above JIT threshold of 1000)
-- so Cranelift-compiled native code handles the timed iterations.
local clock = os.clock

local function float_arith(n)
    local sum = 0.0
    local x = 1.5
    for i = 1, n do
        sum = sum + x * 2.0 - x / 3.0
        x = x + 0.01
    end
    return sum
end

-- Warm up: 1001 calls triggers JIT compilation at call 1000
for j = 1, 1001 do
    float_arith(10)
end

-- Timed run: 100 calls to JIT-compiled function with large N
local t0 = clock()
local total = 0.0
for j = 1, 100 do
    total = total + float_arith(1000000)
end
local elapsed = clock() - t0
if total == 0 then print("impossible") end
print(string.format("RESULT: jit_float_arith %.6f", elapsed))
