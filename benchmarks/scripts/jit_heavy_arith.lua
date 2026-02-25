-- Benchmark: jit_heavy_arith
-- Tests: JIT performance on heavy integer arithmetic (add, mul, idiv, mod)
-- The inner function is called 1100 times (above JIT threshold of 1000)
-- so Cranelift-compiled native code handles the timed iterations.
local clock = os.clock

local function heavy_arith(n)
    local sum = 0
    for i = 1, n do
        sum = sum + i * 3 - i // 2 + i % 7
    end
    return sum
end

-- Warm up: 1001 calls triggers JIT compilation at call 1000
for j = 1, 1001 do
    heavy_arith(10)
end

-- Timed run: 100 calls to JIT-compiled function with large N
local t0 = clock()
local total = 0
for j = 1, 100 do
    total = total + heavy_arith(1000000)
end
local elapsed = clock() - t0
if total == 0 then print("impossible") end
print(string.format("RESULT: jit_heavy_arith %.6f", elapsed))
