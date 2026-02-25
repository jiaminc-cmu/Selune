-- Benchmark: jit_sum_loop
-- Tests: JIT performance on integer sum loop
-- The inner function is called 1100 times (above JIT threshold of 1000)
-- so Cranelift-compiled native code handles the timed iterations.
local clock = os.clock

local function sum_loop(n)
    local sum = 0
    for i = 1, n do
        sum = sum + i
    end
    return sum
end

-- Warm up: 1001 calls triggers JIT compilation at call 1000
for j = 1, 1001 do
    sum_loop(10)
end

-- Timed run: 100 calls to JIT-compiled function with large N
local t0 = clock()
local total = 0
for j = 1, 100 do
    total = total + sum_loop(10000000)
end
local elapsed = clock() - t0
if total == 0 then print("impossible") end
print(string.format("RESULT: jit_sum_loop %.6f", elapsed))
