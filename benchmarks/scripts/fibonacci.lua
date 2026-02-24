-- Benchmark: fibonacci
-- Tests: recursive function calls, integer arithmetic
local clock = os.clock

local function fib(n)
    if n < 2 then return n end
    return fib(n - 1) + fib(n - 2)
end

local t0 = clock()
local result = fib(35)
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: fibonacci %.6f", elapsed))
