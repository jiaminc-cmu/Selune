-- Benchmark: jit_osr (Inc 11)
-- Tests: OSR enters JIT mid-execution of the CURRENT function call.
-- Without OSR, back-edge counting compiles for FUTURE calls only,
-- so the first (and only) call still finishes in the interpreter.
-- With OSR, the hot loop is detected, compiled, and entered immediately.
-- Uses modular sum to stay in small int range.
local clock = os.clock

local function osr_work(n)
    local sum = 0
    for i = 1, n do
        sum = (sum + i) % 1000000007
    end
    return sum
end

local t0 = clock()
local result = osr_work(100000000)
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: jit_osr %.6f", elapsed))
