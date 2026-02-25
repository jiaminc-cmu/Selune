-- Benchmark: jit_backedge (Inc 9)
-- Tests: Back-edge counting triggers JIT for functions called only ONCE.
-- Without back-edge counting, these functions never reach the call-count
-- threshold and run entirely in the interpreter.
local clock = os.clock

-- This function is called only ONCE with a huge N.
-- Back-edge counting at the for-loop detects the hot loop and compiles it.
-- Without Inc 9, this runs 100% interpreted.
-- Uses modular sum to stay in small int range (avoids boxed-int overhead).
local function single_call_work(n)
    local sum = 0
    for i = 1, n do
        sum = (sum + i) % 1000000007
    end
    return sum
end

-- Timed run: one call, large iteration count
-- Back-edge threshold is 10000, so after 10000 iterations the loop
-- gets compiled and the remaining iterations run as JIT.
local t0 = clock()
local result = single_call_work(100000000)
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: jit_backedge %.6f", elapsed))
