-- Benchmark: jit_generic_for (Inc 10)
-- Tests: Generic for loops staying in JIT (TForCall/TForLoop) combined with
-- numeric for-loop computation. Without Inc 10, the generic for side-exits
-- and the entire function runs in the interpreter, losing JIT benefits
-- for the arithmetic-heavy inner loop.
-- Uses modular arithmetic to keep values in small int range.
local clock = os.clock

-- Build a lookup table
local function make_table(n)
    local t = {}
    for i = 1, n do
        t[i] = i * 3 + 1
    end
    return t
end

local weights = make_table(20)

-- Uses ipairs to iterate over weights, then does arithmetic-heavy work
-- with each weight. The ipairs loop has per-iteration overhead from
-- TForCall, but the inner numeric loop benefits from JIT.
local function weighted_sum(weights, iters)
    local total = 0
    for _, w in ipairs(weights) do
        local sub = 0
        for j = 1, iters do
            sub = (sub + w * j) % 1000000007
        end
        total = (total + sub) % 1000000007
    end
    return total
end

-- Warm up to trigger call-count JIT
for j = 1, 1001 do
    weighted_sum(weights, 10)
end

-- Timed run: 20 weights * 5000 inner iters * 500 calls = 50M inner iterations
local t0 = clock()
local total = 0
for j = 1, 500 do
    total = (total + weighted_sum(weights, 5000)) % 1000000007
end
local elapsed = clock() - t0
if total == 0 then print("impossible") end
print(string.format("RESULT: jit_generic_for %.6f", elapsed))
