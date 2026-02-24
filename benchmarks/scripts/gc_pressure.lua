-- Benchmark: gc_pressure
-- Tests: allocation rate, GC throughput
local clock = os.clock

local function run()
    local N = 2000000
    local live = {}
    local sum = 0

    for i = 1, N do
        -- Create short-lived tables
        local t = {i, i + 1, i + 2}
        sum = sum + t[1] + t[2] + t[3]

        -- Keep a rotating window of 1000 live objects
        local idx = (i % 1000) + 1
        live[idx] = {value = i, data = string.rep("x", 10)}
    end

    return sum + #live
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: gc_pressure %.6f", elapsed))
