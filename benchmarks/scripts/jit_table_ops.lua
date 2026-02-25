-- Benchmark: jit_table_ops (Inc 10)
-- Tests: Table read/write inside JIT (GetI, SetI, SetTable, NewTable, SetList)
-- Without Inc 10, these opcodes cause side-exits.
local clock = os.clock

-- Creates a table, fills it, reads it back — all inside JIT
local function table_work(n)
    local t = {}
    for i = 1, n do
        t[i] = i * 2
    end
    local sum = 0
    for i = 1, n do
        sum = sum + t[i]
    end
    return sum
end

-- Warm up
for j = 1, 1001 do
    table_work(10)
end

-- Timed run
local t0 = clock()
local total = 0
for j = 1, 10000 do
    total = total + table_work(1000)
end
local elapsed = clock() - t0
if total == 0 then print("impossible") end
print(string.format("RESULT: jit_table_ops %.6f", elapsed))
