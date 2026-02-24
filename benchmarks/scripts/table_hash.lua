-- Benchmark: table_hash
-- Tests: hash table insert, lookup, deletion
local clock = os.clock

local function run()
    local t = {}
    local N = 1000000
    -- Insert string keys
    for i = 1, N do
        t["key" .. i] = i
    end
    -- Lookup
    local sum = 0
    for i = 1, N do
        sum = sum + t["key" .. i]
    end
    -- Delete half
    for i = 1, N, 2 do
        t["key" .. i] = nil
    end
    return sum
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: table_hash %.6f", elapsed))
