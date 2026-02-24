-- Benchmark: table_array
-- Tests: array creation, sequential access, table.insert/remove
local clock = os.clock

local function run()
    local t = {}
    local N = 2000000
    -- Fill array
    for i = 1, N do
        t[i] = i
    end
    -- Sum array
    local sum = 0
    for i = 1, N do
        sum = sum + t[i]
    end
    -- Reverse in-place
    for i = 1, math.floor(N / 2) do
        t[i], t[N - i + 1] = t[N - i + 1], t[i]
    end
    return sum + t[1]
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: table_array %.6f", elapsed))
