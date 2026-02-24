-- Benchmark: arithmetic
-- Tests: integer/float arithmetic, loop overhead
local clock = os.clock

local function run()
    local sum = 0
    for i = 1, 50000000 do
        sum = sum + i * 3 - math.floor(i / 2) + i % 7
    end
    return sum
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
-- Use result to prevent dead-code elimination
if result == 0 then print("impossible") end
print(string.format("RESULT: arithmetic %.6f", elapsed))
