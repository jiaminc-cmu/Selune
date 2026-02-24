-- Benchmark: string_format
-- Tests: string.format with various format specifiers
local clock = os.clock
local format = string.format

local function run()
    local N = 1000000
    local sum = 0
    for i = 1, N do
        local s = format("item %d: value=%.4f, hex=%x, str=%s", i, i * 0.001, i, "hello")
        sum = sum + #s
    end
    return sum
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: string_format %.6f", elapsed))
