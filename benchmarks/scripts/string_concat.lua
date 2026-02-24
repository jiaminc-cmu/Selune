-- Benchmark: string_concat
-- Tests: string concatenation, table.concat
local clock = os.clock

local function run()
    local N = 500000
    -- table.concat approach (efficient)
    local parts = {}
    for i = 1, N do
        parts[i] = "item" .. i
    end
    local big = table.concat(parts, ",")

    -- Repeated short concatenation
    local s = ""
    for i = 1, 1000 do
        s = s .. "x"
    end

    return #big + #s
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: string_concat %.6f", elapsed))
