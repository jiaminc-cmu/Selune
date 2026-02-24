-- Benchmark: string_match
-- Tests: pattern matching, string.find, string.gmatch, string.gsub
local clock = os.clock

local function run()
    local text = string.rep("the quick brown fox jumps over the lazy dog ", 10000)
    local count = 0

    -- string.find repeated
    local pos = 1
    while true do
        local s, e = string.find(text, "fox", pos, true)
        if not s then break end
        count = count + 1
        pos = e + 1
    end

    -- string.gmatch with pattern
    for w in string.gmatch(text, "%a+") do
        count = count + 1
    end

    -- string.gsub
    local result = string.gsub(text, "dog", "cat")
    count = count + #result

    return count
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: string_match %.6f", elapsed))
