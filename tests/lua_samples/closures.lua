-- Closures: counter factory with upvalue capture
local function make_counter(start)
    local count = start or 0
    return function()
        count = count + 1
        return count
    end
end

local c1 = make_counter(0)
local c2 = make_counter(10)

local a = c1() -- 1
local b = c1() -- 2
local c = c2() -- 11

return a, b, c
