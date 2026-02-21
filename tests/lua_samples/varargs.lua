-- Varargs: various vararg patterns
local function sum(...)
    local args = {...}
    local total = 0
    for i = 1, #args do
        total = total + args[i]
    end
    return total
end

local function first(a, ...)
    return a
end

local function tail(a, ...)
    return ...
end

return sum(1, 2, 3, 4, 5)
