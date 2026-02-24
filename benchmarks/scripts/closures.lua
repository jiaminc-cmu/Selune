-- Benchmark: closures
-- Tests: closure creation, upvalue access, higher-order functions
local clock = os.clock

local function make_counter(start)
    local n = start
    return function()
        n = n + 1
        return n
    end
end

local function make_adder(x)
    return function(y) return x + y end
end

local function apply(f, t)
    local result = {}
    for i = 1, #t do
        result[i] = f(t[i])
    end
    return result
end

local function run()
    local N = 2000000
    -- Create and call many closures
    local sum = 0
    for i = 1, N do
        local counter = make_counter(i)
        sum = sum + counter() + counter()
    end

    -- Higher-order function usage
    local data = {}
    for i = 1, 10000 do data[i] = i end
    for _ = 1, 100 do
        local doubled = apply(make_adder(0), data)
        sum = sum + doubled[1]
    end

    return sum
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: closures %.6f", elapsed))
