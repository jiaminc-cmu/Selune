-- Benchmark: coroutines
-- Tests: coroutine create/resume/yield cycles
-- NOTE: Skipped on LuaJIT (different coroutine semantics may cause issues)
local clock = os.clock

local function producer(n)
    for i = 1, n do
        coroutine.yield(i)
    end
end

local function run()
    local N = 1000000
    local sum = 0

    -- Simple yield/resume
    local co = coroutine.create(function() producer(N) end)
    for i = 1, N do
        local ok, val = coroutine.resume(co)
        if ok and val then sum = sum + val end
    end

    -- Many short coroutines
    for i = 1, 100000 do
        local c = coroutine.create(function(x) coroutine.yield(x + 1) return x + 2 end)
        local _, v1 = coroutine.resume(c, i)
        local _, v2 = coroutine.resume(c)
        sum = sum + v1 + v2
    end

    return sum
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: coroutines %.6f", elapsed))
