-- Benchmark: jit_float_forloop (Inc 12)
-- Tests: Float for-loops running in JIT instead of side-exiting.
-- Without Inc 12, ForPrep/ForLoop only handle integers in JIT,
-- so float for-loops immediately side-exit to interpreter.
local clock = os.clock

-- Uses float step — this is a float for-loop
local function float_integrate(n)
    local sum = 0.0
    local step = 1.0 / n
    for x = 0.0, 1.0 - step, step do
        sum = sum + x * x * step
    end
    return sum
end

-- Warm up
for j = 1, 1001 do
    float_integrate(100)
end

-- Timed run
local t0 = clock()
local total = 0.0
for j = 1, 100 do
    total = total + float_integrate(1000000)
end
local elapsed = clock() - t0
if total == 0 then print("impossible") end
print(string.format("RESULT: jit_float_forloop %.6f", elapsed))
