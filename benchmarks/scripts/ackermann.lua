-- Benchmark: ackermann (recursive calls)
-- Tests: function call overhead via Tak (Takeuchi) function
-- Tak is heavily recursive but bounded depth (~30-50 frames)
local clock = os.clock

local function tak(x, y, z)
    if y >= x then return z end
    return tak(tak(x - 1, y, z), tak(y - 1, z, x), tak(z - 1, x, y))
end

local t0 = clock()
local result = 0
for _ = 1, 100 do
    result = result + tak(24, 16, 8)
end
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: ackermann %.6f", elapsed))
