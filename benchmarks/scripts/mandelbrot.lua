-- Benchmark: mandelbrot
-- Tests: float arithmetic, tight inner loops, bit operations
local clock = os.clock

local function run()
    local size = 1000
    local max_iter = 50
    local sum = 0

    for y = 0, size - 1 do
        local ci = 2.0 * y / size - 1.0
        for x = 0, size - 1 do
            local cr = 2.0 * x / size - 1.5
            local zr, zi = 0.0, 0.0
            local iter = 0
            while iter < max_iter do
                local zr2 = zr * zr
                local zi2 = zi * zi
                if zr2 + zi2 > 4.0 then break end
                zi = 2.0 * zr * zi + ci
                zr = zr2 - zi2 + cr
                iter = iter + 1
            end
            sum = sum + iter
        end
    end

    return sum
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: mandelbrot %.6f", elapsed))
