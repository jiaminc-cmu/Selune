-- Benchmark: spectral_norm
-- Tests: float-heavy computation, nested loops
-- Adapted from the Computer Language Benchmarks Game
local clock = os.clock
local sqrt = math.sqrt

local function A(i, j)
    local ij = i + j
    return 1.0 / (ij * (ij + 1) / 2 + i + 1)
end

local function Av(n, x, y)
    for i = 0, n - 1 do
        local sum = 0.0
        for j = 0, n - 1 do
            sum = sum + A(i, j) * x[j + 1]
        end
        y[i + 1] = sum
    end
end

local function Atv(n, x, y)
    for i = 0, n - 1 do
        local sum = 0.0
        for j = 0, n - 1 do
            sum = sum + A(j, i) * x[j + 1]
        end
        y[i + 1] = sum
    end
end

local function AtAv(n, x, y)
    local tmp = {}
    for i = 1, n do tmp[i] = 0 end
    Av(n, x, tmp)
    Atv(n, tmp, y)
end

local function run()
    local n = 1000
    local u, v = {}, {}
    for i = 1, n do
        u[i] = 1.0
        v[i] = 0.0
    end

    for _ = 1, 10 do
        AtAv(n, u, v)
        AtAv(n, v, u)
    end

    local vBv, vv = 0.0, 0.0
    for i = 1, n do
        vBv = vBv + u[i] * v[i]
        vv = vv + v[i] * v[i]
    end
    return sqrt(vBv / vv)
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: spectral_norm %.6f", elapsed))
