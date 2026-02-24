-- Benchmark: table_object
-- Tests: OOP-style table usage with metatables
local clock = os.clock

local Point = {}
Point.__index = Point

function Point.new(x, y)
    return setmetatable({x = x, y = y}, Point)
end

function Point:dist(other)
    local dx = self.x - other.x
    local dy = self.y - other.y
    return math.sqrt(dx * dx + dy * dy)
end

function Point:translate(dx, dy)
    self.x = self.x + dx
    self.y = self.y + dy
    return self
end

local function run()
    local N = 1000000
    local points = {}
    for i = 1, N do
        points[i] = Point.new(i * 0.1, i * 0.2)
    end
    local total = 0.0
    for i = 1, N - 1 do
        total = total + points[i]:dist(points[i + 1])
    end
    for i = 1, N do
        points[i]:translate(1.0, -1.0)
    end
    return total + points[1].x
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: table_object %.6f", elapsed))
