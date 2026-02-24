-- Benchmark: method_calls
-- Tests: method dispatch via metatables, self parameter passing
local clock = os.clock

local Animal = {}
Animal.__index = Animal

function Animal.new(name, sound)
    return setmetatable({name = name, sound = sound, count = 0}, Animal)
end

function Animal:speak()
    self.count = self.count + 1
    return self.sound
end

function Animal:get_count()
    return self.count
end

local function run()
    local N = 5000000
    local cat = Animal.new("Cat", "meow")
    local dog = Animal.new("Dog", "woof")

    local sum = 0
    for i = 1, N do
        cat:speak()
        dog:speak()
        sum = sum + cat:get_count() + dog:get_count()
    end
    return sum
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: method_calls %.6f", elapsed))
