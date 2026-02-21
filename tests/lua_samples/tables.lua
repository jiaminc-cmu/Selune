-- Tables: array, hash, mixed constructors and access
local arr = {10, 20, 30, 40, 50}
local hash = {name = "Lua", version = 5.4, jit = true}
local mixed = {1, 2, x = "hello", 3, y = "world"}

-- Field access
local n = hash.name
local v = hash.version

-- Index access
local first = arr[1]
local last = arr[5]

-- Bracket key constructor
local t = {[1 + 1] = "two", [true] = "yes"}

-- Nested tables
local nested = {
    inner = {a = 1, b = 2},
    list = {10, 20, 30}
}

return first, n
