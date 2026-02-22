-- Attributes: const and close (Lua 5.4)
local x <const> = 42
local y <const> = "hello"
local z <const> = true

-- Use const values
local a = x + 1
local b = y .. " world"

return a, b
