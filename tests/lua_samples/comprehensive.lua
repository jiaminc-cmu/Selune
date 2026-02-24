-- Comprehensive: exercises every major language feature

-- Locals and globals
local a = 1
local b, c = 2, 3
x = "global"

-- Arithmetic and bitwise
local sum = a + b * c
local div = 10 / 3
local idiv = 10 // 3
local mod = 10 % 3
local pow = 2 ^ 10
local band = 0xFF & 0x0F
local bor = 0xF0 | 0x0F
local bxor = 0xFF ~ 0x0F
local bnot = ~0
local shl = 1 << 4
local shr = 16 >> 2

-- String operations
local s1 = "hello"
local s2 = 'world'
local s3 = s1 .. " " .. s2
local s4 = [[long string]]
local len = #s3

-- Comparisons and logic
local eq = (a == b)
local neq = (a ~= b)
local lt = (a < b)
local le = (a <= b)
local gt = (a > b)
local ge = (a >= b)
local land = (true and 42)
local lor = (nil or "default")
local lnot = not false

-- Table constructors
local t1 = {}
local t2 = {1, 2, 3}
local t3 = {x = 1, y = 2}
local t4 = {1, x = 2, 3, y = 4}
local t5 = {[1+1] = "two"}

-- Table access
t1.name = "test"
t1[1] = 42
local v1 = t1.name
local v2 = t1[1]

-- Functions
function f1() end
function f2(a, b) return a + b end
function f3(...) return ... end
local f4 = function(x) return x * 2 end

-- Local functions
local function fact(n)
    if n <= 1 then return 1 end
    return n * fact(n - 1)
end

-- Methods
local obj = {}
function obj:method(x)
    return self, x
end

-- Control flow
if a > 0 then
    a = a + 1
elseif a == 0 then
    a = 0
else
    a = -1
end

-- Loops
while b > 0 do
    b = b - 1
end

repeat
    c = c - 1
until c <= 0

for i = 1, 10 do
    local _ = i
end

for i = 10, 1, -1 do
    local _ = i
end

for k, v in pairs do
end

-- Break in loop
for i = 1, 100 do
    if i > 5 then
        break
    end
end

-- Goto and labels
do
  goto skip
  print("dead code")
  ::skip::
end

-- Nested closures with upvalue chain
local function outer()
    local x = 1
    local function middle()
        local function inner()
            return x
        end
        return inner
    end
    return middle
end

-- Multiple returns
local function multi() return 1, 2, 3 end

-- Tail call
local function tail(x) return f2(x, 1) end

-- Semicolons
;;;

-- Do/end blocks
do
    local scoped = true
end

-- Return
return fact(5)
