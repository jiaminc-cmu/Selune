-- Control flow: all branch and loop forms
local x = 10

-- if/elseif/else
if x > 20 then
    x = 0
elseif x > 5 then
    x = x + 1
else
    x = -1
end

-- while loop
local sum = 0
local i = 1
while i <= x do
    sum = sum + i
    i = i + 1
end

-- repeat/until
local count = 0
repeat
    count = count + 1
until count >= 5

-- numeric for
local total = 0
for j = 1, 10 do
    total = total + j
end

-- numeric for with step
local rev = 0
for j = 10, 1, -1 do
    rev = rev + j
end

-- do/end block
do
    local temp = 42
end

return sum, count, total
