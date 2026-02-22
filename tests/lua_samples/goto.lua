-- Goto: forward and backward jumps
local x = 0

-- Forward goto
goto skip
x = 999
::skip::

-- Goto skipping over variable scope
do
    goto done
    local y = 42
    ::done::
end

-- Backward goto (loop simulation)
local count = 0
::again::
count = count + 1
if count < 5 then
    goto again
end

return x, count
