-- Goto: forward and backward jumps
local x = 0

-- Forward goto
goto skip
x = 999
::skip::

-- Goto skipping statements (not locals) in block
do
    goto done
    print("skipped")
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
