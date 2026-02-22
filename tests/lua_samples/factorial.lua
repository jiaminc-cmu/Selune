-- Factorial: tail-recursive style
local function fact(n, acc)
    if n <= 1 then
        return acc
    end
    return fact(n - 1, n * acc)
end

return fact(10, 1)
