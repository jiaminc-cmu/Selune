-- Fibonacci: recursive with memoization pattern
local function fib(n)
    if n <= 1 then
        return n
    end
    return fib(n - 1) + fib(n - 2)
end

return fib(10)
