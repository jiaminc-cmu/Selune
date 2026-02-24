-- Benchmark: binary_trees
-- Tests: tree allocation, recursive traversal, GC of deep structures
-- Adapted from the Computer Language Benchmarks Game
local clock = os.clock

local function make_tree(depth)
    if depth == 0 then
        return {1}
    end
    depth = depth - 1
    return {make_tree(depth), make_tree(depth)}
end

local function check_tree(tree)
    if #tree == 1 then return tree[1] end
    return check_tree(tree[1]) + check_tree(tree[2])
end

local function run()
    local min_depth = 4
    local max_depth = 16
    local stretch_depth = max_depth + 1

    -- Stretch tree
    local stretch = make_tree(stretch_depth)
    local stretch_check = check_tree(stretch)
    stretch = nil

    -- Long-lived tree
    local long_lived = make_tree(max_depth)

    local sum = stretch_check
    for depth = min_depth, max_depth, 2 do
        local iterations = 2 ^ (max_depth - depth + min_depth)
        local check = 0
        for _ = 1, iterations do
            check = check + check_tree(make_tree(depth))
        end
        sum = sum + check
    end

    sum = sum + check_tree(long_lived)
    return sum
end

local t0 = clock()
local result = run()
local elapsed = clock() - t0
if result == 0 then print("impossible") end
print(string.format("RESULT: binary_trees %.6f", elapsed))
