use super::helpers::*;

// ── next() function ─────────────────────────────────────────────

#[test]
fn test_next_empty_table() {
    run_check_ints(
        r#"
        local t = {}
        local k = next(t)
        if k == nil then return 1 else return 0 end
        "#,
        &[1],
    );
}

#[test]
fn test_next_array() {
    run_check_ints(
        r#"
        local t = {10, 20, 30}
        local k, v = next(t)
        return k, v
        "#,
        &[1, 10],
    );
}

#[test]
fn test_next_iterate_array() {
    // next with explicit stepping
    run_check_ints(
        r#"
        local t = {10, 20, 30}
        local k1, v1 = next(t)
        local k2, v2 = next(t, k1)
        local k3, v3 = next(t, k2)
        return v1 + v2 + v3
        "#,
        &[60],
    );
}

// ── pairs() basic ───────────────────────────────────────────────

#[test]
fn test_pairs_sum_values() {
    run_check_ints(
        r#"
        local t = {10, 20, 30}
        local sum = 0
        for k, v in pairs(t) do
            sum = sum + v
        end
        return sum
        "#,
        &[60],
    );
}

#[test]
fn test_pairs_count_elements() {
    run_check_ints(
        r#"
        local t = {a = 1, b = 2, c = 3}
        local count = 0
        for k, v in pairs(t) do
            count = count + 1
        end
        return count
        "#,
        &[3],
    );
}

#[test]
fn test_pairs_sum_hash_values() {
    run_check_ints(
        r#"
        local t = {x = 10, y = 20, z = 30}
        local sum = 0
        for k, v in pairs(t) do
            sum = sum + v
        end
        return sum
        "#,
        &[60],
    );
}

#[test]
fn test_pairs_empty_table() {
    run_check_ints(
        r#"
        local count = 0
        for k, v in pairs({}) do
            count = count + 1
        end
        return count
        "#,
        &[0],
    );
}

#[test]
fn test_pairs_mixed_table() {
    run_check_ints(
        r#"
        local t = {10, 20, x = 30}
        local sum = 0
        for k, v in pairs(t) do
            sum = sum + v
        end
        return sum
        "#,
        &[60],
    );
}

// ── ipairs() ────────────────────────────────────────────────────

#[test]
fn test_ipairs_basic() {
    run_check_ints(
        r#"
        local t = {10, 20, 30}
        local sum = 0
        for i, v in ipairs(t) do
            sum = sum + v
        end
        return sum
        "#,
        &[60],
    );
}

#[test]
fn test_ipairs_indices() {
    run_check_ints(
        r#"
        local t = {10, 20, 30}
        local idx_sum = 0
        for i, v in ipairs(t) do
            idx_sum = idx_sum + i
        end
        return idx_sum
        "#,
        &[6],
    );
}

#[test]
fn test_ipairs_empty_table() {
    run_check_ints(
        r#"
        local count = 0
        for i, v in ipairs({}) do
            count = count + 1
        end
        return count
        "#,
        &[0],
    );
}

#[test]
fn test_ipairs_stops_at_nil() {
    run_check_ints(
        r#"
        local t = {10, 20, nil, 40}
        local count = 0
        for i, v in ipairs(t) do
            count = count + 1
        end
        return count
        "#,
        &[2],
    );
}

#[test]
fn test_ipairs_ignores_hash() {
    // ipairs only iterates array part
    run_check_ints(
        r#"
        local t = {10, 20, x = 99}
        local sum = 0
        for i, v in ipairs(t) do
            sum = sum + v
        end
        return sum
        "#,
        &[30],
    );
}

// ── Generic for with break ──────────────────────────────────────

#[test]
fn test_generic_for_break() {
    run_check_ints(
        r#"
        local t = {10, 20, 30, 40, 50}
        local sum = 0
        for i, v in ipairs(t) do
            if v > 30 then break end
            sum = sum + v
        end
        return sum
        "#,
        &[60],
    );
}

// ── Generic for with single variable ────────────────────────────

#[test]
fn test_generic_for_single_var() {
    run_check_ints(
        r#"
        local t = {a = 1, b = 2, c = 3}
        local count = 0
        for k in pairs(t) do
            count = count + 1
        end
        return count
        "#,
        &[3],
    );
}

// ── Nested generic for loops ────────────────────────────────────

#[test]
fn test_nested_generic_for() {
    run_check_ints(
        r#"
        local t1 = {1, 2}
        local t2 = {10, 20}
        local sum = 0
        for _, a in ipairs(t1) do
            for _, b in ipairs(t2) do
                sum = sum + a * b
            end
        end
        return sum
        "#,
        &[90],
    );
}

// ── Custom iterator ─────────────────────────────────────────────

#[test]
fn test_custom_stateless_iterator() {
    run_check_ints(
        r#"
        local function range_iter(max, current)
            current = current + 1
            if current > max then return nil end
            return current
        end

        local sum = 0
        for i in range_iter, 5, 0 do
            sum = sum + i
        end
        return sum
        "#,
        &[15],
    );
}

#[test]
fn test_custom_closure_iterator() {
    run_check_ints(
        r#"
        local function counter(n)
            local i = 0
            return function()
                i = i + 1
                if i > n then return nil end
                return i
            end
        end

        local sum = 0
        for v in counter(4) do
            sum = sum + v
        end
        return sum
        "#,
        &[10],
    );
}

// ── pairs/ipairs return values ──────────────────────────────────

#[test]
fn test_pairs_returns_next() {
    // pairs(t) returns next, t, nil — verify by calling directly
    run_check_ints(
        r#"
        local t = {42}
        local f, s, c = pairs(t)
        local k, v = f(s, c)
        return v
        "#,
        &[42],
    );
}

// ── Generic for with multiple return values ─────────────────────

#[test]
fn test_generic_for_three_vars() {
    // Custom iterator returning 3 values
    run_check_ints(
        r#"
        local data = {{1, 2, 3}, {4, 5, 6}}
        local idx = 0
        local function iter()
            idx = idx + 1
            if idx > #data then return nil end
            return data[idx][1], data[idx][2], data[idx][3]
        end

        local sum = 0
        for a, b, c in iter do
            sum = sum + a + b + c
        end
        return sum
        "#,
        &[21],
    );
}

// ── Generic for preserves state correctly ───────────────────────

#[test]
fn test_generic_for_state_preserved() {
    run_check_ints(
        r#"
        local t = {10, 20, 30}
        local result = 0
        for i, v in ipairs(t) do
            result = result * 10 + i
        end
        return result
        "#,
        &[123],
    );
}

// ── pcall with generic for ──────────────────────────────────────

#[test]
fn test_pcall_with_pairs() {
    run_check_ints(
        r#"
        local ok, result = pcall(function()
            local t = {10, 20, 30}
            local sum = 0
            for k, v in pairs(t) do
                sum = sum + v
            end
            return sum
        end)
        if ok then return result else return -1 end
        "#,
        &[60],
    );
}
