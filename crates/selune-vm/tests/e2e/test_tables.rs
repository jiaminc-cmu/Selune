use super::helpers::*;

#[test]
fn test_empty_table() {
    run_check_ints("local t = {}; return 0", &[0]);
}

#[test]
fn test_array_construction() {
    run_check_ints("local t = {10, 20, 30}; return t[2]", &[20]);
}

#[test]
fn test_array_first() {
    run_check_ints("local t = {10, 20, 30}; return t[1]", &[10]);
}

#[test]
fn test_array_last() {
    run_check_ints("local t = {10, 20, 30}; return t[3]", &[30]);
}

#[test]
fn test_hash_construction() {
    run_check_ints("local t = {x = 10, y = 20}; return t.x + t.y", &[30]);
}

#[test]
fn test_dynamic_set_index() {
    run_check_ints("local t = {}; t[1] = 42; return t[1]", &[42]);
}

#[test]
fn test_dynamic_set_field() {
    run_check_ints("local t = {}; t.x = 42; return t.x", &[42]);
}

#[test]
fn test_table_length() {
    run_check_ints("local t = {1,2,3,4,5}; return #t", &[5]);
}

#[test]
fn test_table_length_empty() {
    run_check_ints("local t = {}; return #t", &[0]);
}

#[test]
fn test_global_set_get() {
    run_check_ints("x = 42; return x", &[42]);
}

#[test]
fn test_global_multiple() {
    run_check_ints("x = 10; y = 20; return x + y", &[30]);
}

#[test]
fn test_nested_table() {
    run_check_ints(
        "local t = {}; t.inner = {}; t.inner.x = 5; return t.inner.x",
        &[5],
    );
}

#[test]
fn test_mixed_construction() {
    run_check_ints("local t = {10, x=20}; return t[1] + t.x", &[30]);
}

#[test]
fn test_table_overwrite() {
    run_check_ints("local t = {x = 1}; t.x = 2; return t.x", &[2]);
}

#[test]
fn test_table_nil_access() {
    let results = run_lua("local t = {}; return t.x");
    assert_nil(&results, 0);
}

#[test]
fn test_table_nil_index() {
    let results = run_lua("local t = {}; return t[1]");
    assert_nil(&results, 0);
}

#[test]
fn test_array_iterate_for() {
    run_check_ints(
        "local t = {10, 20, 30, 40, 50}
        local s = 0
        for i = 1, #t do
            s = s + t[i]
        end
        return s",
        &[150],
    );
}

#[test]
fn test_table_as_accumulator() {
    run_check_ints(
        "local t = {sum = 0}
        for i = 1, 10 do
            t.sum = t.sum + i
        end
        return t.sum",
        &[55],
    );
}
