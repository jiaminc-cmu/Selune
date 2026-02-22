use super::helpers::*;

// ---- table.insert ----

#[test]
fn test_table_insert_append() {
    run_check_ints(
        r#"
        local t = {1, 2, 3}
        table.insert(t, 4)
        return t[1], t[2], t[3], t[4]
        "#,
        &[1, 2, 3, 4],
    );
}

#[test]
fn test_table_insert_at_pos() {
    run_check_ints(
        r#"
        local t = {1, 2, 3}
        table.insert(t, 2, 99)
        return t[1], t[2], t[3], t[4]
        "#,
        &[1, 99, 2, 3],
    );
}

#[test]
fn test_table_insert_at_beginning() {
    run_check_ints(
        r#"
        local t = {1, 2, 3}
        table.insert(t, 1, 0)
        return t[1], t[2], t[3], t[4]
        "#,
        &[0, 1, 2, 3],
    );
}

#[test]
fn test_table_insert_empty() {
    run_check_ints(
        r#"
        local t = {}
        table.insert(t, 42)
        return t[1]
        "#,
        &[42],
    );
}

// ---- table.remove ----

#[test]
fn test_table_remove_last() {
    run_check_ints(
        r#"
        local t = {1, 2, 3}
        local removed = table.remove(t)
        return removed, #t
        "#,
        &[3, 2],
    );
}

#[test]
fn test_table_remove_at_pos() {
    run_check_ints(
        r#"
        local t = {10, 20, 30, 40}
        local removed = table.remove(t, 2)
        return removed, t[1], t[2], t[3]
        "#,
        &[20, 10, 30, 40],
    );
}

#[test]
fn test_table_remove_first() {
    run_check_ints(
        r#"
        local t = {10, 20, 30}
        local removed = table.remove(t, 1)
        return removed, t[1], t[2]
        "#,
        &[10, 20, 30],
    );
}

// ---- table.concat ----

#[test]
fn test_table_concat_basic() {
    run_check_strings(
        r#"
        local t = {"a", "b", "c"}
        return table.concat(t)
        "#,
        &["abc"],
    );
}

#[test]
fn test_table_concat_with_sep() {
    run_check_strings(
        r#"
        local t = {"hello", "world"}
        return table.concat(t, ", ")
        "#,
        &["hello, world"],
    );
}

#[test]
fn test_table_concat_numbers() {
    run_check_strings(
        r#"
        local t = {1, 2, 3}
        return table.concat(t, "-")
        "#,
        &["1-2-3"],
    );
}

#[test]
fn test_table_concat_range() {
    run_check_strings(
        r#"
        local t = {"a", "b", "c", "d", "e"}
        return table.concat(t, ",", 2, 4)
        "#,
        &["b,c,d"],
    );
}

#[test]
fn test_table_concat_empty() {
    run_check_strings(
        r#"
        local t = {}
        return table.concat(t, ",")
        "#,
        &[""],
    );
}

// ---- table.sort ----

#[test]
fn test_table_sort_default() {
    run_check_ints(
        r#"
        local t = {3, 1, 4, 1, 5, 9, 2, 6}
        table.sort(t)
        return t[1], t[2], t[3], t[4], t[5], t[6], t[7], t[8]
        "#,
        &[1, 1, 2, 3, 4, 5, 6, 9],
    );
}

#[test]
fn test_table_sort_strings() {
    run_check_strings(
        r#"
        local t = {"banana", "apple", "cherry"}
        table.sort(t)
        return t[1], t[2], t[3]
        "#,
        &["apple", "banana", "cherry"],
    );
}

#[test]
fn test_table_sort_custom_comparator() {
    run_check_ints(
        r#"
        local t = {3, 1, 4, 1, 5}
        table.sort(t, function(a, b) return a > b end)
        return t[1], t[2], t[3], t[4], t[5]
        "#,
        &[5, 4, 3, 1, 1],
    );
}

#[test]
fn test_table_sort_single_element() {
    run_check_ints(
        r#"
        local t = {42}
        table.sort(t)
        return t[1]
        "#,
        &[42],
    );
}

#[test]
fn test_table_sort_empty() {
    run_check_ints(
        r#"
        local t = {}
        table.sort(t)
        return #t
        "#,
        &[0],
    );
}

#[test]
fn test_table_sort_already_sorted() {
    run_check_ints(
        r#"
        local t = {1, 2, 3, 4, 5}
        table.sort(t)
        return t[1], t[2], t[3], t[4], t[5]
        "#,
        &[1, 2, 3, 4, 5],
    );
}

// ---- table.move ----

#[test]
fn test_table_move_same_table() {
    run_check_ints(
        r#"
        local t = {1, 2, 3, 4, 5}
        table.move(t, 1, 3, 2)
        return t[1], t[2], t[3], t[4]
        "#,
        &[1, 1, 2, 3],
    );
}

#[test]
fn test_table_move_to_other() {
    run_check_ints(
        r#"
        local a = {10, 20, 30}
        local b = {}
        table.move(a, 1, 3, 1, b)
        return b[1], b[2], b[3]
        "#,
        &[10, 20, 30],
    );
}

// ---- table.pack / table.unpack ----

#[test]
fn test_table_pack_basic() {
    run_check_ints(
        r#"
        local t = table.pack(10, 20, 30)
        return t[1], t[2], t[3], t.n
        "#,
        &[10, 20, 30, 3],
    );
}

#[test]
fn test_table_pack_empty() {
    run_check_ints(
        r#"
        local t = table.pack()
        return t.n
        "#,
        &[0],
    );
}

#[test]
fn test_table_unpack_basic() {
    run_check_ints(
        r#"
        return table.unpack({10, 20, 30})
        "#,
        &[10, 20, 30],
    );
}

#[test]
fn test_table_unpack_range() {
    run_check_ints(
        r#"
        return table.unpack({10, 20, 30, 40}, 2, 3)
        "#,
        &[20, 30],
    );
}

#[test]
fn test_table_pack_unpack_roundtrip() {
    run_check_ints(
        r#"
        local t = table.pack(1, 2, 3)
        return table.unpack(t, 1, t.n)
        "#,
        &[1, 2, 3],
    );
}

// ---- integration ----

#[test]
fn test_table_insert_remove_combination() {
    run_check_ints(
        r#"
        local t = {}
        table.insert(t, 10)
        table.insert(t, 20)
        table.insert(t, 30)
        table.remove(t, 2)
        return t[1], t[2], #t
        "#,
        &[10, 30, 2],
    );
}

#[test]
fn test_table_sort_with_insert() {
    run_check_ints(
        r#"
        local t = {}
        table.insert(t, 5)
        table.insert(t, 3)
        table.insert(t, 1)
        table.insert(t, 4)
        table.insert(t, 2)
        table.sort(t)
        return t[1], t[2], t[3], t[4], t[5]
        "#,
        &[1, 2, 3, 4, 5],
    );
}
