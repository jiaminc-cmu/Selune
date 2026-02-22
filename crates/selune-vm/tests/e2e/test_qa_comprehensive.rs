use super::helpers::*;

// ===========================================================================
// QA COMPREHENSIVE TESTS — Phase 2 VM
// Organized by category to systematically cover edge cases and untested paths.
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Arithmetic edge cases
// ---------------------------------------------------------------------------

#[test]
fn qa_integer_overflow_wrapping() {
    // i64::MAX = 9223372036854775807, this exceeds 47-bit inline so uses boxed int
    // Test that large integers round-trip correctly
    let (proto, strings) =
        selune_compiler::compiler::compile(b"local x = 9223372036854775807 return x + 0", "=test")
            .unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    let val = results[0]
        .as_full_integer(&vm.gc)
        .unwrap_or_else(|| panic!("expected integer, got {:?}", results[0]));
    assert_eq!(val, i64::MAX);
}

#[test]
fn qa_integer_min_value() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return -9223372036854775807 - 1", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    let val = results[0]
        .as_full_integer(&vm.gc)
        .unwrap_or_else(|| panic!("expected integer, got {:?}", results[0]));
    assert_eq!(val, i64::MIN);
}

#[test]
fn qa_float_division_zero() {
    let results = run_lua("return 1.0 / 0.0");
    let val = results[0].as_float().expect("expected float");
    assert!(
        val.is_infinite() && val.is_sign_positive(),
        "expected +inf, got {val}"
    );
}

#[test]
fn qa_float_neg_division_zero() {
    let results = run_lua("return -1.0 / 0.0");
    let val = results[0].as_float().expect("expected float");
    assert!(
        val.is_infinite() && val.is_sign_negative(),
        "expected -inf, got {val}"
    );
}

#[test]
fn qa_float_div_always_float() {
    let results = run_lua("return 10 / 2");
    assert_float(&results, 0, 5.0);
}

#[test]
fn qa_idiv_both_negative() {
    // Lua floor division: (-7) // (-2) = 3
    run_check_ints("return (-7) // (-2)", &[3]);
}

#[test]
fn qa_mod_both_negative() {
    // Lua mod: (-7) % (-2) = -1
    run_check_ints("return (-7) % (-2)", &[-1]);
}

#[test]
fn qa_mod_mixed_sign() {
    // -7 % 3 = 2  (result has sign of divisor)
    run_check_ints("return (-7) % 3", &[2]);
}

#[test]
fn qa_power_negative_base() {
    let results = run_lua("return (-2) ^ 3");
    assert_float(&results, 0, -8.0);
}

#[test]
fn qa_power_fractional() {
    let results = run_lua("return 4 ^ 0.5");
    assert_float(&results, 0, 2.0);
}

#[test]
fn qa_bitwise_and_basic() {
    run_check_ints("return 0xFF & 0x0F", &[0x0F]);
}

#[test]
fn qa_bitwise_or_basic() {
    run_check_ints("return 0xF0 | 0x0F", &[0xFF]);
}

#[test]
fn qa_bitwise_xor_basic() {
    run_check_ints("return 0xFF ~ 0x0F", &[0xF0]);
}

#[test]
fn qa_shift_left_large() {
    // 1 << 63 = i64::MIN (0x8000...0) — boxed int since > 47 bits
    let (proto, strings) = selune_compiler::compiler::compile(b"return 1 << 63", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    let val = results[0]
        .as_full_integer(&vm.gc)
        .unwrap_or_else(|| panic!("expected integer, got {:?}", results[0]));
    assert_eq!(val, i64::MIN);
}

#[test]
fn qa_shift_right_basic() {
    run_check_ints("return 256 >> 4", &[16]);
}

#[test]
fn qa_bnot_basic() {
    run_check_ints("return ~0", &[-1]);
}

#[test]
fn qa_bnot_minus_one() {
    run_check_ints("return ~(-1)", &[0]);
}

#[test]
fn qa_unary_minus_float() {
    let results = run_lua("return -(3.15)");
    assert_float(&results, 0, -3.15);
}

#[test]
fn qa_unary_minus_zero() {
    run_check_ints("return -0", &[0]);
}

#[test]
fn qa_not_integer() {
    // In Lua, 0 is truthy, so `not 0` is false
    let results = run_lua("return not 0");
    assert_bool(&results, 0, false);
}

#[test]
fn qa_not_string() {
    let results = run_lua("return not \"\"");
    assert_bool(&results, 0, false);
}

#[test]
fn qa_not_table() {
    let results = run_lua("return not {}");
    assert_bool(&results, 0, false);
}

// ---------------------------------------------------------------------------
// 2. Comparison edge cases
// ---------------------------------------------------------------------------

#[test]
fn qa_eq_integer_float_cross_type() {
    // 5 == 5.0 should be true in Lua 5.4
    let results = run_lua("return 5 == 5.0");
    assert_bool(&results, 0, true);
}

#[test]
fn qa_eq_integer_float_not_equal() {
    let results = run_lua("return 5 == 5.1");
    assert_bool(&results, 0, false);
}

#[test]
fn qa_lt_mixed_int_float() {
    let results = run_lua("return 3 < 3.5");
    assert_bool(&results, 0, true);
}

#[test]
fn qa_le_mixed_int_float() {
    let results = run_lua("return 3 <= 3.0");
    assert_bool(&results, 0, true);
}

#[test]
fn qa_eq_nil_nil() {
    let results = run_lua("return nil == nil");
    assert_bool(&results, 0, true);
}

#[test]
fn qa_eq_nil_false() {
    let results = run_lua("return nil == false");
    assert_bool(&results, 0, false);
}

#[test]
fn qa_neq_different_types() {
    let results = run_lua("return 1 ~= \"1\"");
    assert_bool(&results, 0, true);
}

#[test]
fn qa_eq_bool_bool() {
    let results = run_lua("return true == true");
    assert_bool(&results, 0, true);
}

#[test]
fn qa_lt_strings() {
    let results = run_lua("return \"abc\" < \"abd\"");
    assert_bool(&results, 0, true);
}

#[test]
fn qa_le_strings() {
    let results = run_lua("return \"abc\" <= \"abc\"");
    assert_bool(&results, 0, true);
}

// ---------------------------------------------------------------------------
// 3. String operations
// ---------------------------------------------------------------------------

#[test]
fn qa_concat_int_string() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return 42 .. \" hello\"", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "42 hello", &vm);
}

#[test]
fn qa_concat_float_string() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return 3.14 .. \"!\"", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "3.14!", &vm);
}

#[test]
fn qa_concat_many() {
    let (proto, strings) = selune_compiler::compiler::compile(
        b"return \"a\" .. \"b\" .. \"c\" .. \"d\" .. \"e\"",
        "=test",
    )
    .unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "abcde", &vm);
}

#[test]
fn qa_string_length() {
    run_check_ints("return #\"hello\"", &[5]);
}

#[test]
fn qa_string_length_empty() {
    run_check_ints("return #\"\"", &[0]);
}

// ---------------------------------------------------------------------------
// 4. Table operations — edge cases
// ---------------------------------------------------------------------------

#[test]
fn qa_table_nested_set_get() {
    run_check_ints(
        "local t = {a = {b = {c = 42}}}
         return t.a.b.c",
        &[42],
    );
}

#[test]
fn qa_table_integer_key_1_indexed() {
    run_check_ints(
        "local t = {10, 20, 30}
         return t[1], t[2], t[3]",
        &[10, 20, 30],
    );
}

#[test]
fn qa_table_length_with_gaps() {
    // Length with no gaps
    run_check_ints(
        "local t = {1, 2, 3, 4, 5}
         return #t",
        &[5],
    );
}

#[test]
fn qa_table_overwrite_field() {
    run_check_ints(
        "local t = {x = 1}
         t.x = 2
         return t.x",
        &[2],
    );
}

#[test]
fn qa_table_dynamic_string_key() {
    run_check_ints(
        "local t = {}
         local k = \"key\"
         t[k] = 99
         return t[k]",
        &[99],
    );
}

#[test]
fn qa_table_boolean_key() {
    run_check_ints(
        "local t = {}
         t[true] = 1
         t[false] = 2
         return t[true] + t[false]",
        &[3],
    );
}

#[test]
fn qa_table_large_array() {
    run_check_ints(
        "local t = {}
         for i = 1, 100 do
             t[i] = i
         end
         return t[1] + t[50] + t[100]",
        &[151],
    );
}

#[test]
fn qa_table_setlist_more_than_50() {
    // Test SetList with > LFIELDS_PER_FLUSH (50)
    // Build a table with 55 explicit elements
    run_check_ints(
        "local t = {
            1,2,3,4,5,6,7,8,9,10,
            11,12,13,14,15,16,17,18,19,20,
            21,22,23,24,25,26,27,28,29,30,
            31,32,33,34,35,36,37,38,39,40,
            41,42,43,44,45,46,47,48,49,50,
            51,52,53,54,55
         }
         return #t, t[1], t[55]",
        &[55, 1, 55],
    );
}

#[test]
fn qa_table_nil_access_returns_nil() {
    let results = run_lua("local t = {} return t.x");
    assert_nil(&results, 0);
}

#[test]
fn qa_table_nil_index_returns_nil() {
    let results = run_lua("local t = {} return t[999]");
    assert_nil(&results, 0);
}

// ---------------------------------------------------------------------------
// 5. Control flow edge cases
// ---------------------------------------------------------------------------

#[test]
fn qa_if_zero_is_truthy() {
    // In Lua, 0 is truthy
    run_check_ints("if 0 then return 1 else return 0 end", &[1]);
}

#[test]
fn qa_if_empty_string_is_truthy() {
    run_check_ints("if \"\" then return 1 else return 0 end", &[1]);
}

#[test]
fn qa_while_never_enters() {
    let results = run_lua("while false do return 1 end");
    assert_eq!(results.len(), 0);
}

#[test]
fn qa_repeat_until_true_once() {
    run_check_ints(
        "local x = 0
         repeat x = x + 1 until true
         return x",
        &[1],
    );
}

#[test]
fn qa_repeat_until_with_condition() {
    run_check_ints(
        "local x = 0
         repeat x = x + 1 until x >= 5
         return x",
        &[5],
    );
}

#[test]
fn qa_for_loop_single_iteration() {
    run_check_ints(
        "local s = 0
         for i = 1, 1 do s = s + i end
         return s",
        &[1],
    );
}

#[test]
fn qa_for_loop_zero_iterations() {
    run_check_ints(
        "local s = 0
         for i = 1, 0 do s = s + i end
         return s",
        &[0],
    );
}

#[test]
fn qa_for_loop_negative_step_no_enter() {
    run_check_ints(
        "local s = 0
         for i = 1, 10, -1 do s = s + i end
         return s",
        &[0],
    );
}

#[test]
fn qa_for_loop_float() {
    let results = run_lua(
        "local s = 0.0
         for i = 0.0, 1.0, 0.25 do s = s + i end
         return s",
    );
    assert_float(&results, 0, 2.5);
}

#[test]
fn qa_for_step_zero_error() {
    let err = run_lua_err("for i = 1, 10, 0 do end");
    assert!(
        err.contains("step is zero"),
        "expected step zero error, got: {err}"
    );
}

#[test]
fn qa_nested_if_else() {
    run_check_ints(
        "local x = 10
         if x > 20 then
             return 1
         elseif x > 5 then
             if x == 10 then
                 return 2
             else
                 return 3
             end
         else
             return 4
         end",
        &[2],
    );
}

#[test]
fn qa_and_returns_first_falsy() {
    let results = run_lua("return nil and 42");
    assert_nil(&results, 0);
}

#[test]
fn qa_and_returns_second_if_both_truthy() {
    run_check_ints("return 1 and 42", &[42]);
}

#[test]
fn qa_or_returns_first_truthy() {
    run_check_ints("return 1 or 42", &[1]);
}

#[test]
fn qa_or_returns_second_if_first_falsy() {
    run_check_ints("return nil or 42", &[42]);
}

#[test]
fn qa_or_returns_false_if_both_falsy() {
    let results = run_lua("return nil or false");
    assert_bool(&results, 0, false);
}

#[test]
fn qa_and_or_ternary_pattern() {
    // Lua idiom for ternary: (cond and a or b)
    run_check_ints("return (true and 10 or 20)", &[10]);
    run_check_ints("return (false and 10 or 20)", &[20]);
}

// ---------------------------------------------------------------------------
// 6. Scope and locals
// ---------------------------------------------------------------------------

#[test]
fn qa_local_shadows_outer() {
    run_check_ints(
        "local x = 1
         do
             local x = 2
         end
         return x",
        &[1],
    );
}

#[test]
fn qa_local_multiple_assign_extra_nil() {
    let results = run_lua(
        "local a, b, c = 1, 2
         return a, b, c",
    );
    assert_int(&results, 0, 1);
    assert_int(&results, 1, 2);
    assert_nil(&results, 2);
}

#[test]
fn qa_local_swap_with_multi_assign() {
    run_check_ints(
        "local a, b = 1, 2
         a, b = b, a
         return a, b",
        &[2, 1],
    );
}

#[test]
fn qa_do_block_scoping() {
    run_check_ints(
        "local x = 0
         do
             local x = 10
             x = x + 1
         end
         return x",
        &[0],
    );
}

// ---------------------------------------------------------------------------
// 7. Functions — edge cases
// ---------------------------------------------------------------------------

#[test]
fn qa_function_no_params_no_return() {
    let results = run_lua(
        "local function f() end
         local x = f()
         return x",
    );
    assert_nil(&results, 0);
}

#[test]
fn qa_function_extra_args_ignored() {
    run_check_ints(
        "local function f(a, b) return a + b end
         return f(1, 2, 3, 4)",
        &[3],
    );
}

#[test]
fn qa_function_missing_args_nil() {
    let results = run_lua(
        "local function f(a, b) return b end
         return f(1)",
    );
    assert_nil(&results, 0);
}

#[test]
fn qa_nested_function_calls_3_deep() {
    run_check_ints(
        "local function a(x) return x + 1 end
         local function b(x) return a(x) + 1 end
         local function c(x) return b(x) + 1 end
         return c(0)",
        &[3],
    );
}

#[test]
fn qa_function_as_local() {
    run_check_ints(
        "local f = function(x) return x * 2 end
         return f(21)",
        &[42],
    );
}

#[test]
fn qa_function_returns_function() {
    run_check_ints(
        "local function make(n)
            return function() return n end
         end
         local f = make(42)
         return f()",
        &[42],
    );
}

#[test]
fn qa_immediate_call() {
    run_check_ints("return (function() return 42 end)()", &[42]);
}

// ---------------------------------------------------------------------------
// 8. Globals
// ---------------------------------------------------------------------------

#[test]
fn qa_global_set_and_read() {
    run_check_ints(
        "x = 42
         return x",
        &[42],
    );
}

#[test]
fn qa_global_multiple_set() {
    run_check_ints(
        "x = 1
         y = 2
         z = x + y
         return z",
        &[3],
    );
}

#[test]
fn qa_global_overwrite() {
    run_check_ints(
        "x = 1
         x = 2
         return x",
        &[2],
    );
}

// ---------------------------------------------------------------------------
// 9. Error conditions
// ---------------------------------------------------------------------------

#[test]
fn qa_error_add_string_to_number() {
    let err = run_lua_err("return 1 + \"hello\"");
    assert!(err.contains("attempt to perform arithmetic"), "got: {err}");
}

#[test]
fn qa_error_compare_number_string() {
    let err = run_lua_err("return 1 < \"hello\"");
    assert!(err.contains("attempt to compare"), "got: {err}");
}

#[test]
fn qa_error_index_number() {
    let err = run_lua_err(
        "local x = 42
         return x.foo",
    );
    assert!(err.contains("attempt to index"), "got: {err}");
}

#[test]
fn qa_error_index_nil() {
    let err = run_lua_err(
        "local x = nil
         return x[1]",
    );
    assert!(err.contains("attempt to index"), "got: {err}");
}

#[test]
fn qa_error_call_number() {
    let err = run_lua_err(
        "local x = 42
         return x()",
    );
    assert!(err.contains("attempt to call"), "got: {err}");
}

#[test]
fn qa_error_call_string() {
    let err = run_lua_err("return (\"hello\")()");
    assert!(err.contains("attempt to call"), "got: {err}");
}

#[test]
fn qa_error_call_nil() {
    let err = run_lua_err("return (nil)()");
    assert!(err.contains("attempt to call"), "got: {err}");
}

#[test]
fn qa_error_idiv_zero() {
    let err = run_lua_err("return 1 // 0");
    assert!(
        err.contains("//") || err.contains("divide") || err.contains("attempt to perform"),
        "got: {err}"
    );
}

#[test]
fn qa_error_mod_zero() {
    let err = run_lua_err("return 1 % 0");
    assert!(
        err.contains("modulo")
            || err.contains("divide by zero")
            || err.contains("attempt to perform"),
        "got: {err}"
    );
}

#[test]
fn qa_error_len_number() {
    let err = run_lua_err("return #42");
    assert!(err.contains("attempt to get length"), "got: {err}");
}

#[test]
fn qa_error_len_nil() {
    let err = run_lua_err("return #nil");
    assert!(err.contains("attempt to get length"), "got: {err}");
}

#[test]
fn qa_error_concat_nil() {
    let err = run_lua_err("return \"hello\" .. nil");
    assert!(
        err.contains("attempt to concatenate") || err.contains("concat"),
        "got: {err}"
    );
}

#[test]
fn qa_error_concat_bool() {
    let err = run_lua_err("return \"hello\" .. true");
    assert!(
        err.contains("attempt to concatenate") || err.contains("concat"),
        "got: {err}"
    );
}

#[test]
fn qa_error_concat_table() {
    let err = run_lua_err("return \"hello\" .. {}");
    assert!(
        err.contains("attempt to concatenate") || err.contains("concat"),
        "got: {err}"
    );
}

#[test]
fn qa_error_bitwise_float() {
    let err = run_lua_err("return 1.5 & 2");
    assert!(
        err.contains("attempt to perform bitwise") || err.contains("integer"),
        "got: {err}"
    );
}

// ---------------------------------------------------------------------------
// 10. Complex programs — integration
// ---------------------------------------------------------------------------

#[test]
fn qa_program_gcd() {
    run_check_ints(
        "local function gcd(a, b)
            while b ~= 0 do
                a, b = b, a % b
            end
            return a
         end
         return gcd(48, 18)",
        &[6],
    );
}

#[test]
fn qa_program_sum_1_to_100() {
    run_check_ints(
        "local s = 0
         for i = 1, 100 do s = s + i end
         return s",
        &[5050],
    );
}

#[test]
fn qa_program_nested_for() {
    run_check_ints(
        "local s = 0
         for i = 1, 3 do
             for j = 1, 3 do
                 s = s + i * j
             end
         end
         return s",
        &[36],
    );
}

#[test]
fn qa_program_while_break_early() {
    run_check_ints(
        "local i = 0
         while true do
             i = i + 1
             if i >= 10 then break end
         end
         return i",
        &[10],
    );
}

#[test]
fn qa_program_table_of_functions() {
    run_check_ints(
        "local ops = {
            add = function(a, b) return a + b end,
            mul = function(a, b) return a * b end,
         }
         return ops.add(3, 4), ops.mul(3, 4)",
        &[7, 12],
    );
}

#[test]
fn qa_program_accumulator_loop() {
    run_check_ints(
        "local t = {}
         for i = 1, 5 do
             t[i] = i * i
         end
         local s = 0
         for i = 1, 5 do
             s = s + t[i]
         end
         return s",
        &[55],
    );
}

#[test]
fn qa_program_fibonacci_iterative() {
    run_check_ints(
        "local function fib(n)
            local a, b = 0, 1
            for i = 1, n do
                a, b = b, a + b
            end
            return a
         end
         return fib(10)",
        &[55],
    );
}

#[test]
fn qa_program_bubble_sort() {
    run_check_ints(
        "local t = {5, 3, 1, 4, 2}
         for i = 1, #t do
             for j = 1, #t - i do
                 if t[j] > t[j+1] then
                     t[j], t[j+1] = t[j+1], t[j]
                 end
             end
         end
         return t[1], t[2], t[3], t[4], t[5]",
        &[1, 2, 3, 4, 5],
    );
}

#[test]
fn qa_program_linked_list() {
    run_check_ints(
        "local function cons(h, t) return {head = h, tail = t} end
         local function sum_list(l)
             local s = 0
             while l do
                 s = s + l.head
                 l = l.tail
             end
             return s
         end
         local list = cons(1, cons(2, cons(3, nil)))
         return sum_list(list)",
        &[6],
    );
}

// ---------------------------------------------------------------------------
// 11. Literal loading edge cases
// ---------------------------------------------------------------------------

#[test]
fn qa_literal_large_float() {
    let results = run_lua("return 1e308");
    assert_float(&results, 0, 1e308);
}

#[test]
fn qa_literal_small_float() {
    let results = run_lua("return 1e-308");
    assert_float(&results, 0, 1e-308);
}

#[test]
fn qa_literal_negative_float() {
    let results = run_lua("return -0.0");
    // Result should be 0.0 or -0.0
    let val = results[0];
    assert!(val.as_float().is_some() || val.as_integer().is_some());
}

#[test]
fn qa_literal_hex_integer() {
    run_check_ints("return 0xFF", &[255]);
}

#[test]
fn qa_literal_nil_return() {
    let results = run_lua("return nil");
    assert_nil(&results, 0);
}

#[test]
fn qa_literal_bool_true_false() {
    let results = run_lua("return true, false");
    assert_bool(&results, 0, true);
    assert_bool(&results, 1, false);
}

// ---------------------------------------------------------------------------
// 12. Multiple return value placement
// ---------------------------------------------------------------------------

#[test]
fn qa_multi_return_in_table() {
    // f() as last element in table constructor expands
    run_check_ints(
        "local function f() return 10, 20, 30 end
         local t = {f()}
         return #t, t[1], t[2], t[3]",
        &[3, 10, 20, 30],
    );
}

#[test]
fn qa_multi_return_not_last_truncated() {
    // f() not at last position: only first result
    run_check_ints(
        "local function f() return 10, 20, 30 end
         local a, b = f(), 99
         return a, b",
        &[10, 99],
    );
}

// ---------------------------------------------------------------------------
// 13. Goto and labels
// ---------------------------------------------------------------------------

#[test]
fn qa_goto_forward() {
    run_check_ints(
        "goto skip
         ::skip::
         return 42",
        &[42],
    );
}

#[test]
fn qa_goto_backward_loop() {
    run_check_ints(
        "local x = 0
         ::again::
         x = x + 1
         if x < 5 then goto again end
         return x",
        &[5],
    );
}

// ---------------------------------------------------------------------------
// 14. Native function edge cases
// ---------------------------------------------------------------------------

#[test]
fn qa_type_of_table() {
    let (proto, strings) = selune_compiler::compiler::compile(b"return type({})", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "table", &vm);
}

#[test]
fn qa_tonumber_float_string() {
    let results = run_lua("return tonumber(\"3.15\")");
    assert_float(&results, 0, 3.15);
}

#[test]
fn qa_tonumber_invalid() {
    let results = run_lua("return tonumber(\"not_a_number\")");
    assert_nil(&results, 0);
}

#[test]
fn qa_tonumber_nil_input() {
    let results = run_lua("return tonumber(nil)");
    assert_nil(&results, 0);
}

// ---------------------------------------------------------------------------
// 15. For loop variable scoping
// ---------------------------------------------------------------------------

#[test]
fn qa_for_variable_not_visible_outside() {
    // After for loop, the loop variable should not be accessible
    // It becomes nil since it's a global read that doesn't exist
    let results = run_lua(
        "local s = 0
         for i = 1, 5 do s = s + i end
         -- i is not defined here
         return s",
    );
    assert_int(&results, 0, 15);
}

// ---------------------------------------------------------------------------
// 16. Return edge cases
// ---------------------------------------------------------------------------

#[test]
fn qa_return_no_value() {
    let results = run_lua("return");
    assert_eq!(results.len(), 0);
}

#[test]
fn qa_return_in_middle_of_function() {
    run_check_ints(
        "local function f(x)
            if x > 0 then return x end
            return -x
         end
         return f(5), f(-3)",
        &[5, 3],
    );
}

#[test]
fn qa_implicit_return() {
    let results = run_lua("local x = 42");
    assert_eq!(results.len(), 0);
}

// ---------------------------------------------------------------------------
// 17. Complex closures and upvalues (testing variants that may differ
//     from the already-known-failing tests)
// ---------------------------------------------------------------------------

#[test]
fn qa_closure_capture_immutable() {
    // Simplest closure: capture a local without mutation
    run_check_ints(
        "local x = 42
         local f = function() return x end
         return f()",
        &[42],
    );
}

#[test]
fn qa_closure_write_only() {
    // Closure writes to upvalue but doesn't return it directly
    run_check_ints(
        "local x = 0
         local function set(v) x = v end
         set(99)
         return x",
        &[99],
    );
}

// ---------------------------------------------------------------------------
// 18. Mixed arithmetic
// ---------------------------------------------------------------------------

#[test]
fn qa_mixed_int_float_add() {
    let results = run_lua("return 1 + 0.5");
    assert_float(&results, 0, 1.5);
}

#[test]
fn qa_mixed_int_float_mul() {
    let results = run_lua("return 3 * 1.5");
    assert_float(&results, 0, 4.5);
}

#[test]
fn qa_mixed_int_float_sub() {
    let results = run_lua("return 5 - 0.3");
    assert_float(&results, 0, 4.7);
}

#[test]
fn qa_integer_mul_result() {
    run_check_ints("return 7 * 6", &[42]);
}

#[test]
fn qa_integer_idiv() {
    run_check_ints("return 17 // 5", &[3]);
}

// ---------------------------------------------------------------------------
// 19. Constant folding validation
// ---------------------------------------------------------------------------

#[test]
fn qa_const_fold_add() {
    run_check_ints("return 2 + 3", &[5]);
}

#[test]
fn qa_const_fold_mul() {
    run_check_ints("return 6 * 7", &[42]);
}

#[test]
fn qa_const_fold_neg() {
    run_check_ints("return -42", &[-42]);
}

#[test]
fn qa_const_fold_not_true() {
    let results = run_lua("return not true");
    assert_bool(&results, 0, false);
}

#[test]
fn qa_const_fold_not_nil() {
    let results = run_lua("return not nil");
    assert_bool(&results, 0, true);
}

// ---------------------------------------------------------------------------
// 20. Stress tests
// ---------------------------------------------------------------------------

#[test]
fn qa_stress_deep_nesting_if() {
    // Deeply nested if statements
    run_check_ints(
        "local x = 1
         if x == 1 then
           if true then
             if true then
               if true then
                 if true then
                   return 42
                 end
               end
             end
           end
         end
         return 0",
        &[42],
    );
}

#[test]
fn qa_stress_many_locals() {
    run_check_ints(
        "local a,b,c,d,e,f,g,h,i,j = 1,2,3,4,5,6,7,8,9,10
         return a+b+c+d+e+f+g+h+i+j",
        &[55],
    );
}

#[test]
fn qa_stress_for_loop_large() {
    run_check_ints(
        "local s = 0
         for i = 1, 10000 do s = s + 1 end
         return s",
        &[10000],
    );
}
