use super::helpers::*;

// ==========================================================================
// 1A. Literals & Number Parsing (from testes/literals.lua)
// ==========================================================================

#[test]
fn conformance_integer_type() {
    run_check_strings("return type(3)", &["number"]);
}

#[test]
fn conformance_float_type() {
    run_check_strings("return type(3.0)", &["number"]);
}

#[test]
fn conformance_math_type_integer() {
    run_check_strings("return math.type(3)", &["integer"]);
}

#[test]
fn conformance_math_type_float() {
    run_check_strings("return math.type(3.0)", &["float"]);
}

#[test]
fn conformance_cross_type_equality() {
    run_lua(r#"assert(3 == 3.0)"#);
}

#[test]
fn conformance_cross_type_inequality() {
    run_lua(r#"assert(not (3 ~= 3.0))"#);
}

#[test]
fn conformance_hex_float_basic() {
    run_lua(r#"assert(0x1p4 == 16.0)"#);
}

#[test]
fn conformance_hex_float_fraction() {
    run_lua(r#"assert(0x0.1E == 0x1E / 256.0)"#);
}

#[test]
fn conformance_escape_sequences() {
    run_lua(r#"assert("\x41" == "A")"#);
}

#[test]
fn conformance_unicode_escape() {
    run_lua(r#"assert("\u{41}" == "A")"#);
}

#[test]
fn conformance_escape_a_b_f() {
    run_lua(r#"assert(string.byte("\a") == 7)"#);
}

#[test]
fn conformance_escape_backslash() {
    run_lua(r#"assert(string.byte("\\") == 92)"#);
}

#[test]
fn conformance_max_integer() {
    run_lua("assert(math.maxinteger == 0x7fffffffffffffff)");
}

#[test]
fn conformance_min_integer() {
    run_lua("assert(math.mininteger == -0x7fffffffffffffff - 1)");
}

#[test]
fn conformance_integer_hex_literal() {
    run_check_ints("return 0xff", &[255]);
}

#[test]
fn conformance_integer_hex_upper() {
    run_check_ints("return 0xFF", &[255]);
}

#[test]
fn conformance_float_scientific() {
    run_check_floats("return 1e2", &[100.0]);
}

#[test]
fn conformance_float_scientific_neg_exp() {
    run_check_floats("return 1e-2", &[0.01]);
}

#[test]
fn conformance_long_string_no_escapes() {
    run_check_strings(r#"return [[hello\nworld]]"#, &["hello\\nworld"]);
}

#[test]
fn conformance_decimal_escape() {
    run_lua(r#"assert("\65" == "A")"#);
}

#[test]
fn conformance_zero_literal() {
    run_lua("assert(type(0) == 'number')");
    run_lua("assert(math.type(0) == 'integer')");
}

#[test]
fn conformance_float_zero() {
    run_lua("assert(math.type(0.0) == 'float')");
}

#[test]
fn conformance_negative_zero_float() {
    run_lua("assert(-0.0 == 0.0)");
}

#[test]
fn conformance_large_hex_integer() {
    run_check_ints("return 0x7FFFFFFFFFFFFFFF", &[i64::MAX]);
}

// ==========================================================================
// 1B. Constructs / Control Flow (from testes/constructs.lua)
// ==========================================================================

#[test]
fn conformance_repeat_until_local_visible() {
    run_lua(
        r#"
        do
            local a = 1
            repeat
                local b = a
                a = a + 1
            until b == 3
            assert(a == 4)
        end
        "#,
    );
}

#[test]
fn conformance_break_in_nested_loops() {
    run_lua(
        r#"
        local sum = 0
        for i = 1, 10 do
            for j = 1, 10 do
                if j > i then break end
                sum = sum + 1
            end
        end
        assert(sum == 55)
        "#,
    );
}

#[test]
fn conformance_multiple_assignment_swap() {
    run_lua(
        r#"
        local x, y = 1, 2
        x, y = y, x
        assert(x == 2 and y == 1)
        "#,
    );
}

#[test]
fn conformance_while_false_body_not_executed() {
    run_lua(
        r#"
        local x = 0
        while false do x = x + 1 end
        assert(x == 0)
        "#,
    );
}

#[test]
fn conformance_repeat_executes_at_least_once() {
    run_lua(
        r#"
        local x = 0
        repeat x = x + 1 until true
        assert(x == 1)
        "#,
    );
}

#[test]
fn conformance_for_loop_step() {
    run_lua(
        r#"
        local sum = 0
        for i = 10, 1, -1 do sum = sum + i end
        assert(sum == 55)
        "#,
    );
}

#[test]
fn conformance_for_loop_no_execution() {
    run_lua(
        r#"
        local x = 0
        for i = 1, 0 do x = x + 1 end
        assert(x == 0)
        "#,
    );
}

#[test]
fn conformance_for_loop_negative_step_no_execution() {
    run_lua(
        r#"
        local x = 0
        for i = 0, 1, -1 do x = x + 1 end
        assert(x == 0)
        "#,
    );
}

#[test]
fn conformance_if_elseif_else() {
    run_lua(
        r#"
        local function classify(n)
            if n > 0 then return "positive"
            elseif n < 0 then return "negative"
            else return "zero"
            end
        end
        assert(classify(5) == "positive")
        assert(classify(-3) == "negative")
        assert(classify(0) == "zero")
        "#,
    );
}

#[test]
fn conformance_nested_if() {
    run_lua(
        r#"
        local x = 10
        local result
        if x > 5 then
            if x > 15 then
                result = "big"
            else
                result = "medium"
            end
        else
            result = "small"
        end
        assert(result == "medium")
        "#,
    );
}

#[test]
fn conformance_do_block_scoping() {
    run_lua(
        r#"
        local x = 1
        do
            local x = 2
            assert(x == 2)
        end
        assert(x == 1)
        "#,
    );
}

#[test]
fn conformance_and_or_short_circuit() {
    run_lua(
        r#"
        local a = nil
        local b = a and a.x  -- should not error because short-circuits
        assert(b == nil)
        "#,
    );
}

#[test]
fn conformance_or_default_idiom() {
    run_lua(
        r#"
        local x = nil
        local y = x or 42
        assert(y == 42)
        local z = false or "hello"
        assert(z == "hello")
        local w = 0 or "nope"
        assert(w == 0)  -- 0 is truthy in Lua
        "#,
    );
}

#[test]
fn conformance_ternary_idiom() {
    run_lua(
        r#"
        local function ternary(cond, t, f)
            return cond and t or f
        end
        assert(ternary(true, "yes", "no") == "yes")
        assert(ternary(false, "yes", "no") == "no")
        "#,
    );
}

#[test]
fn conformance_numeric_for_float() {
    run_lua(
        r#"
        local count = 0
        for i = 0.0, 1.0, 0.5 do
            count = count + 1
        end
        assert(count == 3)
        "#,
    );
}

#[test]
fn conformance_multiple_returns_in_assignment() {
    run_lua(
        r#"
        local function f() return 1, 2, 3 end
        local a, b, c, d = f()
        assert(a == 1 and b == 2 and c == 3 and d == nil)
        "#,
    );
}

#[test]
fn conformance_assignment_excess_lhs() {
    run_lua(
        r#"
        local a, b, c = 1
        assert(a == 1 and b == nil and c == nil)
        "#,
    );
}

#[test]
fn conformance_empty_for_body() {
    run_lua(
        r#"
        local sum = 0
        for i = 1, 100 do sum = sum + i end
        assert(sum == 5050)
        "#,
    );
}

// ==========================================================================
// 1C. Functions & Calls (from testes/calls.lua)
// ==========================================================================

#[test]
fn conformance_multireturn_truncated_not_last() {
    run_lua(
        r#"
        local function f() return 1, 2, 3 end
        local a, b = f(), "x"
        assert(a == 1 and b == "x")
        "#,
    );
}

#[test]
fn conformance_multireturn_expanded_in_table_last() {
    run_lua(
        r#"
        local function f() return 1, 2, 3 end
        local t = {f()}
        assert(#t == 3 and t[1] == 1 and t[2] == 2 and t[3] == 3)
        "#,
    );
}

#[test]
fn conformance_multireturn_truncated_in_table_not_last() {
    run_lua(
        r#"
        local function f() return 1, 2, 3 end
        local t = {f(), "x"}
        assert(#t == 2 and t[1] == 1 and t[2] == "x")
        "#,
    );
}

#[test]
fn conformance_parentheses_force_single() {
    run_lua(
        r#"
        local function f() return 1, 2, 3 end
        local a, b = (f())
        assert(a == 1 and b == nil)
        "#,
    );
}

#[test]
fn conformance_tail_call_no_stack_overflow() {
    run_lua(
        r#"
        local function recurse(n) if n > 0 then return recurse(n-1) else return 0 end end
        assert(recurse(1000000) == 0)
        "#,
    );
}

#[test]
fn conformance_select_with_multireturn() {
    run_lua(
        r#"
        local function f() return 10, 20, 30 end
        assert(select(2, f()) == 20)
        assert(select('#', f()) == 3)
        "#,
    );
}

#[test]
fn conformance_select_hash() {
    run_lua(
        r#"
        assert(select('#') == 0)
        assert(select('#', 1) == 1)
        assert(select('#', 1, 2, 3) == 3)
        assert(select('#', nil, nil) == 2)
        "#,
    );
}

#[test]
fn conformance_method_call_colon() {
    run_lua(
        r#"
        local t = {x = 10}
        function t:getx() return self.x end
        assert(t:getx() == 10)
        "#,
    );
}

#[test]
fn conformance_function_as_value() {
    run_lua(
        r#"
        local function apply(f, x) return f(x) end
        local function double(x) return x * 2 end
        assert(apply(double, 5) == 10)
        "#,
    );
}

#[test]
fn conformance_immediate_call() {
    run_lua(
        r#"
        local x = (function(a, b) return a + b end)(3, 4)
        assert(x == 7)
        "#,
    );
}

#[test]
fn conformance_no_return_gives_nil() {
    run_lua(
        r#"
        local function f() end
        local a = f()
        assert(a == nil)
        "#,
    );
}

#[test]
fn conformance_recursive_factorial() {
    run_lua(
        r#"
        local function fact(n)
            if n <= 1 then return 1 end
            return n * fact(n - 1)
        end
        assert(fact(10) == 3628800)
        "#,
    );
}

#[test]
fn conformance_mutual_recursion() {
    run_lua(
        r#"
        local is_even, is_odd
        is_even = function(n)
            if n == 0 then return true end
            return is_odd(n - 1)
        end
        is_odd = function(n)
            if n == 0 then return false end
            return is_even(n - 1)
        end
        assert(is_even(10) == true)
        assert(is_odd(7) == true)
        "#,
    );
}

#[test]
fn conformance_string_call_syntax() {
    run_lua(
        r#"
        local function f(s) return s end
        assert(f "hello" == "hello")
        "#,
    );
}

#[test]
fn conformance_table_call_syntax() {
    run_lua(
        r#"
        local function f(t) return t[1] end
        assert(f {42} == 42)
        "#,
    );
}

#[test]
fn conformance_multireturn_in_return() {
    run_lua(
        r#"
        local function f() return 1, 2, 3 end
        local function g() return f() end
        local a, b, c = g()
        assert(a == 1 and b == 2 and c == 3)
        "#,
    );
}

#[test]
fn conformance_multireturn_in_call_arg() {
    run_lua(
        r#"
        local function f() return 10, 20 end
        local function g(a, b) return a + b end
        assert(g(f()) == 30)
        "#,
    );
}

#[test]
fn conformance_multireturn_in_call_arg_not_last() {
    run_lua(
        r#"
        local function f() return 10, 20 end
        local function g(a, b, c) return a, b, c end
        local a, b, c = g(f(), 30)
        assert(a == 10 and b == 30 and c == nil)
        "#,
    );
}

#[test]
fn conformance_zero_arg_function() {
    run_lua(
        r#"
        local function f() return 42 end
        assert(f() == 42)
        "#,
    );
}

#[test]
fn conformance_many_args() {
    run_lua(
        r#"
        local function f(a,b,c,d,e,f2,g,h)
            return a+b+c+d+e+f2+g+h
        end
        assert(f(1,2,3,4,5,6,7,8) == 36)
        "#,
    );
}

// ==========================================================================
// 1D. Closures & Upvalues (from testes/closure.lua)
// ==========================================================================

#[test]
fn conformance_loop_closure_capture() {
    run_lua(
        r#"
        local closures = {}
        for i = 1, 5 do
            closures[i] = function() return i end
        end
        assert(closures[1]() == 1)
        assert(closures[3]() == 3)
        assert(closures[5]() == 5)
        "#,
    );
}

#[test]
fn conformance_shared_upvalue() {
    run_lua(
        r#"
        local function make()
            local x = 0
            local function inc() x = x + 1 end
            local function get() return x end
            return inc, get
        end
        local inc, get = make()
        inc(); inc(); inc()
        assert(get() == 3)
        "#,
    );
}

#[test]
fn conformance_upvalue_closing() {
    run_lua(
        r#"
        local result = 0
        do
            local x = 10
            local function f() return x end
            result = f()
        end
        assert(result == 10)
        "#,
    );
}

#[test]
fn conformance_deep_nested_upvalue() {
    run_lua(
        r#"
        local function a()
            local x = 1
            return function()
                return function()
                    return function() return x end
                end
            end
        end
        assert(a()()()() == 1)
        "#,
    );
}

#[test]
fn conformance_closure_as_counter() {
    run_lua(
        r#"
        local function counter(start)
            local n = start
            return function()
                n = n + 1
                return n
            end
        end
        local c = counter(0)
        assert(c() == 1)
        assert(c() == 2)
        assert(c() == 3)
        "#,
    );
}

#[test]
fn conformance_closure_captures_mutable() {
    run_lua(
        r#"
        local x = 10
        local function get() return x end
        local function set(v) x = v end
        set(42)
        assert(get() == 42)
        assert(x == 42)
        "#,
    );
}

#[test]
fn conformance_closure_in_table() {
    run_lua(
        r#"
        local function make_obj()
            local val = 0
            return {
                set = function(v) val = v end,
                get = function() return val end
            }
        end
        local obj = make_obj()
        obj.set(99)
        assert(obj.get() == 99)
        "#,
    );
}

#[test]
fn conformance_closure_over_loop_var_while() {
    run_lua(
        r#"
        local fns = {}
        local i = 0
        while i < 3 do
            i = i + 1
            local x = i
            fns[i] = function() return x end
        end
        assert(fns[1]() == 1)
        assert(fns[2]() == 2)
        assert(fns[3]() == 3)
        "#,
    );
}

#[test]
fn conformance_upvalue_in_repeat() {
    run_lua(
        r#"
        local f
        local n = 0
        repeat
            n = n + 1
            if n == 3 then
                local captured = n
                f = function() return captured end
            end
        until n >= 5
        assert(f() == 3)
        "#,
    );
}

#[test]
fn conformance_multiple_closures_same_upvalue() {
    run_lua(
        r#"
        local function make()
            local x = 0
            local function a() x = x + 1 end
            local function b() x = x + 10 end
            local function c() return x end
            return a, b, c
        end
        local a, b, c = make()
        a(); a(); b()
        assert(c() == 12)
        "#,
    );
}

#[test]
fn conformance_closure_over_param() {
    run_lua(
        r#"
        local function make(x)
            return function() return x end
        end
        local f1 = make(10)
        local f2 = make(20)
        assert(f1() == 10)
        assert(f2() == 20)
        "#,
    );
}

// ==========================================================================
// 1E. Varargs (from testes/vararg.lua)
// ==========================================================================

#[test]
fn conformance_basic_vararg() {
    run_lua(
        r#"
        local function f(...) return ... end
        local a, b, c = f(1, 2, 3)
        assert(a == 1 and b == 2 and c == 3)
        "#,
    );
}

#[test]
fn conformance_select_count_vararg() {
    run_lua(
        r#"
        local function count(...) return select('#', ...) end
        assert(count() == 0)
        assert(count(1) == 1)
        assert(count(nil, nil, nil) == 3)
        assert(count(1, nil) == 2)
        "#,
    );
}

#[test]
fn conformance_vararg_in_table() {
    run_lua(
        r#"
        local function pack(...) return {...} end
        local t = pack(10, 20, 30)
        assert(#t == 3 and t[2] == 20)
        "#,
    );
}

#[test]
fn conformance_vararg_forwarding() {
    run_lua(
        r#"
        local function f(...) return ... end
        local function g(...) return f(...) end
        local a, b = g(10, 20)
        assert(a == 10 and b == 20)
        "#,
    );
}

#[test]
fn conformance_table_pack() {
    run_lua(
        r#"
        local t = table.pack(1, nil, 3)
        assert(t.n == 3 and t[1] == 1 and t[2] == nil and t[3] == 3)
        "#,
    );
}

#[test]
fn conformance_table_unpack() {
    run_lua(
        r#"
        local a, b, c = table.unpack({10, 20, 30})
        assert(a == 10 and b == 20 and c == 30)
        "#,
    );
}

#[test]
fn conformance_table_unpack_range() {
    run_lua(
        r#"
        local a, b = table.unpack({10, 20, 30, 40}, 2, 3)
        assert(a == 20 and b == 30)
        "#,
    );
}

#[test]
fn conformance_vararg_empty() {
    run_lua(
        r#"
        local function f(...) return select('#', ...) end
        assert(f() == 0)
        "#,
    );
}

#[test]
fn conformance_vararg_with_named_params() {
    run_lua(
        r#"
        local function f(a, b, ...)
            return a, b, select('#', ...)
        end
        local a, b, c = f(1, 2, 3, 4, 5)
        assert(a == 1 and b == 2 and c == 3)
        "#,
    );
}

#[test]
#[ignore] // WONTFIX: PUC Lua 5.4 does not allow nested functions to access outer '...' (compile error)
fn conformance_vararg_nested() {
    run_lua(
        r#"
        local function outer(...)
            local function inner()
                return ...
            end
            return inner()
        end
        local a, b = outer(10, 20)
        assert(a == 10 and b == 20)
        "#,
    );
}

#[test]
fn conformance_select_with_index() {
    run_lua(
        r#"
        local function f() return 10, 20, 30, 40 end
        assert(select(1, f()) == 10)
        assert(select(3, f()) == 30)
        assert(select(-1, f()) == 40)
        "#,
    );
}

#[test]
fn conformance_vararg_single_nil() {
    run_lua(
        r#"
        local function f(...) return select('#', ...) end
        assert(f(nil) == 1)
        "#,
    );
}

// ==========================================================================
// 1F. Goto & Labels (from testes/goto.lua)
// ==========================================================================

#[test]
fn conformance_goto_forward() {
    run_lua(
        r#"
        goto L1
        ::L1::
        assert(true)
        "#,
    );
}

#[test]
fn conformance_goto_loop() {
    run_lua(
        r#"
        local x = 0
        ::redo::
        x = x + 1
        if x < 3 then goto redo end
        assert(x == 3)
        "#,
    );
}

#[test]
fn conformance_goto_nested_blocks() {
    run_lua(
        r#"
        local result = 0
        do
            do
                goto skip
            end
            result = 999
            ::skip::
        end
        assert(result == 0)
        "#,
    );
}

#[test]
fn conformance_goto_skip_code() {
    run_lua(
        r#"
        local x = 1
        goto done
        x = 2
        ::done::
        assert(x == 1)
        "#,
    );
}

#[test]
fn conformance_multiple_labels() {
    run_lua(
        r#"
        local x = 0
        goto first
        ::second::
        x = x + 10
        goto done
        ::first::
        x = x + 1
        goto second
        ::done::
        assert(x == 11)
        "#,
    );
}

#[test]
fn conformance_goto_in_if() {
    run_lua(
        r#"
        local x = 0
        if true then
            goto skip
        end
        x = 1
        ::skip::
        assert(x == 0)
        "#,
    );
}

#[test]
fn conformance_continue_pattern_with_goto() {
    run_lua(
        r#"
        local sum = 0
        for i = 1, 10 do
            if i % 2 == 0 then goto continue end
            sum = sum + i
            ::continue::
        end
        assert(sum == 25)  -- 1+3+5+7+9
        "#,
    );
}

// ==========================================================================
// 1G. Math Library (from testes/math.lua)
// ==========================================================================

#[test]
fn conformance_math_type_of_arithmetic() {
    run_lua(
        r#"
        assert(math.type(3 + 4) == "integer")
        assert(math.type(3.0 + 4.0) == "float")
        "#,
    );
}

#[test]
fn conformance_division_always_float() {
    run_lua(r#"assert(math.type(6 / 2) == "float")"#);
}

#[test]
fn conformance_floor_div_integer() {
    run_lua(r#"assert(math.type(7 // 2) == "integer")"#);
}

#[test]
fn conformance_math_tointeger() {
    run_lua(
        r#"
        assert(math.tointeger(5.0) == 5)
        assert(math.tointeger(5.1) == nil)
        assert(math.tointeger("x") == nil)
        "#,
    );
}

#[test]
fn conformance_math_huge() {
    run_lua(
        r#"
        assert(math.huge == 1/0)
        assert(-math.huge == -1/0)
        assert(math.huge == math.huge)
        "#,
    );
}

#[test]
fn conformance_nan_not_equal() {
    run_lua(
        r#"
        local nan = 0/0
        assert(nan ~= nan)
        assert(not (nan == nan))
        assert(not (nan < nan))
        assert(not (nan <= nan))
        assert(not (nan > nan))
        assert(not (nan >= nan))
        "#,
    );
}

#[test]
fn conformance_math_type_non_number() {
    run_lua(
        r#"
        assert(math.type("hello") == false)
        assert(math.type(true) == false)
        assert(math.type(nil) == false)
        assert(math.type({}) == false)
        "#,
    );
}

#[test]
fn conformance_integer_overflow_wrap() {
    run_lua("assert(math.maxinteger + 1 == math.mininteger)");
}

#[test]
fn conformance_integer_underflow_wrap() {
    run_lua("assert(math.mininteger - 1 == math.maxinteger)");
}

#[test]
fn conformance_power_always_float() {
    run_lua(r#"assert(math.type(2 ^ 3) == "float")"#);
}

#[test]
fn conformance_math_abs() {
    run_lua(
        r#"
        assert(math.abs(-5) == 5)
        assert(math.abs(5) == 5)
        assert(math.abs(-3.14) == 3.14)
        "#,
    );
}

#[test]
fn conformance_math_ceil_floor() {
    run_lua(
        r#"
        assert(math.ceil(3.2) == 4)
        assert(math.ceil(-3.2) == -3)
        assert(math.floor(3.8) == 3)
        assert(math.floor(-3.8) == -4)
        "#,
    );
}

#[test]
fn conformance_math_max_min() {
    run_lua(
        r#"
        assert(math.max(1, 2, 3) == 3)
        assert(math.min(1, 2, 3) == 1)
        assert(math.max(-1, -2, -3) == -1)
        assert(math.min(-1, -2, -3) == -3)
        "#,
    );
}

#[test]
fn conformance_math_sqrt() {
    run_lua(
        r#"
        assert(math.sqrt(4) == 2.0)
        assert(math.sqrt(9) == 3.0)
        assert(math.sqrt(0) == 0.0)
        "#,
    );
}

#[test]
fn conformance_math_pi() {
    run_lua(
        r#"
        assert(math.pi > 3.14 and math.pi < 3.15)
        "#,
    );
}

#[test]
fn conformance_math_sin_cos() {
    run_lua(
        r#"
        assert(math.abs(math.sin(0)) < 1e-10)
        assert(math.abs(math.cos(0) - 1) < 1e-10)
        assert(math.abs(math.sin(math.pi/2) - 1) < 1e-10)
        "#,
    );
}

#[test]
fn conformance_math_integer_returns() {
    // math.ceil/floor return integers in Lua 5.4
    run_lua(
        r#"
        assert(math.type(math.ceil(3.2)) == "integer")
        assert(math.type(math.floor(3.8)) == "integer")
        "#,
    );
}

#[test]
fn conformance_tonumber_base() {
    run_lua(
        r#"
        assert(tonumber("ff", 16) == 255)
        assert(tonumber("77", 8) == 63)
        assert(tonumber("11", 2) == 3)
        assert(tonumber("10", 10) == 10)
        "#,
    );
}

// ==========================================================================
// 1H. String Library (from testes/strings.lua + testes/pm.lua)
// ==========================================================================

#[test]
fn conformance_string_format_int() {
    run_lua(
        r#"
        assert(string.format("%d", 42) == "42")
        assert(string.format("%05d", 42) == "00042")
        assert(string.format("%x", 255) == "ff")
        assert(string.format("%o", 8) == "10")
        "#,
    );
}

#[test]
fn conformance_string_format_float() {
    run_lua(r#"assert(string.format("%.2f", 3.14159) == "3.14")"#);
}

#[test]
fn conformance_string_format_string() {
    run_lua(r#"assert(string.format("%s", "hello") == "hello")"#);
}

#[test]
fn conformance_string_find_basic() {
    run_lua(
        r#"
        assert(string.find("hello", "ell") == 2)
        assert(string.find("hello", "xyz") == nil)
        "#,
    );
}

#[test]
fn conformance_string_match_captures() {
    run_lua(
        r#"
        local y, m, d = string.match("2024-01-15", "(%d+)-(%d+)-(%d+)")
        assert(y == "2024" and m == "01" and d == "15")
        "#,
    );
}

#[test]
fn conformance_string_gsub_function() {
    run_lua(
        r#"
        local s = string.gsub("hello world", "%w+", string.upper)
        assert(s == "HELLO WORLD")
        "#,
    );
}

#[test]
fn conformance_string_gmatch() {
    run_lua(
        r#"
        local words = {}
        for w in string.gmatch("one two three", "%w+") do
            words[#words + 1] = w
        end
        assert(#words == 3 and words[1] == "one" and words[3] == "three")
        "#,
    );
}

#[test]
fn conformance_string_find_anchored() {
    run_lua(
        r#"
        assert(string.find("hello", "^hell") == 1)
        assert(string.find("hello", "llo$") == 3)
        assert(string.find("hello", "^hello$") == 1)
        assert(string.find("hello world", "^hello$") == nil)
        "#,
    );
}

#[test]
fn conformance_string_find_empty() {
    run_lua(
        r#"
        assert(string.find("", "") == 1)
        assert(string.find("abc", "") == 1)
        "#,
    );
}

#[test]
fn conformance_string_gsub_empty_pattern() {
    run_lua(
        r#"
        assert(string.gsub("abc", "", "x") == "xaxbxcx")
        "#,
    );
}

#[test]
fn conformance_string_len() {
    run_lua(
        r#"
        assert(string.len("hello") == 5)
        assert(string.len("") == 0)
        assert(#"hello" == 5)
        "#,
    );
}

#[test]
fn conformance_string_sub() {
    run_lua(
        r#"
        assert(string.sub("hello", 2, 4) == "ell")
        assert(string.sub("hello", 2) == "ello")
        assert(string.sub("hello", -3) == "llo")
        "#,
    );
}

#[test]
fn conformance_string_rep() {
    run_lua(
        r#"
        assert(string.rep("ab", 3) == "ababab")
        assert(string.rep("ab", 3, "-") == "ab-ab-ab")
        assert(string.rep("x", 0) == "")
        "#,
    );
}

#[test]
fn conformance_string_reverse() {
    run_lua(
        r#"
        assert(string.reverse("hello") == "olleh")
        assert(string.reverse("") == "")
        assert(string.reverse("a") == "a")
        "#,
    );
}

#[test]
fn conformance_string_upper_lower() {
    run_lua(
        r#"
        assert(string.upper("hello") == "HELLO")
        assert(string.lower("HELLO") == "hello")
        "#,
    );
}

#[test]
fn conformance_string_byte_char() {
    run_lua(
        r#"
        assert(string.byte("A") == 65)
        assert(string.char(65) == "A")
        assert(string.byte("hello", 2) == 101)
        "#,
    );
}

#[test]
fn conformance_string_gsub_count() {
    run_lua(
        r#"
        local s, n = string.gsub("hello hello hello", "hello", "world")
        assert(s == "world world world" and n == 3)
        "#,
    );
}

#[test]
fn conformance_string_gsub_limit() {
    run_lua(
        r#"
        local s, n = string.gsub("aaa", "a", "b", 2)
        assert(s == "bba" and n == 2)
        "#,
    );
}

#[test]
fn conformance_string_match_no_capture() {
    run_lua(
        r#"
        assert(string.match("hello123", "%d+") == "123")
        assert(string.match("hello", "%d+") == nil)
        "#,
    );
}

#[test]
fn conformance_pattern_classes() {
    run_lua(
        r#"
        assert(string.match("abc123", "%a+") == "abc")
        assert(string.match("abc123", "%d+") == "123")
        assert(string.match("  hello  ", "%S+") == "hello")
        assert(string.match("  hello  ", "^%s+") == "  ")
        "#,
    );
}

#[test]
fn conformance_string_gsub_table_replacement() {
    run_lua(
        r#"
        local t = {a = "1", b = "2"}
        local s = string.gsub("a-b-c", "%a", t)
        assert(s == "1-2-c")
        "#,
    );
}

#[test]
fn conformance_string_format_percent() {
    run_lua(r#"assert(string.format("%%") == "%")"#);
}

#[test]
fn conformance_string_format_multiple() {
    run_lua(
        r#"
        assert(string.format("%d + %d = %d", 1, 2, 3) == "1 + 2 = 3")
        "#,
    );
}

// ==========================================================================
// 1I. Table Library (from testes/sort.lua, testes/nextvar.lua)
// ==========================================================================

#[test]
fn conformance_next_iteration() {
    run_lua(
        r#"
        local t = {a=1, b=2, c=3}
        local count = 0
        local k = nil
        repeat
            k = next(t, k)
            if k then count = count + 1 end
        until not k
        assert(count == 3)
        "#,
    );
}

#[test]
fn conformance_table_sort_basic() {
    run_lua(
        r#"
        local t = {3, 1, 4, 1, 5, 9, 2, 6}
        table.sort(t)
        assert(t[1] == 1 and t[2] == 1 and t[3] == 2 and t[8] == 9)
        "#,
    );
}

#[test]
fn conformance_table_sort_comparator() {
    run_lua(
        r#"
        local t = {3, 1, 4, 1, 5, 9, 2, 6}
        table.sort(t, function(a, b) return a > b end)
        assert(t[1] == 9 and t[8] == 1)
        "#,
    );
}

#[test]
fn conformance_table_sort_empty() {
    run_lua(
        r#"
        local t = {}
        table.sort(t)
        "#,
    );
}

#[test]
fn conformance_table_sort_single() {
    run_lua(
        r#"
        local t = {1}
        table.sort(t)
        assert(t[1] == 1)
        "#,
    );
}

#[test]
fn conformance_table_concat_basic() {
    run_lua(
        r#"
        assert(table.concat({1, 2, 3}, ", ") == "1, 2, 3")
        assert(table.concat({}, ", ") == "")
        assert(table.concat({"a"}, "-") == "a")
        "#,
    );
}

#[test]
fn conformance_table_move() {
    run_lua(
        r#"
        local t = {1, 2, 3, 4, 5}
        table.move(t, 3, 5, 1)
        assert(t[1] == 3 and t[2] == 4 and t[3] == 5)
        "#,
    );
}

#[test]
fn conformance_table_insert_remove() {
    run_lua(
        r#"
        local t = {1, 2, 3}
        table.insert(t, 4)
        assert(#t == 4 and t[4] == 4)
        table.insert(t, 2, 10)
        assert(t[2] == 10 and t[3] == 2)
        table.remove(t, 2)
        assert(t[2] == 2)
        "#,
    );
}

#[test]
fn conformance_ipairs_basic() {
    run_lua(
        r#"
        local t = {10, 20, 30}
        local sum = 0
        for i, v in ipairs(t) do
            sum = sum + v
        end
        assert(sum == 60)
        "#,
    );
}

#[test]
fn conformance_pairs_basic() {
    run_lua(
        r#"
        local t = {a=1, b=2, c=3}
        local sum = 0
        for k, v in pairs(t) do
            sum = sum + v
        end
        assert(sum == 6)
        "#,
    );
}

#[test]
fn conformance_next_empty_table() {
    run_lua("assert(next({}) == nil)");
}

#[test]
fn conformance_table_length_sequence() {
    run_lua(
        r#"
        assert(#{} == 0)
        assert(#{1, 2, 3} == 3)
        assert(#{1, 2, 3, 4, 5} == 5)
        "#,
    );
}

#[test]
fn conformance_table_concat_range() {
    run_lua(
        r#"
        local t = {"a", "b", "c", "d", "e"}
        assert(table.concat(t, "-", 2, 4) == "b-c-d")
        "#,
    );
}

// ==========================================================================
// 1J. Coroutines (from testes/coroutine.lua)
// ==========================================================================

#[test]
fn conformance_yield_from_nested_call() {
    run_lua(
        r#"
        local function inner() return coroutine.yield(42) end
        local function outer() return inner() end
        local co = coroutine.create(outer)
        local ok, v = coroutine.resume(co)
        assert(ok and v == 42)
        local ok2, v2 = coroutine.resume(co, 100)
        assert(ok2 and v2 == 100)
        "#,
    );
}

#[test]
fn conformance_wrap_error_propagation() {
    run_lua(
        r#"
        local f = coroutine.wrap(function() error("boom") end)
        local ok, err = pcall(f)
        assert(not ok)
        "#,
    );
}

#[test]
fn conformance_multiple_coroutines_interleaved() {
    run_lua(
        r#"
        local co1 = coroutine.create(function() coroutine.yield(1); return 2 end)
        local co2 = coroutine.create(function() coroutine.yield(3); return 4 end)
        local _, a = coroutine.resume(co1)
        local _, b = coroutine.resume(co2)
        local _, c = coroutine.resume(co1)
        local _, d = coroutine.resume(co2)
        assert(a == 1 and b == 3 and c == 2 and d == 4)
        "#,
    );
}

#[test]
fn conformance_coroutine_status() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            coroutine.yield()
        end)
        assert(coroutine.status(co) == "suspended")
        coroutine.resume(co)
        assert(coroutine.status(co) == "suspended")
        coroutine.resume(co)
        assert(coroutine.status(co) == "dead")
        "#,
    );
}

#[test]
fn conformance_coroutine_wrap_basic() {
    run_lua(
        r#"
        local gen = coroutine.wrap(function()
            coroutine.yield(1)
            coroutine.yield(2)
            return 3
        end)
        assert(gen() == 1)
        assert(gen() == 2)
        assert(gen() == 3)
        "#,
    );
}

#[test]
fn conformance_coroutine_resume_dead() {
    run_lua(
        r#"
        local co = coroutine.create(function() return 42 end)
        local ok1, v1 = coroutine.resume(co)
        assert(ok1 and v1 == 42)
        local ok2, msg = coroutine.resume(co)
        assert(not ok2)
        "#,
    );
}

#[test]
fn conformance_coroutine_yield_multiple_values() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            coroutine.yield(1, 2, 3)
        end)
        local ok, a, b, c = coroutine.resume(co)
        assert(ok and a == 1 and b == 2 and c == 3)
        "#,
    );
}

#[test]
fn conformance_coroutine_resume_passes_values() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            local a, b = coroutine.yield()
            return a + b
        end)
        coroutine.resume(co)
        local ok, result = coroutine.resume(co, 10, 20)
        assert(ok and result == 30)
        "#,
    );
}

#[test]
fn conformance_coroutine_producer_consumer() {
    run_lua(
        r#"
        local function producer()
            return coroutine.wrap(function()
                for i = 1, 5 do
                    coroutine.yield(i * 10)
                end
            end)
        end
        local sum = 0
        for v in producer() do
            sum = sum + v
        end
        assert(sum == 150)  -- 10+20+30+40+50
        "#,
    );
}

#[test]
fn conformance_coroutine_isyieldable() {
    run_lua(
        r#"
        assert(coroutine.isyieldable() == false)
        local co = coroutine.create(function()
            assert(coroutine.isyieldable() == true)
            coroutine.yield()
        end)
        coroutine.resume(co)
        "#,
    );
}

#[test]
fn conformance_coroutine_error_in_body() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            error("oops")
        end)
        local ok, msg = coroutine.resume(co)
        assert(not ok)
        assert(coroutine.status(co) == "dead")
        "#,
    );
}

#[test]
fn conformance_coroutine_multiple_yields() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            for i = 1, 5 do
                coroutine.yield(i)
            end
            return 99
        end)
        local results = {}
        while true do
            local ok, v = coroutine.resume(co)
            if not ok then break end
            results[#results + 1] = v
            if coroutine.status(co) == "dead" then break end
        end
        assert(#results == 6)  -- 1,2,3,4,5,99
        assert(results[1] == 1)
        assert(results[6] == 99)
        "#,
    );
}

// ==========================================================================
// 1K. Events / Metamethods (from testes/events.lua)
// ==========================================================================

#[test]
fn conformance_index_chain_table() {
    run_lua(
        r#"
        local base = {x = 10}
        local derived = setmetatable({}, {__index = base})
        assert(derived.x == 10)
        "#,
    );
}

#[test]
fn conformance_index_function() {
    run_lua(
        r#"
        local t = setmetatable({}, {__index = function(t, k) return k .. "!" end})
        assert(t.hello == "hello!")
        assert(t.world == "world!")
        "#,
    );
}

#[test]
fn conformance_newindex_function() {
    run_lua(
        r#"
        local log = {}
        local t = setmetatable({}, {__newindex = function(t, k, v)
            log[#log + 1] = k
            rawset(t, k, v)
        end})
        t.a = 1; t.b = 2
        assert(log[1] == "a" and log[2] == "b")
        assert(t.a == 1)
        "#,
    );
}

#[test]
fn conformance_newindex_existing_key_no_fire() {
    run_lua(
        r#"
        local count = 0
        local t = setmetatable({}, {__newindex = function(t, k, v)
            count = count + 1
            rawset(t, k, v)
        end})
        t.a = 1    -- fires __newindex (count=1)
        t.a = 99   -- key exists, does NOT fire __newindex
        assert(count == 1)
        "#,
    );
}

#[test]
fn conformance_tostring_metamethod() {
    run_lua(
        r#"
        local t = setmetatable({}, {__tostring = function() return "custom" end})
        assert(tostring(t) == "custom")
        "#,
    );
}

#[test]
fn conformance_len_metamethod() {
    run_lua(
        r#"
        local t = setmetatable({1, 2, 3}, {__len = function() return 99 end})
        assert(#t == 99)
        "#,
    );
}

#[test]
fn conformance_concat_metamethod() {
    run_lua(
        r#"
        local t = setmetatable({}, {__concat = function(a, b) return "joined" end})
        assert(t .. "x" == "joined")
        "#,
    );
}

#[test]
fn conformance_arith_mm_precedence() {
    run_lua(
        r#"
        local a = setmetatable({}, {__add = function() return "a" end})
        local b = setmetatable({}, {__add = function() return "b" end})
        assert(a + b == "a")
        assert(1 + b == "b")
        "#,
    );
}

#[test]
fn conformance_eq_same_metatable() {
    run_lua(
        r#"
        local mt = {__eq = function(a, b) return true end}
        local a = setmetatable({}, mt)
        local b = setmetatable({}, mt)
        assert(a == b)
        "#,
    );
}

#[test]
fn conformance_call_metamethod() {
    run_lua(
        r#"
        local t = setmetatable({}, {
            __call = function(self, x, y) return x + y end
        })
        assert(t(3, 4) == 7)
        "#,
    );
}

#[test]
fn conformance_unm_metamethod() {
    run_lua(
        r#"
        local t = setmetatable({}, {__unm = function(a) return 42 end})
        assert(-t == 42)
        "#,
    );
}

#[test]
fn conformance_lt_metamethod() {
    run_lua(
        r#"
        local mt = {__lt = function(a, b)
            return rawget(a, "val") < rawget(b, "val")
        end}
        local a = setmetatable({val = 1}, mt)
        local b = setmetatable({val = 2}, mt)
        assert(a < b)
        assert(not (b < a))
        "#,
    );
}

#[test]
fn conformance_le_metamethod() {
    run_lua(
        r#"
        local mt = {__le = function(a, b)
            return rawget(a, "val") <= rawget(b, "val")
        end}
        local a = setmetatable({val = 2}, mt)
        local b = setmetatable({val = 2}, mt)
        assert(a <= b)
        "#,
    );
}

#[test]
fn conformance_index_chain_3_levels() {
    run_lua(
        r#"
        local c = {x = 42}
        local b = setmetatable({}, {__index = c})
        local a = setmetatable({}, {__index = b})
        assert(a.x == 42)
        "#,
    );
}

#[test]
fn conformance_rawget_bypasses_index() {
    run_lua(
        r#"
        local t = setmetatable({}, {__index = function() return 99 end})
        assert(t.x == 99)
        assert(rawget(t, "x") == nil)
        "#,
    );
}

#[test]
fn conformance_rawset_bypasses_newindex() {
    run_lua(
        r#"
        local count = 0
        local t = setmetatable({}, {__newindex = function(t, k, v) count = count + 1 end})
        rawset(t, "x", 42)
        assert(count == 0)
        assert(t.x == 42)
        "#,
    );
}

#[test]
fn conformance_setmetatable_returns_table() {
    run_lua(
        r#"
        local t = {}
        local result = setmetatable(t, {})
        assert(t == result)
        "#,
    );
}

#[test]
fn conformance_getmetatable_basic() {
    run_lua(
        r#"
        local mt = {}
        local t = setmetatable({}, mt)
        assert(getmetatable(t) == mt)
        "#,
    );
}

#[test]
fn conformance_metatable_protect() {
    run_lua(
        r#"
        local mt = {__metatable = "protected"}
        local t = setmetatable({}, mt)
        assert(getmetatable(t) == "protected")
        local ok = pcall(setmetatable, t, {})
        assert(not ok)
        "#,
    );
}

// ==========================================================================
// 1L. Error Handling (from testes/errors.lua)
// ==========================================================================

#[test]
fn conformance_pcall_returns_false_msg() {
    run_lua(
        r#"
        local ok, msg = pcall(error, "boom")
        assert(ok == false)
        "#,
    );
}

#[test]
fn conformance_error_non_string() {
    run_lua(
        r#"
        local ok, msg = pcall(error, 42)
        assert(ok == false and msg == 42)
        "#,
    );
}

#[test]
fn conformance_error_table_identity() {
    run_lua(
        r#"
        local t = {msg = "err"}
        local ok, msg = pcall(error, t)
        assert(ok == false and msg == t)
        "#,
    );
}

#[test]
fn conformance_xpcall_handler() {
    run_lua(
        r#"
        local ok, msg = xpcall(
            function() error("oops") end,
            function(e) return "handled: " .. e end
        )
        assert(ok == false)
        assert(string.find(msg, "handled:") ~= nil)
        "#,
    );
}

#[test]
fn conformance_nested_pcall() {
    run_lua(
        r#"
        local ok1, ok2, msg = pcall(function()
            return pcall(function() error("inner") end)
        end)
        assert(ok1 == true and ok2 == false)
        "#,
    );
}

#[test]
fn conformance_error_level_0() {
    run_lua(
        r#"
        local ok, msg = pcall(error, "raw", 0)
        assert(msg == "raw")
        "#,
    );
}

#[test]
fn conformance_error_boolean_false() {
    run_lua(
        r#"
        local ok, msg = pcall(error, false)
        assert(ok == false and msg == false)
        "#,
    );
}

#[test]
fn conformance_error_nil() {
    run_lua(
        r#"
        local ok, msg = pcall(error, nil)
        assert(ok == false and msg == nil)
        "#,
    );
}

#[test]
fn conformance_assert_with_message() {
    run_lua(
        r#"
        local ok, msg = pcall(assert, false, "custom msg")
        assert(ok == false and msg == "custom msg")
        "#,
    );
}

#[test]
fn conformance_assert_default_message() {
    run_lua(
        r#"
        local ok, msg = pcall(assert, false)
        assert(ok == false and msg == "assertion failed!")
        "#,
    );
}

#[test]
fn conformance_assert_passes_through() {
    run_lua(
        r#"
        assert(assert(42) == 42)
        assert(assert("hello") == "hello")
        assert(assert(true) == true)
        "#,
    );
}

#[test]
fn conformance_pcall_stack_preserves() {
    run_lua(
        r#"
        local x = 10
        local ok = pcall(function()
            x = 20
            error("boom")
        end)
        assert(not ok and x == 20)
        "#,
    );
}

#[test]
fn conformance_deeply_nested_pcall() {
    run_lua(
        r#"
        local ok = pcall(function()
            pcall(function()
                pcall(function()
                    error("deep")
                end)
            end)
        end)
        assert(ok == true)
        "#,
    );
}

#[test]
fn conformance_xpcall_handler_error() {
    run_lua(
        r#"
        local ok, msg = xpcall(
            function() error("first") end,
            function(e) error("handler_error") end
        )
        assert(ok == false)
        "#,
    );
}

#[test]
fn conformance_pcall_no_error_multiple_results() {
    run_lua(
        r#"
        local ok, a, b, c = pcall(function() return 1, 2, 3 end)
        assert(ok == true and a == 1 and b == 2 and c == 3)
        "#,
    );
}
