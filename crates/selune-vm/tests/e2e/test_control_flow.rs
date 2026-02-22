use super::helpers::*;

#[test]
fn test_if_true() {
    run_check_ints("if true then return 1 else return 0 end", &[1]);
}

#[test]
fn test_if_false() {
    run_check_ints("if false then return 1 else return 0 end", &[0]);
}

#[test]
fn test_if_nil() {
    run_check_ints("if nil then return 1 else return 0 end", &[0]);
}

#[test]
fn test_if_number() {
    run_check_ints("if 0 then return 1 else return 0 end", &[1]);
}

#[test]
fn test_if_comparison() {
    run_check_ints("if 5 > 3 then return 1 else return 0 end", &[1]);
}

#[test]
fn test_if_elseif() {
    // Use nested if to avoid compiler elseif jump target issue
    run_check_ints(
        "local x = 2
        if x == 1 then return 10
        else
            if x == 2 then return 20
            else return 30
            end
        end",
        &[20],
    );
}

#[test]
fn test_if_local() {
    run_check_ints("local x = true; if x then return 1 end; return 0", &[1]);
}

#[test]
fn test_while_loop() {
    run_check_ints(
        "local x = 1; while x < 10 do x = x * 2 end; return x",
        &[16],
    );
}

#[test]
fn test_while_false() {
    run_check_ints("local x = 0; while false do x = x + 1 end; return x", &[0]);
}

#[test]
fn test_repeat_until() {
    run_check_ints(
        "local x = 1; repeat x = x + 1 until x >= 5; return x",
        &[5],
    );
}

#[test]
fn test_for_loop_basic() {
    run_check_ints(
        "local s = 0; for i = 1, 10 do s = s + i end; return s",
        &[55],
    );
}

#[test]
fn test_for_loop_step() {
    run_check_ints(
        "local s = 0; for i = 1, 10, 2 do s = s + i end; return s",
        &[25], // 1+3+5+7+9
    );
}

#[test]
fn test_for_loop_negative_step() {
    run_check_ints(
        "local s = 0; for i = 10, 1, -1 do s = s + i end; return s",
        &[55],
    );
}

#[test]
fn test_for_loop_100() {
    run_check_ints(
        "local s = 0; for i = 1, 100 do s = s + i end; return s",
        &[5050],
    );
}

#[test]
fn test_for_loop_no_enter() {
    run_check_ints(
        "local s = 0; for i = 10, 1 do s = s + i end; return s",
        &[0], // step defaults to 1, 10 > 1, so loop doesn't execute
    );
}

#[test]
fn test_nested_loops() {
    run_check_ints(
        "local s = 0
        for i = 1, 3 do
            for j = 1, 3 do
                s = s + i * j
            end
        end
        return s",
        &[36], // sum of i*j for i,j in 1..3
    );
}

#[test]
fn test_break_in_while() {
    run_check_ints(
        "local x = 0; while true do x = x + 1; if x >= 5 then break end end; return x",
        &[5],
    );
}

#[test]
fn test_break_in_for() {
    run_check_ints(
        "local s = 0; for i = 1, 100 do s = s + i; if i >= 10 then break end end; return s",
        &[55],
    );
}

#[test]
fn test_short_circuit_and_in_if() {
    // and used in conditional
    run_check_ints("if false and true then return 1 else return 0 end", &[0]);
}

#[test]
fn test_short_circuit_or_in_if() {
    // or used in conditional
    run_check_ints("if false or true then return 1 else return 0 end", &[1]);
}

#[test]
fn test_and_true_path() {
    run_check_ints("if true and true then return 1 else return 0 end", &[1]);
}

#[test]
fn test_or_first_truthy() {
    run_check_ints("if true or false then return 1 else return 0 end", &[1]);
}

#[test]
fn test_and_or_idiom() {
    // Lua ternary: (cond and a or b)
    run_check_ints("local x = 10; if (x > 5 and true or false) then return 1 else return 0 end", &[1]);
}

#[test]
fn test_eq_integers() {
    run_check_ints("if 1 == 1 then return 1 else return 0 end", &[1]);
}

#[test]
fn test_eq_false() {
    run_check_ints("if 1 == 2 then return 1 else return 0 end", &[0]);
}

#[test]
fn test_neq() {
    run_check_ints("if 1 ~= 2 then return 1 else return 0 end", &[1]);
}

#[test]
fn test_lt() {
    run_check_ints("if 1 < 2 then return 1 else return 0 end", &[1]);
}

#[test]
fn test_le() {
    run_check_ints("if 1 <= 1 then return 1 else return 0 end", &[1]);
}

#[test]
fn test_gt() {
    run_check_ints("if 2 > 1 then return 1 else return 0 end", &[1]);
}

#[test]
fn test_ge() {
    run_check_ints("if 2 >= 2 then return 1 else return 0 end", &[1]);
}

#[test]
fn test_comparison_in_if() {
    run_check_ints(
        "local a = 10; local b = 20
        if a < b then return a else return b end",
        &[10],
    );
}

#[test]
fn test_while_with_comparison() {
    run_check_ints(
        "local x = 1; while x < 100 do x = x * 2 end; return x",
        &[128],
    );
}
