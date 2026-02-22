use super::helpers::*;

#[test]
fn test_add_integers() {
    run_check_ints("return 1 + 2", &[3]);
}

#[test]
fn test_add_locals() {
    run_check_ints("local x = 10; local y = 20; return x + y", &[30]);
}

#[test]
fn test_sub() {
    run_check_ints("return 10 - 3", &[7]);
}

#[test]
fn test_mul() {
    run_check_ints("return 6 * 7", &[42]);
}

#[test]
fn test_div_float() {
    let results = run_lua("return 10 / 3");
    assert_float(&results, 0, 10.0 / 3.0);
}

#[test]
fn test_idiv() {
    run_check_ints("return 7 // 2", &[3]);
}

#[test]
fn test_idiv_negative() {
    run_check_ints("return -7 // 2", &[-4]);
}

#[test]
fn test_mod() {
    run_check_ints("return 7 % 3", &[1]);
}

#[test]
fn test_mod_negative() {
    // Lua modulo: result has same sign as divisor
    run_check_ints("return -7 % 3", &[2]);
}

#[test]
fn test_pow() {
    let results = run_lua("return 2 ^ 10");
    assert_float(&results, 0, 1024.0);
}

#[test]
fn test_band() {
    run_check_ints("return 0xFF & 0x0F", &[15]);
}

#[test]
fn test_bor() {
    run_check_ints("return 0xF0 | 0x0F", &[0xFF]);
}

#[test]
fn test_bxor() {
    run_check_ints("return 0xFF ~ 0x0F", &[0xF0]);
}

#[test]
fn test_shl() {
    run_check_ints("return 3 << 4", &[48]);
}

#[test]
fn test_shr() {
    run_check_ints("return 48 >> 4", &[3]);
}

#[test]
fn test_unm() {
    run_check_ints("return -42", &[-42]);
}

#[test]
fn test_unm_float() {
    let results = run_lua("return -3.14");
    assert_float(&results, 0, -3.14);
}

#[test]
fn test_bnot() {
    run_check_ints("return ~0", &[-1]);
}

#[test]
fn test_not_true() {
    let results = run_lua("return not true");
    assert_bool(&results, 0, false);
}

#[test]
fn test_not_false() {
    let results = run_lua("return not false");
    assert_bool(&results, 0, true);
}

#[test]
fn test_not_nil() {
    let results = run_lua("return not nil");
    assert_bool(&results, 0, true);
}

#[test]
fn test_not_zero() {
    // 0 is truthy in Lua
    let results = run_lua("return not 0");
    assert_bool(&results, 0, false);
}

#[test]
fn test_len_string() {
    run_check_ints("return #\"hello\"", &[5]);
}

#[test]
fn test_len_empty_string() {
    run_check_ints("return #\"\"", &[0]);
}

#[test]
fn test_concat_strings() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return \"hello\" .. \" \" .. \"world\"", "=test")
            .unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_eq!(results.len(), 1);
    assert_str(&results, 0, "hello world", &vm);
}

#[test]
fn test_concat_with_numbers() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return \"value: \" .. 42", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_eq!(results.len(), 1);
    assert_str(&results, 0, "value: 42", &vm);
}

#[test]
fn test_complex_expression() {
    // (2 + 3) * 4 - 1
    run_check_ints(
        "local a = 2; local b = 3; local c = 4; return (a + b) * c - 1",
        &[19],
    );
}

#[test]
fn test_mixed_int_float() {
    let results = run_lua("return 1 + 2.5");
    assert_float(&results, 0, 3.5);
}

#[test]
fn test_float_div_always_float() {
    let results = run_lua("return 10 / 2");
    assert_float(&results, 0, 5.0);
}
