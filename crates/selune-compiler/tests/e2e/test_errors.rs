use super::helpers::*;

#[test]
fn e2e_error_unterminated_string() {
    let err = compile_str_err("local x = \"hello");
    assert!(err.contains("unterminated string"));
}

#[test]
fn e2e_error_break_outside_loop() {
    let err = compile_str_err("break");
    assert!(err.contains("break") || err.contains("outside"));
}

#[test]
fn e2e_error_duplicate_label() {
    let err = compile_str_err("::x:: ::x::");
    assert!(err.contains("label 'x' already defined"));
}

#[test]
fn e2e_error_unexpected_symbol() {
    let err = compile_str_err("return )");
    assert!(err.contains("unexpected symbol") || err.contains("expected"));
}

#[test]
fn e2e_error_malformed_number() {
    let err = compile_str_err("local x = 1e");
    assert!(err.contains("malformed number") || err.contains("expected"));
}

#[test]
fn e2e_error_invalid_escape() {
    let err = compile_str_err("local x = \"\\q\"");
    assert!(err.contains("invalid escape"));
}

#[test]
fn e2e_error_expected_end() {
    let err = compile_str_err("if true then");
    assert!(err.contains("expected") || err.contains("end"));
}

#[test]
fn e2e_error_expected_then() {
    let err = compile_str_err("if true do end");
    assert!(err.contains("expected 'then'") || err.contains("expected"));
}

#[test]
fn e2e_error_vararg_outside() {
    let err = compile_str_err("function f() return ... end");
    assert!(err.contains("vararg") || err.contains("..."));
}

#[test]
fn e2e_error_expression_not_statement() {
    let err = compile_str_err("42");
    assert!(err.contains("statement") || err.contains("unexpected"));
}
