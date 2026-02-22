use selune_core::value::TValue;
use selune_vm::vm::Vm;

/// Compile and execute Lua source, returning result TValues.
pub fn run_lua(source: &str) -> Vec<TValue> {
    let (proto, strings) = selune_compiler::compiler::compile(source.as_bytes(), "=test")
        .unwrap_or_else(|e| panic!("compile error: {} at line {}", e.message, e.line));

    let mut vm = Vm::new();
    vm.execute(&proto, strings)
        .unwrap_or_else(|e| panic!("runtime error: {e}"))
}

/// Compile and execute Lua source, expecting a runtime error.
pub fn run_lua_err(source: &str) -> String {
    let (proto, strings) = selune_compiler::compiler::compile(source.as_bytes(), "=test")
        .unwrap_or_else(|e| panic!("compile error: {} at line {}", e.message, e.line));

    let mut vm = Vm::new();
    match vm.execute(&proto, strings) {
        Err(e) => format!("{e}"),
        Ok(vals) => panic!("expected error, got {} results: {:?}", vals.len(), vals),
    }
}

/// Check that results[idx] is an integer with the expected value.
pub fn assert_int(results: &[TValue], idx: usize, expected: i64) {
    let val = results[idx];
    let got = val
        .as_integer()
        .unwrap_or_else(|| panic!("result[{idx}] = {:?}, expected integer {expected}", val));
    assert_eq!(got, expected, "result[{idx}] = {got}, expected {expected}");
}

/// Check that results[idx] is a float with the expected value.
pub fn assert_float(results: &[TValue], idx: usize, expected: f64) {
    let val = results[idx];
    let got = val
        .as_float()
        .unwrap_or_else(|| panic!("result[{idx}] = {:?}, expected float {expected}", val));
    assert!(
        (got - expected).abs() < 1e-10,
        "result[{idx}] = {got}, expected {expected}"
    );
}

/// Check that results[idx] is a boolean with the expected value.
pub fn assert_bool(results: &[TValue], idx: usize, expected: bool) {
    let val = results[idx];
    let got = val
        .as_bool()
        .unwrap_or_else(|| panic!("result[{idx}] = {:?}, expected bool {expected}", val));
    assert_eq!(got, expected, "result[{idx}] = {got}, expected {expected}");
}

/// Check that results[idx] is nil.
pub fn assert_nil(results: &[TValue], idx: usize) {
    let val = results[idx];
    assert!(val.is_nil(), "result[{idx}] = {:?}, expected nil", val);
}

/// Check that results[idx] is a string with the expected value.
pub fn assert_str(results: &[TValue], idx: usize, expected: &str, vm: &Vm) {
    let val = results[idx];
    let sid = val
        .as_string_id()
        .unwrap_or_else(|| panic!("result[{idx}] = {:?}, expected string \"{expected}\"", val));
    let got = std::str::from_utf8(vm.strings.get_bytes(sid)).unwrap();
    assert_eq!(
        got, expected,
        "result[{idx}] = \"{got}\", expected \"{expected}\""
    );
}

/// Run Lua source and check results against expected integer values.
pub fn run_check_ints(source: &str, expected: &[i64]) {
    let results = run_lua(source);
    assert_eq!(
        results.len(),
        expected.len(),
        "expected {} results, got {}",
        expected.len(),
        results.len()
    );
    for (i, &exp) in expected.iter().enumerate() {
        assert_int(&results, i, exp);
    }
}
