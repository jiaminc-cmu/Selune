use super::helpers::*;

// ---- os.clock ----

#[test]
fn test_os_clock_returns_number() {
    let results = run_lua("return os.clock() >= 0");
    assert_bool(&results, 0, true);
}

#[test]
fn test_os_clock_is_float() {
    let (results, vm) = run_with_vm("return type(os.clock())");
    assert_str(&results, 0, "number", &vm);
}

// ---- os.time ----

#[test]
fn test_os_time_returns_integer() {
    let (results, vm) = run_with_vm("return type(os.time())");
    assert_str(&results, 0, "number", &vm);
}

#[test]
fn test_os_time_is_positive() {
    let results = run_lua("return os.time() > 0");
    assert_bool(&results, 0, true);
}

#[test]
fn test_os_time_with_table() {
    // Known date: 2000-01-01 00:00:00 UTC = 946684800
    run_check_ints(
        "return os.time({year=2000, month=1, day=1, hour=0, min=0, sec=0})",
        &[946684800],
    );
}

#[test]
fn test_os_time_with_table_defaults() {
    // hour defaults to 12, min/sec default to 0
    // 2000-01-01 12:00:00 UTC = 946684800 + 12*3600 = 946728000
    run_check_ints("return os.time({year=2000, month=1, day=1})", &[946728000]);
}

// ---- os.difftime ----

#[test]
fn test_os_difftime_basic() {
    run_check_floats("return os.difftime(100, 50)", &[50.0]);
}

#[test]
fn test_os_difftime_negative() {
    run_check_floats("return os.difftime(50, 100)", &[-50.0]);
}

#[test]
fn test_os_difftime_with_time() {
    // difftime of current time with itself should be 0
    let results = run_lua(
        r#"
        local t = os.time()
        return os.difftime(t, t)
    "#,
    );
    assert_float(&results, 0, 0.0);
}

// ---- os.date ----

#[test]
fn test_os_date_star_t() {
    // os.date("*t") should return a table
    let (results, vm) = run_with_vm("return type(os.date('*t'))");
    assert_str(&results, 0, "table", &vm);
}

#[test]
fn test_os_date_star_t_fields() {
    // Check that *t table has the expected fields
    let results = run_lua(
        r#"
        local t = os.date("*t")
        return t.year > 2000, t.month >= 1, t.month <= 12, t.day >= 1, t.day <= 31
    "#,
    );
    assert_bool(&results, 0, true);
    assert_bool(&results, 1, true);
    assert_bool(&results, 2, true);
    assert_bool(&results, 3, true);
    assert_bool(&results, 4, true);
}

#[test]
fn test_os_date_year_format() {
    // %Y should return a 4-digit year string
    let results = run_lua(r#"return #os.date("%Y") == 4"#);
    assert_bool(&results, 0, true);
}

#[test]
fn test_os_date_known_timestamp() {
    // Unix epoch: 1970-01-01 00:00:00 UTC
    let (results, vm) = run_with_vm(r#"return os.date("%Y-%m-%d", 0)"#);
    assert_str(&results, 0, "1970-01-01", &vm);
}

#[test]
fn test_os_date_known_timestamp_full() {
    // 2000-01-01 00:00:00 UTC = 946684800
    let (results, vm) = run_with_vm(r#"return os.date("%Y-%m-%d %H:%M:%S", 946684800)"#);
    assert_str(&results, 0, "2000-01-01 00:00:00", &vm);
}

#[test]
fn test_os_date_percent_escape() {
    let (results, vm) = run_with_vm(r#"return os.date("%%", 0)"#);
    assert_str(&results, 0, "%", &vm);
}

// ---- os.getenv ----

#[test]
fn test_os_getenv_path() {
    // PATH should always be set in a normal environment
    let results = run_lua("return os.getenv('PATH') ~= nil");
    assert_bool(&results, 0, true);
}

#[test]
fn test_os_getenv_nonexistent() {
    let results = run_lua("return os.getenv('SELUNE_NONEXISTENT_VAR_12345')");
    assert_nil(&results, 0);
}

// ---- os.execute ----

#[test]
fn test_os_execute_nil() {
    // os.execute() with no args returns true (shell available)
    let results = run_lua("return os.execute()");
    assert_bool(&results, 0, true);
}

#[test]
#[ignore = "requires shell access"]
fn test_os_execute_success() {
    let (results, vm) = run_with_vm(r#"return os.execute("echo hello")"#);
    assert_bool(&results, 0, true);
    assert_str(&results, 1, "exit", &vm);
}

#[test]
#[ignore = "requires shell access"]
fn test_os_execute_failure() {
    let (results, vm) = run_with_vm(
        r#"
        local ok, tp, code = os.execute("exit 1")
        return ok == nil, tp, code
    "#,
    );
    assert_bool(&results, 0, true); // ok == nil is true
    assert_str(&results, 1, "exit", &vm);
}

// ---- os.tmpname ----

#[test]
fn test_os_tmpname_returns_string() {
    let (results, vm) = run_with_vm("return type(os.tmpname())");
    assert_str(&results, 0, "string", &vm);
}

#[test]
fn test_os_tmpname_unique() {
    // Two calls should return different names
    let results = run_lua("return os.tmpname() ~= os.tmpname()");
    assert_bool(&results, 0, true);
}

// ---- os.remove ----

#[test]
fn test_os_remove_nonexistent() {
    // Removing a nonexistent file should return nil + error message
    let results = run_lua(
        r#"
        local ok, msg = os.remove("/tmp/selune_nonexistent_file_12345")
        return ok == nil, type(msg) == "string"
    "#,
    );
    assert_bool(&results, 0, true);
    assert_bool(&results, 1, true);
}

// ---- os.rename ----

#[test]
fn test_os_rename_nonexistent() {
    // Renaming a nonexistent file should return nil + error message
    let results = run_lua(
        r#"
        local ok, msg = os.rename("/tmp/selune_nonexistent_a_12345", "/tmp/selune_nonexistent_b_12345")
        return ok == nil, type(msg) == "string"
    "#,
    );
    assert_bool(&results, 0, true);
    assert_bool(&results, 1, true);
}

// ---- os.setlocale ----

#[test]
fn test_os_setlocale_c() {
    let (results, vm) = run_with_vm(r#"return os.setlocale("C")"#);
    assert_str(&results, 0, "C", &vm);
}

#[test]
fn test_os_setlocale_query() {
    let (results, vm) = run_with_vm("return os.setlocale(nil)");
    assert_str(&results, 0, "C", &vm);
}

// ---- os.date with *t and os.time roundtrip ----

#[test]
fn test_os_date_time_roundtrip() {
    // os.time(os.date("*t")) should return approximately current time
    // (may differ by 1 second due to timing)
    let results = run_lua(
        r#"
        local t1 = os.time()
        local t2 = os.time(os.date("*t"))
        return math.abs(t2 - t1) <= 1
    "#,
    );
    assert_bool(&results, 0, true);
}
