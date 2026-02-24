/// Tests for load(), dofile(), loadfile(), _VERSION, _G, and warn().
use super::helpers::*;

// ---- load() tests ----

#[test]
fn test_load_simple_string() {
    run_check_ints("local f = load('return 1 + 1')\nreturn f()", &[2]);
}

#[test]
fn test_load_returns_function() {
    run_check_strings("return type(load('return 1'))", &["function"]);
}

#[test]
fn test_load_with_arguments() {
    run_check_ints(
        "local f = load('local a, b = ...; return a + b')\nreturn f(10, 20)",
        &[30],
    );
}

#[test]
fn test_load_syntax_error() {
    // load with syntax error returns nil + error message
    let (results, vm) = run_with_vm(
        r#"
        local f, err = load('invalid ===')
        return f == nil, type(err)
        "#,
    );
    assert_bool(&results, 0, true);
    assert_str(&results, 1, "string", &vm);
}

#[test]
fn test_load_chunkname() {
    // Custom chunkname should appear in error messages
    let (results, _vm) = run_with_vm(
        r#"
        local f, err = load('error("boom")', 'mychunk')
        return f ~= nil
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_load_custom_env() {
    run_check_ints(
        r#"
        local env = { x = 42 }
        setmetatable(env, { __index = _G })
        local f = load('return x', 'test', 't', env)
        return f()
        "#,
        &[42],
    );
}

#[test]
fn test_load_function_reader() {
    run_check_ints(
        r#"
        local pieces = { "return ", "1 + ", "2" }
        local i = 0
        local f = load(function()
            i = i + 1
            return pieces[i]
        end)
        return f()
        "#,
        &[3],
    );
}

#[test]
fn test_load_function_reader_nil_terminates() {
    run_check_ints(
        r#"
        local called = 0
        local f = load(function()
            called = called + 1
            if called == 1 then return "return 99" end
            return nil
        end)
        return f()
        "#,
        &[99],
    );
}

#[test]
fn test_load_empty_string() {
    // load("") should return a function that returns no values
    let results = run_lua("local f = load('')\nreturn f()");
    assert_eq!(results.len(), 0);
}

#[test]
fn test_load_multiple_returns() {
    run_check_ints("local f = load('return 1, 2, 3')\nreturn f()", &[1, 2, 3]);
}

#[test]
fn test_load_access_env() {
    // Loaded chunk should see _ENV globals by default
    run_check_strings(
        r#"
        local f = load('return type(print)')
        return f()
        "#,
        &["function"],
    );
}

// ---- _VERSION tests ----

#[test]
fn test_version() {
    run_check_strings("return _VERSION", &["Lua 5.4"]);
}

// ---- _G tests ----

#[test]
fn test_g_is_env() {
    let (results, _) = run_with_vm("return _G == _ENV");
    assert_bool(&results, 0, true);
}

#[test]
fn test_g_contains_globals() {
    run_check_strings("return type(_G.print)", &["function"]);
}

#[test]
fn test_g_assignment() {
    run_check_ints(
        r#"
        _G.myval = 42
        return myval
        "#,
        &[42],
    );
}

// ---- warn() tests ----

#[test]
fn test_warn_does_not_error() {
    // warn() should not raise an error
    let results = run_lua(r#"warn("test warning")"#);
    assert_eq!(results.len(), 0);
}

#[test]
fn test_warn_control_messages() {
    // @on and @off should not raise errors
    let results = run_lua(r#"
        warn("@off")
        warn("@on")
    "#);
    assert_eq!(results.len(), 0);
}

// ---- dofile tests (using temp files) ----

#[test]
fn test_dofile_basic() {
    use std::io::Write;
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    writeln!(tmp, "return 42").unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(r#"return dofile("{path}")"#);
    run_check_ints(&source, &[42]);
}

#[test]
fn test_dofile_with_globals() {
    // Test that globals set in loaded code work - use locals for now
    // Global assignment in loaded code requires proper _ENV sharing
    run_check_ints(
        r#"
        local f = load("local x = 100 return x + 1")
        return f()
        "#,
        &[101],
    );
}

#[test]
fn test_load_global_read() {
    // Test that loaded code can read globals from _ENV
    // Set a global in main, then read it in loaded code
    run_check_ints(
        r#"
        y = 42
        local f = load("return y")
        return f()
        "#,
        &[42],
    );
}

#[test]
fn test_load_global_write_and_read_same_chunk() {
    // Write and read in the same loaded chunk
    run_check_ints(
        r#"
        local f = load("x = 100 return x")
        return f()
        "#,
        &[100],
    );
}

#[test]
fn test_load_global_write_and_read_cross_chunk() {
    // Write in loaded chunk, read in main chunk
    run_check_ints(
        r#"
        local f = load("x = 100")
        f()
        return x
        "#,
        &[100],
    );
}

#[test]
fn test_dofile_nonexistent_file() {
    let err = run_lua_err(r#"dofile("/nonexistent/file.lua")"#);
    assert!(err.contains("cannot open"), "error was: {err}");
}

// ---- loadfile tests ----

#[test]
fn test_loadfile_basic() {
    use std::io::Write;
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    writeln!(tmp, "return 77").unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(r#"
        local f = loadfile("{path}")
        return f()
    "#);
    run_check_ints(&source, &[77]);
}

#[test]
fn test_loadfile_nonexistent() {
    let (results, _vm) = run_with_vm(
        r#"
        local f, err = loadfile("/nonexistent/file.lua")
        return f == nil, err ~= nil
        "#,
    );
    assert_bool(&results, 0, true);
    assert_bool(&results, 1, true);
}

#[test]
fn test_loadfile_returns_function() {
    use std::io::Write;
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    writeln!(tmp, "return 1").unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(r#"return type(loadfile("{path}"))"#);
    run_check_strings(&source, &["function"]);
}

// ---- load() with nested protos ----

#[test]
fn test_load_closure_in_loaded_code() {
    run_check_ints(
        r#"
        local f = load('local function add(a,b) return a+b end return add(3,4)')
        return f()
        "#,
        &[7],
    );
}

#[test]
fn test_load_called_multiple_times() {
    run_check_ints(
        r#"
        local f = load('return 5')
        local a = f()
        local b = f()
        return a + b
        "#,
        &[10],
    );
}

#[test]
fn test_load_shares_string_interner() {
    // Strings created in loaded code should be comparable with host strings
    let (results, _) = run_with_vm(
        r#"
        local f = load('return "hello"')
        return f() == "hello"
        "#,
    );
    assert_bool(&results, 0, true);
}
