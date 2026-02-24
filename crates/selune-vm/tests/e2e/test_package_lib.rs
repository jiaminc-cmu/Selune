/// Tests for the package/require library.
use super::helpers::*;

// ---- package table structure ----

#[test]
fn test_package_is_table() {
    run_check_strings("return type(package)", &["table"]);
}

#[test]
fn test_package_loaded_is_table() {
    run_check_strings("return type(package.loaded)", &["table"]);
}

#[test]
fn test_package_preload_is_table() {
    run_check_strings("return type(package.preload)", &["table"]);
}

#[test]
fn test_package_path_is_string() {
    run_check_strings("return type(package.path)", &["string"]);
}

#[test]
fn test_package_config_is_string() {
    run_check_strings("return type(package.config)", &["string"]);
}

#[test]
fn test_package_searchpath_is_function() {
    run_check_strings("return type(package.searchpath)", &["function"]);
}

#[test]
fn test_package_searchers_is_table() {
    run_check_strings("return type(package.searchers)", &["table"]);
}

// ---- require exists ----

#[test]
fn test_require_is_function() {
    run_check_strings("return type(require)", &["function"]);
}

// ---- package.loaded pre-populated ----

#[test]
fn test_package_loaded_has_math() {
    let (results, _) = run_with_vm(
        r#"
        return package.loaded.math == math
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_package_loaded_has_string() {
    let (results, _) = run_with_vm(
        r#"
        return package.loaded.string == string
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_package_loaded_has_table() {
    let (results, _) = run_with_vm(
        r#"
        return package.loaded.table == table
        "#,
    );
    assert_bool(&results, 0, true);
}

// ---- require with preload ----

#[test]
fn test_require_preload() {
    run_check_ints(
        r#"
        package.preload["mymod"] = function(name)
            return { value = 42 }
        end
        local m = require("mymod")
        return m.value
        "#,
        &[42],
    );
}

#[test]
fn test_require_preload_cached() {
    // Second require returns the same table
    let (results, _) = run_with_vm(
        r#"
        package.preload["mymod"] = function(name)
            return { value = 42 }
        end
        local m1 = require("mymod")
        local m2 = require("mymod")
        return m1 == m2
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_require_preload_receives_modname() {
    run_check_strings(
        r#"
        package.preload["testmod"] = function(name)
            return { name = name }
        end
        local m = require("testmod")
        return m.name
        "#,
        &["testmod"],
    );
}

// ---- require with Lua file ----

#[test]
fn test_require_lua_file() {
    use std::io::Write;

    // Create a temp directory and Lua module file
    let dir = tempfile::TempDir::new().unwrap();
    let mod_path = dir.path().join("mylib.lua");
    let mut f = std::fs::File::create(&mod_path).unwrap();
    writeln!(f, "local M = {{}}").unwrap();
    writeln!(f, "M.answer = 42").unwrap();
    writeln!(f, "return M").unwrap();

    let dir_str = dir.path().to_str().unwrap().replace('\\', "/");
    let source = format!(
        r#"
        package.path = "{}/?.lua"
        local m = require("mylib")
        return m.answer
        "#,
        dir_str
    );
    run_check_ints(&source, &[42]);
}

#[test]
fn test_require_lua_file_cached() {
    use std::io::Write;

    let dir = tempfile::TempDir::new().unwrap();
    let mod_path = dir.path().join("counter.lua");
    let mut f = std::fs::File::create(&mod_path).unwrap();
    writeln!(f, "local M = {{}}").unwrap();
    writeln!(f, "M.count = 0").unwrap();
    writeln!(f, "M.count = M.count + 1").unwrap();
    writeln!(f, "return M").unwrap();

    let dir_str = dir.path().to_str().unwrap().replace('\\', "/");
    let source = format!(
        r#"
        package.path = "{}/?.lua"
        local m1 = require("counter")
        local m2 = require("counter")
        return m1 == m2, m1.count
        "#,
        dir_str
    );
    let (results, _) = run_with_vm(&source);
    assert_bool(&results, 0, true);
    assert_int(&results, 1, 1);
}

#[test]
fn test_require_lua_file_receives_modname() {
    use std::io::Write;

    let dir = tempfile::TempDir::new().unwrap();
    let mod_path = dir.path().join("namecheck.lua");
    let mut f = std::fs::File::create(&mod_path).unwrap();
    writeln!(f, "local name = ...").unwrap();
    writeln!(f, "return name").unwrap();

    let dir_str = dir.path().to_str().unwrap().replace('\\', "/");
    let source = format!(
        r#"
        package.path = "{}/?.lua"
        return require("namecheck")
        "#,
        dir_str
    );
    run_check_strings(&source, &["namecheck"]);
}

// ---- require error cases ----

#[test]
fn test_require_not_found() {
    let err = run_lua_err(
        r#"
        package.path = ""
        require("nonexistent_module")
        "#,
    );
    assert!(
        err.contains("module 'nonexistent_module' not found"),
        "error was: {err}"
    );
}

#[test]
fn test_require_bad_argument() {
    let err = run_lua_err("require(123)");
    assert!(err.contains("string expected"), "error was: {err}");
}

// ---- package.searchpath ----

#[test]
fn test_searchpath_not_found() {
    let (results, _) = run_with_vm(
        r#"
        local f, err = package.searchpath("nonexistent", "./?.lua")
        return f == nil, err ~= nil
        "#,
    );
    assert_bool(&results, 0, true);
    assert_bool(&results, 1, true);
}

#[test]
fn test_searchpath_found() {
    use std::io::Write;

    let dir = tempfile::TempDir::new().unwrap();
    let mod_path = dir.path().join("found.lua");
    let mut f = std::fs::File::create(&mod_path).unwrap();
    writeln!(f, "return 1").unwrap();

    let dir_str = dir.path().to_str().unwrap().replace('\\', "/");
    let source = format!(
        r#"
        local f = package.searchpath("found", "{}/?.lua")
        return f ~= nil
        "#,
        dir_str
    );
    let (results, _) = run_with_vm(&source);
    assert_bool(&results, 0, true);
}

// ---- require already loaded returns same value ----

#[test]
fn test_require_stdlib_already_loaded() {
    // Requiring a stdlib module that's in package.loaded should work
    let (results, _) = run_with_vm(
        r#"
        local m = require("math")
        return m == math
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_require_package_config_format() {
    // package.config first character should be directory separator
    run_check_strings(
        r#"
        return string.sub(package.config, 1, 1)
        "#,
        &["/"],
    );
}
