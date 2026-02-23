/// Tests for the io library.
use super::helpers::*;

// ---- io table structure ----

#[test]
fn test_io_is_table() {
    run_check_strings("return type(io)", &["table"]);
}

#[test]
fn test_io_open_is_function() {
    run_check_strings("return type(io.open)", &["function"]);
}

#[test]
fn test_io_close_is_function() {
    run_check_strings("return type(io.close)", &["function"]);
}

#[test]
fn test_io_read_is_function() {
    run_check_strings("return type(io.read)", &["function"]);
}

#[test]
fn test_io_write_is_function() {
    run_check_strings("return type(io.write)", &["function"]);
}

#[test]
fn test_io_type_is_function() {
    run_check_strings("return type(io.type)", &["function"]);
}

// ---- io.open / f:write / f:read / f:close ----

#[test]
fn test_io_open_write_read() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local f = io.open("{path}", "w")
        f:write("hello world")
        f:close()
        local f2 = io.open("{path}", "r")
        local content = f2:read("a")
        f2:close()
        return content
        "#
    );
    run_check_strings(&source, &["hello world"]);
}

#[test]
fn test_io_open_nonexistent() {
    let (results, _) = run_with_vm(
        r#"
        local f, err = io.open("/nonexistent_file_xyz", "r")
        return f == nil, err ~= nil
        "#,
    );
    assert_bool(&results, 0, true);
    assert_bool(&results, 1, true);
}

// ---- io.type ----

#[test]
fn test_io_type_open_file() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local f = io.open("{path}", "r")
        local t = io.type(f)
        f:close()
        return t
        "#
    );
    run_check_strings(&source, &["file"]);
}

#[test]
fn test_io_type_closed_file() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local f = io.open("{path}", "r")
        f:close()
        return io.type(f)
        "#
    );
    run_check_strings(&source, &["closed file"]);
}

#[test]
fn test_io_type_non_file() {
    let (results, _) = run_with_vm("return io.type(42) == nil");
    assert_bool(&results, 0, true);
}

// ---- read formats ----

#[test]
fn test_read_line() {
    use std::io::Write;
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    writeln!(tmp, "line one").unwrap();
    writeln!(tmp, "line two").unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local f = io.open("{path}", "r")
        local l1 = f:read("l")
        local l2 = f:read("l")
        f:close()
        return l1, l2
        "#
    );
    run_check_strings(&source, &["line one", "line two"]);
}

#[test]
fn test_read_all() {
    use std::io::Write;
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    write!(tmp, "all content").unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local f = io.open("{path}", "r")
        local all = f:read("a")
        f:close()
        return all
        "#
    );
    run_check_strings(&source, &["all content"]);
}

#[test]
fn test_read_bytes() {
    use std::io::Write;
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    write!(tmp, "hello world").unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local f = io.open("{path}", "r")
        local chunk = f:read(5)
        f:close()
        return chunk
        "#
    );
    run_check_strings(&source, &["hello"]);
}

#[test]
fn test_read_eof_returns_nil() {
    use std::io::Write;
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    write!(tmp, "x").unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local f = io.open("{path}", "r")
        f:read("a")  -- consume everything
        local eof = f:read("l")
        f:close()
        return eof == nil
        "#
    );
    let (results, _) = run_with_vm(&source);
    assert_bool(&results, 0, true);
}

// ---- f:seek ----

#[test]
fn test_file_seek() {
    use std::io::Write;
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    write!(tmp, "abcdefghij").unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local f = io.open("{path}", "r")
        f:seek("set", 5)
        local chunk = f:read("a")
        f:close()
        return chunk
        "#
    );
    run_check_strings(&source, &["fghij"]);
}

// ---- f:write chaining ----

#[test]
fn test_file_write_returns_file() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local f = io.open("{path}", "w")
        local r = f:write("test")
        local is_same = (io.type(r) == "file")
        f:close()
        return is_same
        "#
    );
    let (results, _) = run_with_vm(&source);
    assert_bool(&results, 0, true);
}

// ---- io.tmpfile ----

#[test]
fn test_io_tmpfile() {
    let (results, vm) = run_with_vm(
        r#"
        local f = io.tmpfile()
        f:write("temp data")
        f:seek("set", 0)
        local data = f:read("a")
        f:close()
        return data
        "#,
    );
    assert_str(&results, 0, "temp data", &vm);
}

// ---- io.lines ----

#[test]
fn test_io_lines_file() {
    use std::io::Write;
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    writeln!(tmp, "alpha").unwrap();
    writeln!(tmp, "beta").unwrap();
    writeln!(tmp, "gamma").unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local lines = {{}}
        for line in io.lines("{path}") do
            lines[#lines + 1] = line
        end
        return #lines, lines[1], lines[2], lines[3]
        "#
    );
    let (results, vm) = run_with_vm(&source);
    assert_int(&results, 0, 3);
    assert_str(&results, 1, "alpha", &vm);
    assert_str(&results, 2, "beta", &vm);
    assert_str(&results, 3, "gamma", &vm);
}

// ---- io.stdin / io.stdout / io.stderr ----

#[test]
fn test_io_stdin_exists() {
    run_check_strings("return io.type(io.stdin)", &["file"]);
}

#[test]
fn test_io_stdout_exists() {
    run_check_strings("return io.type(io.stdout)", &["file"]);
}

#[test]
fn test_io_stderr_exists() {
    run_check_strings("return io.type(io.stderr)", &["file"]);
}

// ---- io.popen stub ----

#[test]
fn test_io_popen_stub() {
    let (results, _) = run_with_vm(
        r#"
        local f, err = io.popen("echo hello")
        return f == nil, err ~= nil
        "#,
    );
    assert_bool(&results, 0, true);
    assert_bool(&results, 1, true);
}

// ---- write multiple values ----

#[test]
fn test_file_write_multiple() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_str().unwrap().replace('\\', "/");

    let source = format!(
        r#"
        local f = io.open("{path}", "w")
        f:write("hello", " ", "world")
        f:close()
        local f2 = io.open("{path}", "r")
        local content = f2:read("a")
        f2:close()
        return content
        "#
    );
    run_check_strings(&source, &["hello world"]);
}
