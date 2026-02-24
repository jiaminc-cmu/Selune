use super::helpers::*;

// ---- utf8.len ----

#[test]
fn test_utf8_len_ascii() {
    run_check_ints("return utf8.len('hello')", &[5]);
}

#[test]
fn test_utf8_len_multibyte() {
    // "résumé" in UTF-8: r(1) é(2) s(1) u(1) m(1) é(2) = 6 chars, 8 bytes
    run_check_ints("return utf8.len('r\\xC3\\xA9sum\\xC3\\xA9')", &[6]);
}

#[test]
fn test_utf8_len_empty() {
    run_check_ints("return utf8.len('')", &[0]);
}

// ---- utf8.char ----

#[test]
fn test_utf8_char_ascii() {
    run_check_strings("return utf8.char(65)", &["A"]);
}

#[test]
fn test_utf8_char_chinese() {
    // U+4E16 = 世 (3 bytes: E4 B8 96)
    // U+754C = 界 (3 bytes: E7 95 8C)
    // Total: 6 bytes
    let (results, vm) = run_with_vm("return utf8.char(0x4e16, 0x754c)");
    assert_eq!(results.len(), 1);
    let sid = results[0].as_string_id().expect("expected string");
    let bytes = vm.strings.get_bytes(sid);
    assert_eq!(bytes.len(), 6);
    // 世 = E4 B8 96
    assert_eq!(bytes[0], 0xE4);
    assert_eq!(bytes[1], 0xB8);
    assert_eq!(bytes[2], 0x96);
    // 界 = E7 95 8C
    assert_eq!(bytes[3], 0xE7);
    assert_eq!(bytes[4], 0x95);
    assert_eq!(bytes[5], 0x8C);
}

#[test]
fn test_utf8_char_nul() {
    // utf8.char(0) should produce a string containing NUL byte
    let (results, vm) = run_with_vm("return utf8.char(0)");
    assert_eq!(results.len(), 1);
    let sid = results[0].as_string_id().expect("expected string");
    let bytes = vm.strings.get_bytes(sid);
    assert_eq!(bytes.len(), 1);
    assert_eq!(bytes[0], 0x00);
}

// ---- utf8.codepoint ----

#[test]
fn test_utf8_codepoint_ascii() {
    run_check_ints("return utf8.codepoint('A')", &[65]);
}

#[test]
fn test_utf8_codepoint_range() {
    // "ABC" codepoints at positions 1 through 3
    run_check_ints("return utf8.codepoint('ABC', 1, 3)", &[65, 66, 67]);
}

// ---- utf8.char / utf8.codepoint roundtrip ----

#[test]
fn test_utf8_char_codepoint_roundtrip() {
    run_check_ints(
        "local s = utf8.char(0x41, 0xE9, 0x4E16) return utf8.codepoint(s, 1, #s)",
        &[0x41, 0xE9, 0x4E16],
    );
}

// ---- utf8.codes ----

#[test]
fn test_utf8_codes_count() {
    // Count characters using utf8.codes iterator
    run_check_ints(
        r#"
        local count = 0
        for p, c in utf8.codes("ABC") do
            count = count + 1
        end
        return count
        "#,
        &[3],
    );
}

#[test]
fn test_utf8_codes_positions_and_codepoints() {
    // Verify positions and codepoints for a multibyte string
    // "Aé" = A(1 byte at pos 1) + é(2 bytes at pos 2)
    run_check_ints(
        r#"
        local positions = {}
        local codes = {}
        local i = 0
        for p, c in utf8.codes("A\xC3\xA9") do
            i = i + 1
            positions[i] = p
            codes[i] = c
        end
        return positions[1], codes[1], positions[2], codes[2]
        "#,
        &[1, 65, 2, 0xE9],
    );
}

// ---- utf8.offset ----

#[test]
fn test_utf8_offset_basic() {
    // For "ABC", offset(s, 1) = 1, offset(s, 2) = 2, offset(s, 3) = 3
    run_check_ints("return utf8.offset('ABC', 1)", &[1]);
    run_check_ints("return utf8.offset('ABC', 2)", &[2]);
    run_check_ints("return utf8.offset('ABC', 3)", &[3]);
}

#[test]
fn test_utf8_offset_multibyte() {
    // "Aé" = A (1 byte) + é (2 bytes = C3 A9)
    // offset(s, 1) = 1 (start of first char)
    // offset(s, 2) = 2 (start of second char, at byte 2)
    run_check_ints(r#"return utf8.offset("A\xC3\xA9", 1)"#, &[1]);
    run_check_ints(r#"return utf8.offset("A\xC3\xA9", 2)"#, &[2]);
}

#[test]
fn test_utf8_offset_negative() {
    // offset(s, -1) from end: returns position of last character
    // "ABC" -> offset(s, -1) = 3
    run_check_ints(r#"return utf8.offset("ABC", -1)"#, &[3]);
}

// ---- utf8.len on invalid UTF-8 ----

#[test]
fn test_utf8_len_invalid() {
    // \xFF is not a valid UTF-8 byte
    let (results, _vm) = run_with_vm(r#"return utf8.len("hello\xFF")"#);
    assert_eq!(results.len(), 2);
    assert_nil(&results, 0);
    // Error position should be 6 (1-based, the position of \xFF)
    let pos = results[1]
        .as_integer()
        .expect("expected integer error position");
    assert_eq!(pos, 6);
}

// ---- utf8.charpattern ----

#[test]
fn test_utf8_charpattern_is_string() {
    // utf8.charpattern should be a string
    run_check_strings("return type(utf8.charpattern)", &["string"]);
}
