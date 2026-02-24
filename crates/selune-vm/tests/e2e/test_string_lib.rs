use super::helpers::*;

// ---- string.len ----

#[test]
fn test_string_len() {
    run_check_ints("return string.len('hello')", &[5]);
}

#[test]
fn test_string_len_empty() {
    run_check_ints("return string.len('')", &[0]);
}

// ---- string.byte ----

#[test]
fn test_string_byte_single() {
    run_check_ints("return string.byte('A')", &[65]);
}

#[test]
fn test_string_byte_range() {
    run_check_ints("return string.byte('ABC', 1, 3)", &[65, 66, 67]);
}

#[test]
fn test_string_byte_negative_index() {
    run_check_ints("return string.byte('hello', -1)", &[111]); // 'o'
}

// ---- string.char ----

#[test]
fn test_string_char() {
    run_check_strings("return string.char(72, 101, 108, 108, 111)", &["Hello"]);
}

#[test]
fn test_string_char_single() {
    run_check_strings("return string.char(65)", &["A"]);
}

// ---- string.sub ----

#[test]
fn test_string_sub_basic() {
    run_check_strings("return string.sub('Hello World', 1, 5)", &["Hello"]);
}

#[test]
fn test_string_sub_negative() {
    run_check_strings("return string.sub('Hello', -3)", &["llo"]);
}

#[test]
fn test_string_sub_from_start() {
    run_check_strings("return string.sub('abcdef', 3)", &["cdef"]);
}

#[test]
fn test_string_sub_empty_range() {
    run_check_strings("return string.sub('hello', 3, 2)", &[""]);
}

// ---- string.rep ----

#[test]
fn test_string_rep() {
    run_check_strings("return string.rep('ab', 3)", &["ababab"]);
}

#[test]
fn test_string_rep_with_sep() {
    run_check_strings("return string.rep('ab', 3, ',')", &["ab,ab,ab"]);
}

#[test]
fn test_string_rep_zero() {
    run_check_strings("return string.rep('x', 0)", &[""]);
}

// ---- string.reverse ----

#[test]
fn test_string_reverse() {
    run_check_strings("return string.reverse('hello')", &["olleh"]);
}

#[test]
fn test_string_reverse_empty() {
    run_check_strings("return string.reverse('')", &[""]);
}

// ---- string.upper / string.lower ----

#[test]
fn test_string_upper() {
    run_check_strings("return string.upper('hello')", &["HELLO"]);
}

#[test]
fn test_string_lower() {
    run_check_strings("return string.lower('HELLO')", &["hello"]);
}

#[test]
fn test_string_upper_mixed() {
    run_check_strings("return string.upper('Hello World')", &["HELLO WORLD"]);
}

// ---- string.format ----

#[test]
fn test_format_string() {
    run_check_strings(
        "return string.format('hello %s', 'world')",
        &["hello world"],
    );
}

#[test]
fn test_format_integer() {
    run_check_strings(
        "return string.format('%d + %d = %d', 1, 2, 3)",
        &["1 + 2 = 3"],
    );
}

#[test]
fn test_format_float() {
    run_check_strings("return string.format('%.2f', 3.14159)", &["3.14"]);
}

#[test]
fn test_format_hex() {
    run_check_strings("return string.format('%x', 255)", &["ff"]);
}

#[test]
fn test_format_hex_upper() {
    run_check_strings("return string.format('%X', 255)", &["FF"]);
}

#[test]
fn test_format_octal() {
    run_check_strings("return string.format('%o', 8)", &["10"]);
}

#[test]
fn test_format_percent() {
    run_check_strings("return string.format('100%%')", &["100%"]);
}

#[test]
fn test_format_padded() {
    run_check_strings("return string.format('%05d', 42)", &["00042"]);
}

#[test]
fn test_format_quoted() {
    run_check_strings(
        r#"return string.format('%q', 'hello "world"')"#,
        &[r#""hello \"world\"""#],
    );
}

#[test]
fn test_format_char() {
    run_check_strings("return string.format('%c', 65)", &["A"]);
}

// ---- string.find ----

#[test]
fn test_find_plain() {
    run_check_ints(
        "return string.find('hello world', 'world', 1, true)",
        &[7, 11],
    );
}

#[test]
fn test_find_not_found() {
    let r = run_lua("return string.find('hello', 'xyz')");
    assert_nil(&r, 0);
}

#[test]
fn test_find_pattern() {
    run_check_ints("return string.find('hello123', '%d+')", &[6, 8]);
}

#[test]
fn test_find_with_captures() {
    // string.find with captures returns start, end, captures...
    let r = run_lua("return string.find('hello123world', '(%d+)')");
    assert_int(&r, 0, 6);
    assert_int(&r, 1, 8);
    // Third result should be the capture "123"
    assert_eq!(r.len(), 3);
}

#[test]
fn test_find_from_position() {
    run_check_ints("return string.find('abcabc', 'abc', 2)", &[4, 6]);
}

// ---- string.match ----

#[test]
fn test_match_basic() {
    run_check_strings("return string.match('hello123', '%d+')", &["123"]);
}

#[test]
fn test_match_captures() {
    run_check_strings(
        "return string.match('2023-01-15', '(%d+)-(%d+)-(%d+)')",
        &["2023", "01", "15"],
    );
}

#[test]
fn test_match_no_match() {
    let r = run_lua("return string.match('hello', '%d+')");
    assert_nil(&r, 0);
}

// ---- string.gmatch ----

#[test]
fn test_gmatch_words() {
    run_check_strings(
        r#"
        local t = {}
        for w in string.gmatch("hello world foo", "%a+") do
            t[#t+1] = w
        end
        return t[1], t[2], t[3]
        "#,
        &["hello", "world", "foo"],
    );
}

#[test]
fn test_gmatch_captures() {
    run_check_strings(
        r#"
        local keys = {}
        local vals = {}
        for k, v in string.gmatch("a=1,b=2,c=3", "(%a)=(%d)") do
            keys[#keys+1] = k
            vals[#vals+1] = v
        end
        return keys[1], vals[1], keys[2], vals[2], keys[3], vals[3]
        "#,
        &["a", "1", "b", "2", "c", "3"],
    );
}

#[test]
fn test_gmatch_digits() {
    run_check_strings(
        r#"
        local t = {}
        for d in string.gmatch("abc123def456", "%d+") do
            t[#t+1] = d
        end
        return t[1], t[2]
        "#,
        &["123", "456"],
    );
}

// ---- string.gsub ----

#[test]
fn test_gsub_string_replacement() {
    run_check_strings(
        "local r, n = string.gsub('hello world', 'world', 'lua') return r",
        &["hello lua"],
    );
}

#[test]
fn test_gsub_count() {
    run_check_ints("local r, n = string.gsub('aaa', 'a', 'b') return n", &[3]);
}

#[test]
fn test_gsub_with_max() {
    run_check_strings(
        "local r, n = string.gsub('aaa', 'a', 'b', 2) return r",
        &["bba"],
    );
}

#[test]
fn test_gsub_pattern() {
    run_check_strings(
        "local r = string.gsub('hello 123 world 456', '%d+', 'NUM') return r",
        &["hello NUM world NUM"],
    );
}

#[test]
fn test_gsub_capture_reference() {
    run_check_strings(
        "local r = string.gsub('hello', '(h)(e)', '%2%1') return r",
        &["ehllo"],
    );
}

#[test]
fn test_gsub_table_replacement() {
    run_check_strings(
        r#"
        local t = {hello = "HI", world = "EARTH"}
        local r = string.gsub("hello world", "(%a+)", t)
        return r
        "#,
        &["HI EARTH"],
    );
}

#[test]
fn test_gsub_function_replacement() {
    run_check_strings(
        r#"
        local r = string.gsub("hello world", "(%a+)", function(w)
            return string.upper(w)
        end)
        return r
        "#,
        &["HELLO WORLD"],
    );
}

#[test]
fn test_gsub_function_returning_false() {
    run_check_strings(
        r#"
        local r = string.gsub("hello world", "(%a+)", function(w)
            if w == "hello" then return "HI" end
            return false
        end)
        return r
        "#,
        &["HI world"],
    );
}

// ---- Pattern edge cases ----

#[test]
fn test_find_anchored() {
    run_check_ints("return string.find('hello', '^hello$')", &[1, 5]);
}

#[test]
fn test_find_anchored_no_match() {
    let r = run_lua("return string.find('hello world', '^world')");
    assert_nil(&r, 0);
}

#[test]
fn test_match_character_classes() {
    run_check_strings("return string.match('abc123', '%a+')", &["abc"]);
}

#[test]
fn test_match_dot() {
    run_check_strings("return string.match('hello', '...')", &["hel"]);
}

#[test]
fn test_gsub_empty_match() {
    // Empty pattern matches everywhere
    run_check_strings(
        "local r = string.gsub('abc', '', '-') return r",
        &["-a-b-c-"],
    );
}

// ---- Combined / integration tests ----

#[test]
fn test_string_format_with_gsub() {
    run_check_strings(
        r#"
        local name = "world"
        local greeting = string.format("hello %s!", name)
        local r = string.gsub(greeting, "hello", "hi")
        return r
        "#,
        &["hi world!"],
    );
}

#[test]
fn test_gmatch_count() {
    run_check_ints(
        r#"
        local count = 0
        for _ in string.gmatch("a b c d e", "%a") do
            count = count + 1
        end
        return count
        "#,
        &[5],
    );
}

#[test]
fn test_string_rep_and_find() {
    run_check_ints(
        r#"
        local s = string.rep("ab", 5)
        local i, j = string.find(s, "abab", 1, true)
        return i, j
        "#,
        &[1, 4],
    );
}

#[test]
fn test_string_sub_and_upper() {
    run_check_strings(
        r#"
        local s = "hello world"
        local first = string.upper(string.sub(s, 1, 1))
        local rest = string.sub(s, 2)
        return first .. rest
        "#,
        &["Hello world"],
    );
}

#[test]
fn test_match_negative_index() {
    // string.find with negative init
    run_check_ints("return string.find('hello', 'lo', -3)", &[4, 5]);
}

#[test]
fn test_format_scientific() {
    run_check_strings("return string.format('%e', 100000.0)", &["1.000000e+05"]);
    // Might need platform-specific handling; let's also test %g
}

#[test]
fn test_format_g() {
    run_check_strings("return string.format('%g', 100.0)", &["100"]);
}

#[test]
fn test_format_g_small() {
    run_check_strings("return string.format('%g', 0.00123)", &["0.00123"]);
}

#[test]
fn test_byte_char_roundtrip() {
    run_check_strings("return string.char(string.byte('A'))", &["A"]);
}

#[test]
fn test_find_set_pattern() {
    run_check_ints("return string.find('hello', '[el]+')", &[2, 4]);
}

#[test]
fn test_match_quantifiers() {
    run_check_strings("return string.match('aabbb', 'a+b-')", &["aa"]);
}

#[test]
fn test_gsub_no_match() {
    run_check_strings(
        "local r = string.gsub('hello', 'xyz', 'abc') return r",
        &["hello"],
    );
}

#[test]
fn test_format_left_align() {
    run_check_strings("return string.format('%-10s|', 'hi')", &["hi        |"]);
}

#[test]
fn test_format_integer_width() {
    run_check_strings("return string.format('%10d', 42)", &["        42"]);
}
