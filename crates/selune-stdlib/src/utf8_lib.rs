//! Lua 5.4 utf8 library.

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;

/// Maximum valid Unicode code point (non-lax mode).
const MAX_UNICODE: u32 = 0x10FFFF;

/// Register the utf8 library into _ENV.
pub fn register(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) {
    let utf8_table = gc.alloc_table(0, 8);

    register_fn(gc, utf8_table, strings, "char", native_utf8_char);
    register_fn(gc, utf8_table, strings, "codes", native_utf8_codes);
    register_fn(gc, utf8_table, strings, "codepoint", native_utf8_codepoint);
    register_fn(gc, utf8_table, strings, "len", native_utf8_len);
    register_fn(gc, utf8_table, strings, "offset", native_utf8_offset);

    // utf8.charpattern = "[\0-\x7F\xC2-\xFD][\x80-\xBF]*"
    let pattern_bytes: &[u8] = b"[\x00-\x7F\xC2-\xFD][\x80-\xBF]*";
    let pattern_sid = strings.intern_or_create(pattern_bytes);
    let cp_name = strings.intern(b"charpattern");
    gc.get_table_mut(utf8_table)
        .raw_set_str(cp_name, TValue::from_string_id(pattern_sid));

    let name = strings.intern(b"utf8");
    gc.get_table_mut(env_idx)
        .raw_set_str(name, TValue::from_table(utf8_table));
}

fn register_fn(
    gc: &mut GcHeap,
    table: GcIdx<Table>,
    strings: &mut StringInterner,
    name: &'static str,
    func: fn(&mut NativeContext) -> Result<Vec<TValue>, NativeError>,
) {
    let idx = gc.alloc_native(func, name);
    let val = TValue::from_native(idx);
    let key = strings.intern(name.as_bytes());
    gc.get_table_mut(table).raw_set_str(key, val);
}

// ---------------------------------------------------------------------------
// UTF-8 encoding/decoding helpers
// ---------------------------------------------------------------------------

/// Maximum codepoint in lax/non-strict mode (original UTF-8).
const MAX_LAX: u32 = 0x7FFFFFFF;

/// Check if a codepoint is a surrogate (U+D800..U+DFFF).
fn is_surrogate(cp: u32) -> bool {
    cp >= 0xD800 && cp <= 0xDFFF
}

/// Encode a single code point into UTF-8 bytes (up to 6 bytes for lax mode).
/// Returns the number of bytes written.
fn encode_utf8(codepoint: u32, buf: &mut [u8; 6]) -> usize {
    if codepoint <= 0x7F {
        buf[0] = codepoint as u8;
        1
    } else if codepoint <= 0x7FF {
        buf[0] = 0xC0 | ((codepoint >> 6) as u8);
        buf[1] = 0x80 | ((codepoint & 0x3F) as u8);
        2
    } else if codepoint <= 0xFFFF {
        buf[0] = 0xE0 | ((codepoint >> 12) as u8);
        buf[1] = 0x80 | (((codepoint >> 6) & 0x3F) as u8);
        buf[2] = 0x80 | ((codepoint & 0x3F) as u8);
        3
    } else if codepoint <= 0x1FFFFF {
        buf[0] = 0xF0 | ((codepoint >> 18) as u8);
        buf[1] = 0x80 | (((codepoint >> 12) & 0x3F) as u8);
        buf[2] = 0x80 | (((codepoint >> 6) & 0x3F) as u8);
        buf[3] = 0x80 | ((codepoint & 0x3F) as u8);
        4
    } else if codepoint <= 0x3FFFFFF {
        buf[0] = 0xF8 | ((codepoint >> 24) as u8);
        buf[1] = 0x80 | (((codepoint >> 18) & 0x3F) as u8);
        buf[2] = 0x80 | (((codepoint >> 12) & 0x3F) as u8);
        buf[3] = 0x80 | (((codepoint >> 6) & 0x3F) as u8);
        buf[4] = 0x80 | ((codepoint & 0x3F) as u8);
        5
    } else if codepoint <= 0x7FFFFFFF {
        buf[0] = 0xFC | ((codepoint >> 30) as u8);
        buf[1] = 0x80 | (((codepoint >> 24) & 0x3F) as u8);
        buf[2] = 0x80 | (((codepoint >> 18) & 0x3F) as u8);
        buf[3] = 0x80 | (((codepoint >> 12) & 0x3F) as u8);
        buf[4] = 0x80 | (((codepoint >> 6) & 0x3F) as u8);
        buf[5] = 0x80 | ((codepoint & 0x3F) as u8);
        6
    } else {
        0
    }
}

/// Decode one UTF-8 character starting at `bytes[pos]` in strict mode.
/// Rejects surrogates (D800-DFFF) and codepoints > 10FFFF.
/// Returns `(codepoint, next_position)` or `None` if invalid.
fn decode_utf8(bytes: &[u8], pos: usize) -> Option<(u32, usize)> {
    let (cp, next) = decode_utf8_raw(bytes, pos)?;
    // Strict mode: reject surrogates and values > MAX_UNICODE
    if is_surrogate(cp) || cp > MAX_UNICODE {
        return None;
    }
    Some((cp, next))
}

/// Decode one UTF-8 character in lax mode (allows surrogates, 5/6 byte sequences).
fn decode_utf8_lax(bytes: &[u8], pos: usize) -> Option<(u32, usize)> {
    decode_utf8_raw(bytes, pos)
}

/// Raw UTF-8 decoder supporting up to 6-byte sequences.
/// Does NOT reject surrogates or out-of-range values.
/// Rejects overlong encodings.
fn decode_utf8_raw(bytes: &[u8], pos: usize) -> Option<(u32, usize)> {
    if pos >= bytes.len() {
        return None;
    }
    let b0 = bytes[pos];
    if b0 <= 0x7F {
        Some((b0 as u32, pos + 1))
    } else if b0 & 0xE0 == 0xC0 {
        if pos + 1 >= bytes.len() { return None; }
        let b1 = bytes[pos + 1];
        if b1 & 0xC0 != 0x80 { return None; }
        let cp = ((b0 as u32 & 0x1F) << 6) | (b1 as u32 & 0x3F);
        if cp < 0x80 { return None; }
        Some((cp, pos + 2))
    } else if b0 & 0xF0 == 0xE0 {
        if pos + 2 >= bytes.len() { return None; }
        let b1 = bytes[pos + 1];
        let b2 = bytes[pos + 2];
        if (b1 & 0xC0 != 0x80) || (b2 & 0xC0 != 0x80) { return None; }
        let cp = ((b0 as u32 & 0x0F) << 12) | ((b1 as u32 & 0x3F) << 6) | (b2 as u32 & 0x3F);
        if cp < 0x800 { return None; }
        Some((cp, pos + 3))
    } else if b0 & 0xF8 == 0xF0 {
        if pos + 3 >= bytes.len() { return None; }
        let b1 = bytes[pos + 1];
        let b2 = bytes[pos + 2];
        let b3 = bytes[pos + 3];
        if (b1 & 0xC0 != 0x80) || (b2 & 0xC0 != 0x80) || (b3 & 0xC0 != 0x80) { return None; }
        let cp = ((b0 as u32 & 0x07) << 18)
            | ((b1 as u32 & 0x3F) << 12)
            | ((b2 as u32 & 0x3F) << 6)
            | (b3 as u32 & 0x3F);
        if cp < 0x10000 { return None; }
        Some((cp, pos + 4))
    } else if b0 & 0xFC == 0xF8 {
        // 5-byte: 111110xx
        if pos + 4 >= bytes.len() { return None; }
        for k in 1..5 {
            if bytes[pos + k] & 0xC0 != 0x80 { return None; }
        }
        let cp = ((b0 as u32 & 0x03) << 24)
            | ((bytes[pos + 1] as u32 & 0x3F) << 18)
            | ((bytes[pos + 2] as u32 & 0x3F) << 12)
            | ((bytes[pos + 3] as u32 & 0x3F) << 6)
            | (bytes[pos + 4] as u32 & 0x3F);
        if cp < 0x200000 { return None; }
        Some((cp, pos + 5))
    } else if b0 & 0xFE == 0xFC {
        // 6-byte: 1111110x
        if pos + 5 >= bytes.len() { return None; }
        for k in 1..6 {
            if bytes[pos + k] & 0xC0 != 0x80 { return None; }
        }
        let cp = ((b0 as u32 & 0x01) << 30)
            | ((bytes[pos + 1] as u32 & 0x3F) << 24)
            | ((bytes[pos + 2] as u32 & 0x3F) << 18)
            | ((bytes[pos + 3] as u32 & 0x3F) << 12)
            | ((bytes[pos + 4] as u32 & 0x3F) << 6)
            | (bytes[pos + 5] as u32 & 0x3F);
        if cp < 0x4000000 { return None; }
        Some((cp, pos + 6))
    } else {
        None
    }
}

/// Check if byte at `pos` is a continuation byte (10xxxxxx).
fn is_continuation_byte(b: u8) -> bool {
    b & 0xC0 == 0x80
}

/// Get expected byte length of a UTF-8 character from its leading byte.
fn utf8_char_len(b: u8) -> usize {
    if b <= 0x7F {
        1
    } else if b & 0xE0 == 0xC0 {
        2
    } else if b & 0xF0 == 0xE0 {
        3
    } else if b & 0xF8 == 0xF0 {
        4
    } else if b & 0xFC == 0xF8 {
        5
    } else if b & 0xFE == 0xFC {
        6
    } else {
        // Continuation byte or invalid - treat as 1 byte
        1
    }
}

// ---------------------------------------------------------------------------
// utf8.char(...)
// ---------------------------------------------------------------------------

fn native_utf8_char(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let mut result = Vec::new();
    for (i, arg) in ctx.args.iter().enumerate() {
        let cp = arg.as_full_integer(ctx.gc).ok_or_else(|| {
            NativeError::String(format!(
                "bad argument #{} to 'utf8.char' (number expected)",
                i + 1
            ))
        })?;
        if cp < 0 || cp > MAX_LAX as i64 {
            return Err(NativeError::String(format!(
                "bad argument #{} to 'utf8.char' (value out of range)",
                i + 1
            )));
        }
        let mut buf = [0u8; 6];
        let n = encode_utf8(cp as u32, &mut buf);
        result.extend_from_slice(&buf[..n]);
    }
    let sid = ctx.strings.intern_or_create(&result);
    Ok(vec![TValue::from_string_id(sid)])
}

// ---------------------------------------------------------------------------
// utf8.codes(s [, lax])
// ---------------------------------------------------------------------------

fn native_utf8_codes(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    // Validate that argument 1 is a string
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if val.as_string_id().is_none() {
        return Err(NativeError::String(
            "bad argument #1 to 'utf8.codes' (string expected)".to_string(),
        ));
    }

    let lax = ctx
        .args
        .get(1)
        .map(|v| v.is_truthy())
        .unwrap_or(false);

    // Return (iterator_function, s, 0) — use lax or strict iterator
    let iter_fn = if lax {
        native_utf8_codes_iter_lax
    } else {
        native_utf8_codes_iter
    };
    let iter_idx = ctx.gc.alloc_native(iter_fn, "utf8.codes iterator");
    Ok(vec![
        TValue::from_native(iter_idx),
        val,
        TValue::from_integer(0),
    ])
}

/// Strict iterator for utf8.codes.
fn native_utf8_codes_iter(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    utf8_codes_iter_impl(ctx, false)
}

/// Lax iterator for utf8.codes.
fn native_utf8_codes_iter_lax(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    utf8_codes_iter_impl(ctx, true)
}

/// Iterator implementation for utf8.codes.
/// Receives (s, n) where n is the control variable.
/// n starts at 0 (before the string).
fn utf8_codes_iter_impl(ctx: &mut NativeContext, lax: bool) -> Result<Vec<TValue>, NativeError> {
    let s_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let sid = s_val.as_string_id().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'utf8.codes iterator' (string expected)".to_string())
    })?;
    let bytes = ctx.strings.get_bytes(sid).to_vec();
    let len = bytes.len();

    let n = ctx
        .args
        .get(1)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(0);

    // n is the 1-based position of the previous character (or 0 at start)
    if n < 0 || (n > 0 && n as usize > len) {
        return Ok(vec![TValue::nil()]);
    }

    let next_pos_0based = if n == 0 {
        0usize
    } else {
        let prev_0 = (n as usize) - 1;
        if prev_0 >= len {
            return Ok(vec![TValue::nil()]);
        }
        let char_len = utf8_char_len(bytes[prev_0]);
        prev_0 + char_len
    };

    if next_pos_0based >= len {
        return Ok(vec![TValue::nil()]);
    }

    let decoded = if lax {
        decode_utf8_lax(&bytes, next_pos_0based)
    } else {
        decode_utf8(&bytes, next_pos_0based)
    };

    match decoded {
        Some((codepoint, _next)) => {
            let lua_pos = (next_pos_0based + 1) as i64;
            Ok(vec![
                TValue::from_full_integer(lua_pos, ctx.gc),
                TValue::from_full_integer(codepoint as i64, ctx.gc),
            ])
        }
        None => Err(NativeError::String(format!(
            "invalid UTF-8 code at byte position {}",
            next_pos_0based + 1
        ))),
    }
}

// ---------------------------------------------------------------------------
// utf8.codepoint(s [, i [, j [, lax]]])
// ---------------------------------------------------------------------------

fn native_utf8_codepoint(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let sid = val.as_string_id().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'utf8.codepoint' (string expected)".to_string())
    })?;
    let bytes = ctx.strings.get_bytes(sid).to_vec();
    let len = bytes.len();

    let i = ctx
        .args
        .get(1)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(1);
    let j = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(i);

    // Convert 1-based Lua positions to 0-based, with bounds checking.
    // Use posrelatI semantics: positive i means i-1 (0-based), clamped to [0, len].
    // Negative i means len + i (wrapping from end).
    let start_raw = if i >= 1 {
        (i as isize) - 1
    } else if i < 0 {
        (len as isize) + (i as isize)
    } else {
        -1 // i == 0, will be caught by bounds check
    };
    // Bounds check: start must be in [0, len-1] for codepoint
    if start_raw < 0 || start_raw as usize >= len {
        // But if j would result in end < start, it's just an empty range
        let end_raw = if j >= 1 { (j as isize) - 1 } else if j < 0 { (len as isize) + (j as isize) } else { -1 };
        if end_raw < start_raw {
            return Ok(vec![]); // empty range
        }
        return Err(NativeError::String(
            "bad argument #2 to 'utf8.codepoint' (out of bounds)".to_string(),
        ));
    }
    let start = start_raw as usize;

    let end_raw = if j >= 1 {
        (j as isize) - 1
    } else if j < 0 {
        (len as isize) + (j as isize)
    } else {
        -1 // j == 0
    };
    if end_raw < 0 || end_raw as usize >= len {
        if end_raw < start_raw {
            return Ok(vec![]); // empty range
        }
        return Err(NativeError::String(
            "bad argument #3 to 'utf8.codepoint' (out of bounds)".to_string(),
        ));
    }
    let end = end_raw as usize;

    // If start > end, empty range
    if start > end {
        return Ok(vec![]);
    }

    // 4th argument: lax/nonstrict mode
    let lax = ctx
        .args
        .get(3)
        .map(|v| v.is_truthy())
        .unwrap_or(false);

    let mut results = Vec::new();
    let mut pos = start;
    // We need to decode all characters whose start byte is in [start, end]
    while pos <= end && pos < len {
        let decoded = if lax {
            decode_utf8_lax(&bytes, pos)
        } else {
            decode_utf8(&bytes, pos)
        };
        match decoded {
            Some((codepoint, next)) => {
                results.push(TValue::from_full_integer(codepoint as i64, ctx.gc));
                pos = next;
            }
            None => {
                return Err(NativeError::String(format!(
                    "invalid UTF-8 code at byte position {}",
                    pos + 1
                )));
            }
        }
    }

    Ok(results)
}

// ---------------------------------------------------------------------------
// utf8.len(s [, i [, j]])
// ---------------------------------------------------------------------------

fn native_utf8_len(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let sid = val.as_string_id().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'utf8.len' (string expected)".to_string())
    })?;
    let bytes = ctx.strings.get_bytes(sid).to_vec();
    let len = bytes.len();

    let i = ctx
        .args
        .get(1)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(1);
    let j = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(-1);

    // Validate bounds: i must be in [1, #s+1], j must be in [-#s, #s]
    // (Lua 5.4 reference: initial position out of bounds, final position out of bounds)
    // Convert 1-based Lua positions to 0-based byte indices
    let start = if i >= 1 {
        let s = (i as usize) - 1;
        if s > len {
            return Err(NativeError::String(
                "bad argument #2 to 'utf8.len' (initial position out of bounds)".to_string(),
            ));
        }
        s
    } else if i < 0 {
        let back = (-i) as usize;
        if back > len {
            return Err(NativeError::String(
                "bad argument #2 to 'utf8.len' (initial position out of bounds)".to_string(),
            ));
        }
        len - back
    } else {
        // i == 0 is out of bounds
        return Err(NativeError::String(
            "bad argument #2 to 'utf8.len' (initial position out of bounds)".to_string(),
        ));
    };

    let end_inclusive_raw = if j >= 1 {
        let e = (j as usize) - 1;
        if e >= len {
            return Err(NativeError::String(
                "bad argument #3 to 'utf8.len' (final position out of bounds)".to_string(),
            ));
        }
        e as isize
    } else if j < 0 {
        // Negative index: j=-1 means last byte
        // For empty string (len=0): -1 maps to index -1 (before start), range is empty
        (len as isize) + (j as isize)
    } else {
        // j == 0 is out of bounds
        return Err(NativeError::String(
            "bad argument #3 to 'utf8.len' (final position out of bounds)".to_string(),
        ));
    };

    // If end < start, the range is empty → return 0
    if end_inclusive_raw < 0 || (end_inclusive_raw as usize) < start {
        return Ok(vec![TValue::from_full_integer(0, ctx.gc)]);
    }
    let end_inclusive = end_inclusive_raw as usize;

    // 4th argument: lax/nonstrict mode
    let lax = ctx
        .args
        .get(3)
        .map(|v| v.is_truthy())
        .unwrap_or(false);

    // Count UTF-8 characters in the range [start, end_inclusive]
    let mut count: i64 = 0;
    let mut pos = start;
    let limit = if end_inclusive < len {
        end_inclusive + 1
    } else {
        len
    };

    while pos < limit {
        let decoded = if lax {
            decode_utf8_lax(&bytes, pos)
        } else {
            decode_utf8(&bytes, pos)
        };
        match decoded {
            Some((_cp, next)) => {
                count += 1;
                pos = next;
            }
            None => {
                // Return nil + error byte position (1-based)
                return Ok(vec![
                    TValue::nil(),
                    TValue::from_full_integer((pos + 1) as i64, ctx.gc),
                ]);
            }
        }
    }

    Ok(vec![TValue::from_full_integer(count, ctx.gc)])
}

// ---------------------------------------------------------------------------
// utf8.offset(s, n [, i])
// ---------------------------------------------------------------------------

fn native_utf8_offset(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let sid = val.as_string_id().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'utf8.offset' (string expected)".to_string())
    })?;
    let bytes = ctx.strings.get_bytes(sid).to_vec();
    let len = bytes.len();

    let n = ctx
        .args
        .get(1)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .ok_or_else(|| {
            NativeError::String(
                "bad argument #2 to 'utf8.offset' (number expected)".to_string(),
            )
        })?;

    // Default i: if n >= 0, i = 1; if n < 0, i = len + 1 (one past the end)
    let default_i = if n >= 0 { 1i64 } else { (len as i64) + 1 };
    let i = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(default_i);

    // Convert to 0-based
    // Valid range for i: 1 to #s+1 (positive), -#s to -1 (negative), and 0 is invalid.
    let mut pos = if i > 0 {
        let p = (i as usize).saturating_sub(1);
        if p > len {
            return Err(NativeError::String(
                "bad argument #3 to 'utf8.offset' (position out of bounds)".to_string(),
            ));
        }
        p
    } else if i < 0 {
        let back = (-i) as usize;
        if back > len {
            return Err(NativeError::String(
                "bad argument #3 to 'utf8.offset' (position out of bounds)".to_string(),
            ));
        }
        len - back
    } else {
        return Err(NativeError::String(
            "bad argument #3 to 'utf8.offset' (position out of bounds)".to_string(),
        ));
    };

    if n == 0 {
        // n=0: find the start of the character containing byte at position i.
        // The initial position CAN be a continuation byte; scan backward.
        while pos > 0 && pos < len && is_continuation_byte(bytes[pos]) {
            pos -= 1;
        }
        return Ok(vec![TValue::from_full_integer((pos + 1) as i64, ctx.gc)]);
    }

    // For n != 0, pos must be at a valid position: either at len or at a non-continuation byte
    if pos < len && is_continuation_byte(bytes[pos]) {
        return Err(NativeError::String(
            "bad argument #3 to 'utf8.offset' (initial position is a continuation byte)"
                .to_string(),
        ));
    }

    if n > 0 {
        // Move forward n characters from position pos
        // n=1 means the character at pos, n=2 means the next one, etc.
        let mut remaining = n;
        // n=1: we want the position of the character starting at pos
        // But we need to move forward. Actually, for n >= 1:
        // The character at pos counts as the first one.
        // So n=1 returns pos itself.
        // n=2 means skip one character forward from pos.
        remaining -= 1; // The character at pos counts as #1
        while remaining > 0 && pos < len {
            // Skip current character using leading byte to determine length
            let char_len = utf8_char_len(bytes[pos]);
            pos += char_len;
            remaining -= 1;
        }
        if remaining > 0 {
            // Ran out of string
            return Ok(vec![TValue::nil()]);
        }
        // If pos is exactly len (one past end for the last char's forward movement), return len+1
        Ok(vec![TValue::from_full_integer((pos + 1) as i64, ctx.gc)])
    } else {
        // n < 0: move backward |n| characters from position pos
        // n=-1 means the character BEFORE the one at pos (or the last char if pos is at end)
        let mut remaining = (-n) as usize;
        // When pos is at len (one past end), first move back to find the last char
        if pos == len && remaining > 0 {
            // Back up to the start of the last character
            if pos == 0 {
                return Ok(vec![TValue::nil()]);
            }
            pos -= 1;
            while pos > 0 && is_continuation_byte(bytes[pos]) {
                pos -= 1;
            }
            remaining -= 1;
        }
        while remaining > 0 {
            if pos == 0 {
                return Ok(vec![TValue::nil()]);
            }
            pos -= 1;
            while pos > 0 && is_continuation_byte(bytes[pos]) {
                pos -= 1;
            }
            remaining -= 1;
        }
        Ok(vec![TValue::from_full_integer((pos + 1) as i64, ctx.gc)])
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Convert a 1-based Lua byte index (possibly negative) to a 0-based index.
/// Negative indices count from the end (-1 = last byte).
fn lua_byte_index(i: i64, len: usize) -> usize {
    if i >= 0 {
        if i == 0 {
            0
        } else {
            ((i as usize).saturating_sub(1)).min(len)
        }
    } else {
        let back = (-i) as usize;
        if back > len {
            0
        } else {
            len - back
        }
    }
}
