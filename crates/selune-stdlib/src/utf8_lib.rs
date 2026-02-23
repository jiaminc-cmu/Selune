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

/// Encode a single code point into UTF-8 bytes. Returns the number of bytes written.
fn encode_utf8(codepoint: u32, buf: &mut [u8; 4]) -> usize {
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
    } else if codepoint <= 0x10FFFF {
        buf[0] = 0xF0 | ((codepoint >> 18) as u8);
        buf[1] = 0x80 | (((codepoint >> 12) & 0x3F) as u8);
        buf[2] = 0x80 | (((codepoint >> 6) & 0x3F) as u8);
        buf[3] = 0x80 | ((codepoint & 0x3F) as u8);
        4
    } else {
        // Beyond standard Unicode but allowed in lax mode (up to 6 bytes)
        // For simplicity we only support up to 4-byte sequences (U+10FFFF)
        // since lax mode beyond that is extremely rare.
        0
    }
}

/// Decode one UTF-8 character starting at `bytes[pos]`.
/// Returns `(codepoint, next_position)` or `None` if invalid.
fn decode_utf8(bytes: &[u8], pos: usize) -> Option<(u32, usize)> {
    if pos >= bytes.len() {
        return None;
    }
    let b0 = bytes[pos];
    if b0 <= 0x7F {
        // 1-byte: 0xxxxxxx
        Some((b0 as u32, pos + 1))
    } else if b0 & 0xE0 == 0xC0 {
        // 2-byte: 110xxxxx 10xxxxxx
        if pos + 1 >= bytes.len() {
            return None;
        }
        let b1 = bytes[pos + 1];
        if b1 & 0xC0 != 0x80 {
            return None;
        }
        let cp = ((b0 as u32 & 0x1F) << 6) | (b1 as u32 & 0x3F);
        // Reject overlong encoding
        if cp < 0x80 {
            return None;
        }
        Some((cp, pos + 2))
    } else if b0 & 0xF0 == 0xE0 {
        // 3-byte: 1110xxxx 10xxxxxx 10xxxxxx
        if pos + 2 >= bytes.len() {
            return None;
        }
        let b1 = bytes[pos + 1];
        let b2 = bytes[pos + 2];
        if (b1 & 0xC0 != 0x80) || (b2 & 0xC0 != 0x80) {
            return None;
        }
        let cp = ((b0 as u32 & 0x0F) << 12) | ((b1 as u32 & 0x3F) << 6) | (b2 as u32 & 0x3F);
        // Reject overlong encoding
        if cp < 0x800 {
            return None;
        }
        Some((cp, pos + 3))
    } else if b0 & 0xF8 == 0xF0 {
        // 4-byte: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
        if pos + 3 >= bytes.len() {
            return None;
        }
        let b1 = bytes[pos + 1];
        let b2 = bytes[pos + 2];
        let b3 = bytes[pos + 3];
        if (b1 & 0xC0 != 0x80) || (b2 & 0xC0 != 0x80) || (b3 & 0xC0 != 0x80) {
            return None;
        }
        let cp = ((b0 as u32 & 0x07) << 18)
            | ((b1 as u32 & 0x3F) << 12)
            | ((b2 as u32 & 0x3F) << 6)
            | (b3 as u32 & 0x3F);
        // Reject overlong encoding and out-of-range
        if cp < 0x10000 || cp > MAX_UNICODE {
            return None;
        }
        Some((cp, pos + 4))
    } else {
        // Invalid leading byte (continuation byte or 5/6-byte sequence)
        None
    }
}

/// Check if byte at `pos` is a continuation byte (10xxxxxx).
fn is_continuation_byte(b: u8) -> bool {
    b & 0xC0 == 0x80
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
        if cp < 0 || cp > MAX_UNICODE as i64 {
            return Err(NativeError::String(format!(
                "bad argument #{} to 'utf8.char' (value out of range)",
                i + 1
            )));
        }
        let mut buf = [0u8; 4];
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

    // Return (iterator_function, s, 0)
    let iter_idx = ctx.gc.alloc_native(native_utf8_codes_iter, "utf8.codes iterator");
    Ok(vec![
        TValue::from_native(iter_idx),
        val,
        TValue::from_integer(0),
    ])
}

/// Iterator function for utf8.codes.
/// Receives (s, n) where n is the control variable (starts at 0).
/// Algorithm matches PUC-Rio Lua 5.4:
///   1. Skip continuation bytes at position n
///   2. If n >= len, return nil (done)
///   3. Decode UTF-8 at position n
///   4. Return (n+1, codepoint) -- n+1 converts 0-based to 1-based
fn native_utf8_codes_iter(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let s_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let sid = s_val.as_string_id().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'utf8.codes iterator' (string expected)".to_string())
    })?;
    let bytes = ctx.strings.get_bytes(sid).to_vec();

    let idx = ctx
        .args
        .get(1)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(0);

    let pos = idx; // 0-based byte offset
    if pos < 0 {
        // Shouldn't happen, but handle gracefully
        return Ok(vec![TValue::nil()]);
    }
    let mut pos = pos as usize;

    // Skip continuation bytes
    while pos < bytes.len() && is_continuation_byte(bytes[pos]) {
        pos += 1;
    }

    if pos >= bytes.len() {
        return Ok(vec![TValue::nil()]);
    }

    match decode_utf8(&bytes, pos) {
        Some((codepoint, _next)) => {
            // Return (1-based byte position, codepoint)
            let lua_pos = (pos + 1) as i64;
            Ok(vec![
                TValue::from_full_integer(lua_pos, ctx.gc),
                TValue::from_full_integer(codepoint as i64, ctx.gc),
            ])
        }
        None => {
            Err(NativeError::String(format!(
                "invalid UTF-8 code at byte position {}",
                pos + 1
            )))
        }
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

    // Convert 1-based Lua positions to 0-based
    let start = lua_byte_index(i, len);
    let end = lua_byte_index(j, len);

    if start > len || end > len {
        return Err(NativeError::String(
            "bad argument to 'utf8.codepoint' (out of bounds)".to_string(),
        ));
    }

    let mut results = Vec::new();
    let mut pos = start;
    // We need to decode all characters whose start byte is in [start, end]
    while pos <= end && pos < len {
        match decode_utf8(&bytes, pos) {
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

    // Convert 1-based Lua positions to 0-based byte indices
    let start = lua_byte_index(i, len);
    // For j, in Lua utf8.len, j=-1 means the last byte (inclusive)
    let end_inclusive = lua_byte_index(j, len);

    if start > len {
        return Err(NativeError::String(
            "bad argument #2 to 'utf8.len' (initial position out of bounds)".to_string(),
        ));
    }

    // Count UTF-8 characters in the range [start, end_inclusive]
    let mut count: i64 = 0;
    let mut pos = start;
    let limit = if end_inclusive < len {
        end_inclusive + 1
    } else {
        len
    };

    while pos < limit {
        match decode_utf8(&bytes, pos) {
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
    let mut pos = if i > 0 {
        (i as usize).saturating_sub(1)
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

    // pos must be at a valid position: either at len (one past end) or at a non-continuation byte
    if pos < len && is_continuation_byte(bytes[pos]) {
        return Err(NativeError::String(
            "bad argument #3 to 'utf8.offset' (initial position is a continuation byte)"
                .to_string(),
        ));
    }

    if n == 0 {
        // n=0: find the start of the character at byte position i
        // pos is already at a non-continuation byte or at len
        // Just back up over any continuation bytes (but we verified it's not one)
        // Return 1-based position
        return Ok(vec![TValue::from_full_integer((pos + 1) as i64, ctx.gc)]);
    } else if n > 0 {
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
            // Skip current character
            match decode_utf8(&bytes, pos) {
                Some((_cp, next)) => {
                    pos = next;
                }
                None => {
                    return Ok(vec![TValue::nil()]);
                }
            }
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
