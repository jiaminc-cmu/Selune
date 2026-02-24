//! Lua 5.4 table library.

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError, NativeFunction};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;

/// Result from table library registration.
pub struct TableLibIndices {
    pub sort_idx: GcIdx<NativeFunction>,
    pub move_idx: GcIdx<NativeFunction>,
    pub insert_idx: GcIdx<NativeFunction>,
    pub remove_idx: GcIdx<NativeFunction>,
    pub concat_idx: GcIdx<NativeFunction>,
    pub unpack_idx: GcIdx<NativeFunction>,
}

/// Register the table library into _ENV.
pub fn register(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) -> TableLibIndices {
    let table_table = gc.alloc_table(0, 16);

    // table.insert/remove are special — need VM access for __len/__index/__newindex metamethods
    let insert_idx = gc.alloc_native(native_table_insert_stub, "insert");
    let insert_val = TValue::from_native(insert_idx);
    let insert_name = strings.intern(b"insert");
    gc.get_table_mut(table_table)
        .raw_set_str(insert_name, insert_val);

    let remove_idx = gc.alloc_native(native_table_remove_stub, "remove");
    let remove_val = TValue::from_native(remove_idx);
    let remove_name = strings.intern(b"remove");
    gc.get_table_mut(table_table)
        .raw_set_str(remove_name, remove_val);
    // table.concat/unpack are special — need VM access for __len/__index metamethods
    let concat_idx = gc.alloc_native(native_table_concat_stub, "concat");
    let concat_val = TValue::from_native(concat_idx);
    let concat_name = strings.intern(b"concat");
    gc.get_table_mut(table_table)
        .raw_set_str(concat_name, concat_val);

    let unpack_idx = gc.alloc_native(native_table_unpack_stub, "unpack");
    let unpack_val = TValue::from_native(unpack_idx);
    let unpack_name = strings.intern(b"unpack");
    gc.get_table_mut(table_table)
        .raw_set_str(unpack_name, unpack_val);

    register_fn(gc, table_table, strings, "pack", native_table_pack);

    // table.sort is special — needs VM access for custom comparator
    let sort_idx = gc.alloc_native(native_table_sort_stub, "sort");
    let sort_val = TValue::from_native(sort_idx);
    let sort_name = strings.intern(b"sort");
    gc.get_table_mut(table_table)
        .raw_set_str(sort_name, sort_val);

    // table.move is special — needs VM access for metamethods (__index/__newindex)
    let move_idx = gc.alloc_native(native_table_move_stub, "move");
    let move_val = TValue::from_native(move_idx);
    let move_name = strings.intern(b"move");
    gc.get_table_mut(table_table)
        .raw_set_str(move_name, move_val);

    let name = strings.intern(b"table");
    gc.get_table_mut(env_idx)
        .raw_set_str(name, TValue::from_table(table_table));

    TableLibIndices {
        sort_idx,
        move_idx,
        insert_idx,
        remove_idx,
        concat_idx,
        unpack_idx,
    }
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

#[allow(dead_code)]
fn get_table_arg(
    ctx: &NativeContext,
    idx: usize,
    fname: &str,
) -> Result<GcIdx<Table>, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    val.as_table_idx().ok_or_else(|| {
        NativeError::String(format!(
            "bad argument #{} to '{}' (table expected, got {})",
            idx + 1,
            fname,
            type_name(val)
        ))
    })
}

#[allow(dead_code)]
fn get_int_arg(ctx: &NativeContext, idx: usize, fname: &str) -> Result<i64, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    val.as_full_integer(ctx.gc).ok_or_else(|| {
        NativeError::String(format!(
            "bad argument #{} to '{}' (number expected, got {})",
            idx + 1,
            fname,
            type_name(val)
        ))
    })
}

#[allow(dead_code)]
fn type_name(val: TValue) -> &'static str {
    if val.is_nil() {
        "nil"
    } else if val.is_bool() {
        "boolean"
    } else if val.is_integer() || val.is_float() {
        "number"
    } else if val.is_string() {
        "string"
    } else if val.is_table() {
        "table"
    } else if val.is_function() {
        "function"
    } else {
        "userdata"
    }
}

/// Get table length, respecting __len metamethod. Returns error if __len returns non-integer.
#[allow(dead_code)]
fn get_table_len(ctx: &mut NativeContext, table_idx: GcIdx<Table>) -> Result<i64, NativeError> {
    let mt = ctx.gc.get_table(table_idx).metatable;
    if let Some(mt_idx) = mt {
        let len_key = ctx.strings.intern(b"__len");
        let mm = ctx.gc.get_table(mt_idx).raw_get_str(len_key);
        if !mm.is_nil() {
            // Call the __len metamethod
            if let Some(native_idx) = mm.as_native_idx() {
                let native_fn = ctx.gc.get_native(native_idx).func;
                let table_val = TValue::from_table(table_idx);
                let args = [table_val];
                let mut sub_ctx = NativeContext {
                    args: &args,
                    gc: ctx.gc,
                    strings: ctx.strings,
                    upvalue: TValue::nil(),
                };
                let results =
                    native_fn(&mut sub_ctx).map_err(|e| NativeError::String(format!("{:?}", e)))?;
                let result = results.first().copied().unwrap_or(TValue::nil());
                // Must be an integer
                if let Some(i) = result.as_full_integer(ctx.gc) {
                    return Ok(i);
                }
                return Err(NativeError::String(
                    "object length is not an integer".to_string(),
                ));
            }
            if mm.as_closure_idx().is_some() {
                // Lua closure __len: we can't call it from native context.
                // Return error since the result might not be integer.
                return Err(NativeError::String(
                    "object length is not an integer".to_string(),
                ));
            }
        }
    }
    Ok(ctx.gc.get_table(table_idx).length())
}

/// table.insert(t [,pos], val)
#[allow(dead_code)]
fn native_table_insert(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_idx = get_table_arg(ctx, 0, "insert")?;
    let len = get_table_len(ctx, table_idx)?;

    if ctx.args.len() == 2 {
        // table.insert(t, val) — append at end (wrapping for overflow)
        let val = ctx.args[1];
        ctx.gc
            .get_table_mut(table_idx)
            .raw_seti(len.wrapping_add(1), val);
    } else if ctx.args.len() == 3 {
        // table.insert(t, pos, val) — insert at pos, shift right
        let pos = get_int_arg(ctx, 1, "insert")?;
        let val = ctx.args[2];

        // Validate position using unsigned arithmetic (matches PUC Lua)
        // (pos - 1) as u64 < e as u64  (note: strict less-than)
        // where e = #t + 1
        let e = len.wrapping_add(1);
        if (pos.wrapping_sub(1) as u64) >= (e as u64) {
            return Err(NativeError::String(
                "bad argument #2 to 'insert' (position out of bounds)".to_string(),
            ));
        }

        // Shift elements right from len down to pos
        let mut i = len;
        while i >= pos {
            let v = ctx.gc.get_table(table_idx).raw_geti(i);
            ctx.gc.get_table_mut(table_idx).raw_seti(i + 1, v);
            i -= 1;
        }
        ctx.gc.get_table_mut(table_idx).raw_seti(pos, val);
    } else {
        return Err(NativeError::String(
            "wrong number of arguments to 'insert'".to_string(),
        ));
    }

    Ok(vec![])
}

/// table.remove(t [,pos])
#[allow(dead_code)]
fn native_table_remove(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_idx = get_table_arg(ctx, 0, "remove")?;
    let len = get_table_len(ctx, table_idx)?;

    let pos = if ctx.args.len() > 1 {
        get_int_arg(ctx, 1, "remove")?
    } else {
        len
    };

    // Validate position when pos != size (matches PUC Lua)
    if pos != len && (pos.wrapping_sub(1) as u64) > (len as u64) {
        return Err(NativeError::String(
            "bad argument #1 to 'remove' (position out of bounds)".to_string(),
        ));
    }

    let removed = ctx.gc.get_table(table_idx).raw_geti(pos);

    // Shift elements left: for (; pos < size; pos++) { t[pos] = t[pos+1]; }
    let mut i = pos;
    while i < len {
        let v = ctx.gc.get_table(table_idx).raw_geti(i + 1);
        ctx.gc.get_table_mut(table_idx).raw_seti(i, v);
        i += 1;
    }
    // t[pos] = nil (pos is now the last position after shifting)
    ctx.gc.get_table_mut(table_idx).raw_seti(i, TValue::nil());

    Ok(vec![removed])
}

/// table.concat(t [,sep [,i [,j]]])
#[allow(dead_code)]
fn native_table_concat(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_idx = get_table_arg(ctx, 0, "concat")?;

    let sep = if ctx.args.len() > 1 {
        let val = ctx.args[1];
        if let Some(sid) = val.as_string_id() {
            String::from_utf8_lossy(ctx.strings.get_bytes(sid)).into_owned()
        } else if val.is_nil() {
            String::new()
        } else {
            return Err(NativeError::String(
                "bad argument #2 to 'concat' (string expected)".to_string(),
            ));
        }
    } else {
        String::new()
    };

    let i = if ctx.args.len() > 2 {
        get_int_arg(ctx, 2, "concat")?
    } else {
        1
    };

    let j = if ctx.args.len() > 3 {
        get_int_arg(ctx, 3, "concat")?
    } else {
        ctx.gc.get_table(table_idx).length()
    };

    let mut parts = Vec::new();
    let mut k = i;
    while k <= j {
        let val = ctx.gc.get_table(table_idx).raw_geti(k);
        if let Some(sid) = val.as_string_id() {
            parts.push(String::from_utf8_lossy(ctx.strings.get_bytes(sid)).into_owned());
        } else if let Some(int) = val.as_full_integer(ctx.gc) {
            parts.push(format!("{}", int));
        } else if let Some(f) = val.as_float() {
            parts.push(format_float(f));
        } else {
            return Err(NativeError::String(format!(
                "invalid value ({}): no __tostring metamethod at index {} in table for 'concat'",
                type_name(val),
                k
            )));
        }
        // Use checked_add to prevent overflow when k == i64::MAX
        k = match k.checked_add(1) {
            Some(next) => next,
            None => break,
        };
    }

    let result = parts.join(&sep);
    let sid = ctx.strings.intern_or_create(result.as_bytes());
    Ok(vec![TValue::from_string_id(sid)])
}

#[allow(dead_code)]
fn format_float(f: f64) -> String {
    if f.fract() == 0.0 && f.abs() < 1e15 && !f.is_infinite() && !f.is_nan() {
        // Lua prints 1.0 as "1.0", not "1"
        format!("{:.1}", f)
    } else {
        format!("{}", f)
    }
}

/// table.move(a1, f, e, t [,a2])
#[allow(dead_code)]
fn native_table_move(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let a1_idx = get_table_arg(ctx, 0, "move")?;
    let f = get_int_arg(ctx, 1, "move")?;
    let e = get_int_arg(ctx, 2, "move")?;
    let t = get_int_arg(ctx, 3, "move")?;

    let a2_idx = if ctx.args.len() > 4 {
        get_table_arg(ctx, 4, "move")?
    } else {
        a1_idx
    };

    if f > e {
        return Ok(vec![TValue::from_table(a2_idx)]);
    }

    // Check for too many elements (e - f would overflow or is too large)
    let n = (e as i128) - (f as i128); // number of elements minus 1
    if n > i64::MAX as i128 {
        return Err(NativeError::String("too many elements to move".to_string()));
    }

    // Check destination wrap around: t + n must not overflow i64
    let last_dest = (t as i128) + n;
    if last_dest > i64::MAX as i128 || last_dest < i64::MIN as i128 {
        return Err(NativeError::String("destination wrap around".to_string()));
    }

    // Copy elements (with overflow-safe iteration)
    if t <= f || a1_idx != a2_idx {
        // Forward copy
        let mut i = f;
        loop {
            let v = ctx.gc.get_table(a1_idx).raw_geti(i);
            ctx.gc.get_table_mut(a2_idx).raw_seti(t + (i - f), v);
            if i == e {
                break;
            }
            i += 1;
        }
    } else {
        // Backward copy (overlapping, destination after source)
        let mut i = e;
        loop {
            let v = ctx.gc.get_table(a1_idx).raw_geti(i);
            ctx.gc.get_table_mut(a2_idx).raw_seti(t + (i - f), v);
            if i == f {
                break;
            }
            i -= 1;
        }
    }

    Ok(vec![TValue::from_table(a2_idx)])
}

/// table.pack(...)
fn native_table_pack(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_idx = ctx.gc.alloc_table(ctx.args.len(), 1);
    for (i, &v) in ctx.args.iter().enumerate() {
        ctx.gc.get_table_mut(table_idx).raw_seti((i + 1) as i64, v);
    }
    // Set 'n' field
    let n_name = ctx.strings.intern(b"n");
    let n_val = TValue::from_full_integer(ctx.args.len() as i64, ctx.gc);
    ctx.gc.get_table_mut(table_idx).raw_set_str(n_name, n_val);
    Ok(vec![TValue::from_table(table_idx)])
}

/// table.unpack(t [,i [,j]])
#[allow(dead_code)]
fn native_table_unpack(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_idx = get_table_arg(ctx, 0, "unpack")?;
    let arg1 = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let arg2 = ctx.args.get(2).copied().unwrap_or(TValue::nil());
    let i = if !arg1.is_nil() {
        get_int_arg(ctx, 1, "unpack")?
    } else {
        1
    };
    let j = if !arg2.is_nil() {
        get_int_arg(ctx, 2, "unpack")?
    } else {
        ctx.gc.get_table(table_idx).length()
    };

    // Check for too many results (mirrors PUC Lua's lua_checkstack limit)
    if j >= i {
        let n = (j as i128) - (i as i128) + 1;
        if n > 1_000_000 {
            return Err(NativeError::String(
                "too many results to unpack".to_string(),
            ));
        }
    }

    let mut results = Vec::new();
    let mut k = i;
    while k <= j {
        results.push(ctx.gc.get_table(table_idx).raw_geti(k));
        if k == j {
            break;
        } // avoid overflow when j == i64::MAX
        k += 1;
    }
    Ok(results)
}

/// Stub for table.sort — actual dispatch happens in call_function
fn native_table_sort_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "table.sort stub should not be called directly".to_string(),
    ))
}

fn native_table_insert_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "table.insert stub should not be called directly".to_string(),
    ))
}

fn native_table_remove_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "table.remove stub should not be called directly".to_string(),
    ))
}

/// Stub for table.move — actual dispatch happens in call_function
fn native_table_move_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "table.move stub should not be called directly".to_string(),
    ))
}

/// Stub for table.concat — actual dispatch happens in call_function
fn native_table_concat_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "table.concat stub should not be called directly".to_string(),
    ))
}

/// Stub for table.unpack — actual dispatch happens in call_function
fn native_table_unpack_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "table.unpack stub should not be called directly".to_string(),
    ))
}
