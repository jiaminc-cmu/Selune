//! Lua 5.4 table library.

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError, NativeFunction};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;

/// Register the table library into _ENV.
/// Returns the GcIdx of the table.sort native function (for special dispatch in VM).
pub fn register(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) -> GcIdx<NativeFunction> {
    let table_table = gc.alloc_table(0, 16);

    register_fn(gc, table_table, strings, "insert", native_table_insert);
    register_fn(gc, table_table, strings, "remove", native_table_remove);
    register_fn(gc, table_table, strings, "concat", native_table_concat);
    register_fn(gc, table_table, strings, "move", native_table_move);
    register_fn(gc, table_table, strings, "pack", native_table_pack);
    register_fn(gc, table_table, strings, "unpack", native_table_unpack);

    // table.sort is special — needs VM access for custom comparator
    let sort_idx = gc.alloc_native(native_table_sort_stub, "sort");
    let sort_val = TValue::from_native(sort_idx);
    let sort_name = strings.intern(b"sort");
    gc.get_table_mut(table_table).raw_set_str(sort_name, sort_val);

    let name = strings.intern(b"table");
    gc.get_table_mut(env_idx)
        .raw_set_str(name, TValue::from_table(table_table));

    sort_idx
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

fn get_table_arg(ctx: &NativeContext, idx: usize, fname: &str) -> Result<GcIdx<Table>, NativeError> {
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

/// table.insert(t [,pos], val)
fn native_table_insert(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_idx = get_table_arg(ctx, 0, "insert")?;
    let len = ctx.gc.get_table(table_idx).length();

    if ctx.args.len() == 2 {
        // table.insert(t, val) — append at end
        let val = ctx.args[1];
        ctx.gc.get_table_mut(table_idx).raw_seti(len + 1, val);
    } else if ctx.args.len() >= 3 {
        // table.insert(t, pos, val) — insert at pos, shift right
        let pos = get_int_arg(ctx, 1, "insert")?;
        let val = ctx.args[2];

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
fn native_table_remove(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_idx = get_table_arg(ctx, 0, "remove")?;
    let len = ctx.gc.get_table(table_idx).length();

    let pos = if ctx.args.len() > 1 {
        get_int_arg(ctx, 1, "remove")?
    } else {
        len
    };

    let removed = ctx.gc.get_table(table_idx).raw_geti(pos);

    // Shift elements left
    let mut i = pos;
    while i < len {
        let v = ctx.gc.get_table(table_idx).raw_geti(i + 1);
        ctx.gc.get_table_mut(table_idx).raw_seti(i, v);
        i += 1;
    }
    // Remove last element
    ctx.gc.get_table_mut(table_idx).raw_seti(len, TValue::nil());

    Ok(vec![removed])
}

/// table.concat(t [,sep [,i [,j]]])
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
        k += 1;
    }

    let result = parts.join(&sep);
    let sid = ctx.strings.intern_or_create(result.as_bytes());
    Ok(vec![TValue::from_string_id(sid)])
}

fn format_float(f: f64) -> String {
    if f.fract() == 0.0 && f.abs() < 1e15 && !f.is_infinite() && !f.is_nan() {
        // Lua prints 1.0 as "1.0", not "1"
        format!("{:.1}", f)
    } else {
        format!("{}", f)
    }
}

/// table.move(a1, f, e, t [,a2])
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

    // Copy elements
    if t <= f || a1_idx != a2_idx {
        // Forward copy
        let mut i = f;
        while i <= e {
            let v = ctx.gc.get_table(a1_idx).raw_geti(i);
            ctx.gc.get_table_mut(a2_idx).raw_seti(t + (i - f), v);
            i += 1;
        }
    } else {
        // Backward copy (overlapping, destination after source)
        let mut i = e;
        while i >= f {
            let v = ctx.gc.get_table(a1_idx).raw_geti(i);
            ctx.gc.get_table_mut(a2_idx).raw_seti(t + (i - f), v);
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
fn native_table_unpack(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_idx = get_table_arg(ctx, 0, "unpack")?;
    let i = if ctx.args.len() > 1 {
        get_int_arg(ctx, 1, "unpack")?
    } else {
        1
    };
    let j = if ctx.args.len() > 2 {
        get_int_arg(ctx, 2, "unpack")?
    } else {
        ctx.gc.get_table(table_idx).length()
    };

    let mut results = Vec::new();
    let mut k = i;
    while k <= j {
        results.push(ctx.gc.get_table(table_idx).raw_geti(k));
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
