//! Lua 5.4 debug library.
//!
//! Functions that only need GcHeap/NativeContext access are fully implemented.
//! Functions that need full VM access (call stack, hooks, locals) are stubbed
//! and will be wired up through dispatch.rs later.

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError, NativeFunction, UpValLocation};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;

/// Register the debug library into _ENV.
/// Return value from debug lib registration with indices of special natives.
pub struct DebugIndices {
    pub getupvalue_idx: GcIdx<NativeFunction>,
    pub setupvalue_idx: GcIdx<NativeFunction>,
    pub getinfo_idx: GcIdx<NativeFunction>,
    pub traceback_idx: GcIdx<NativeFunction>,
    pub sethook_idx: GcIdx<NativeFunction>,
    pub gethook_idx: GcIdx<NativeFunction>,
    pub getlocal_idx: GcIdx<NativeFunction>,
    pub setlocal_idx: GcIdx<NativeFunction>,
    pub getregistry_idx: GcIdx<NativeFunction>,
}

pub fn register(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) -> DebugIndices {
    let debug_table = gc.alloc_table(0, 16);

    // Functions implementable with NativeContext
    register_fn(
        gc,
        debug_table,
        strings,
        "getmetatable",
        native_debug_getmetatable,
    );
    register_fn(
        gc,
        debug_table,
        strings,
        "setmetatable",
        native_debug_setmetatable,
    );
    register_fn(
        gc,
        debug_table,
        strings,
        "upvalueid",
        native_debug_upvalueid,
    );
    register_fn(
        gc,
        debug_table,
        strings,
        "upvaluejoin",
        native_debug_upvaluejoin,
    );
    register_fn(
        gc,
        debug_table,
        strings,
        "getuservalue",
        native_debug_getuservalue,
    );
    register_fn(
        gc,
        debug_table,
        strings,
        "setuservalue",
        native_debug_setuservalue,
    );

    // getupvalue/setupvalue need full VM access (redirected through dispatch.rs)
    let getupvalue_idx = gc.alloc_native(native_debug_getupvalue, "getupvalue");
    gc.get_table_mut(debug_table).raw_set_str(
        strings.intern(b"getupvalue"),
        TValue::from_native(getupvalue_idx),
    );
    let setupvalue_idx = gc.alloc_native(native_debug_setupvalue, "setupvalue");
    gc.get_table_mut(debug_table).raw_set_str(
        strings.intern(b"setupvalue"),
        TValue::from_native(setupvalue_idx),
    );

    // getinfo needs full VM access (redirected through dispatch.rs)
    let getinfo_idx = gc.alloc_native(native_debug_getinfo, "getinfo");
    gc.get_table_mut(debug_table)
        .raw_set_str(strings.intern(b"getinfo"), TValue::from_native(getinfo_idx));

    // traceback needs full VM access (redirected through dispatch.rs)
    let traceback_idx = gc.alloc_native(native_debug_traceback, "traceback");
    gc.get_table_mut(debug_table).raw_set_str(
        strings.intern(b"traceback"),
        TValue::from_native(traceback_idx),
    );

    // Functions that need full VM access (redirected through dispatch.rs)
    let sethook_idx = gc.alloc_native(native_debug_sethook, "sethook");
    gc.get_table_mut(debug_table)
        .raw_set_str(strings.intern(b"sethook"), TValue::from_native(sethook_idx));
    let gethook_idx = gc.alloc_native(native_debug_gethook, "gethook");
    gc.get_table_mut(debug_table)
        .raw_set_str(strings.intern(b"gethook"), TValue::from_native(gethook_idx));
    let getlocal_idx = gc.alloc_native(native_debug_getlocal, "getlocal");
    gc.get_table_mut(debug_table).raw_set_str(
        strings.intern(b"getlocal"),
        TValue::from_native(getlocal_idx),
    );
    let setlocal_idx = gc.alloc_native(native_debug_setlocal, "setlocal");
    gc.get_table_mut(debug_table).raw_set_str(
        strings.intern(b"setlocal"),
        TValue::from_native(setlocal_idx),
    );
    let getregistry_idx = gc.alloc_native(native_debug_getregistry, "getregistry");
    gc.get_table_mut(debug_table).raw_set_str(
        strings.intern(b"getregistry"),
        TValue::from_native(getregistry_idx),
    );

    let debug_name = strings.intern(b"debug");
    gc.get_table_mut(env_idx)
        .raw_set_str(debug_name, TValue::from_table(debug_table));

    DebugIndices {
        getupvalue_idx,
        setupvalue_idx,
        getinfo_idx,
        traceback_idx,
        sethook_idx,
        gethook_idx,
        getlocal_idx,
        setlocal_idx,
        getregistry_idx,
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

// ---------------------------------------------------------------------------
// debug.getmetatable(value)
// Returns the metatable of any value, bypassing the __metatable metamethod.
// ---------------------------------------------------------------------------

fn native_debug_getmetatable(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());

    if let Some(tbl_idx) = val.as_table_idx() {
        let mt = ctx.gc.get_table(tbl_idx).metatable;
        match mt {
            Some(mt_idx) => Ok(vec![TValue::from_table(mt_idx)]),
            None => Ok(vec![TValue::nil()]),
        }
    } else if let Some(ud_idx) = val.as_userdata_idx() {
        let mt = ctx.gc.get_userdata(ud_idx).metatable;
        match mt {
            Some(mt_idx) => Ok(vec![TValue::from_table(mt_idx)]),
            None => Ok(vec![TValue::nil()]),
        }
    } else if val.is_string() {
        match ctx.gc.string_metatable {
            Some(mt_idx) => Ok(vec![TValue::from_table(mt_idx)]),
            None => Ok(vec![TValue::nil()]),
        }
    } else if val.is_number() || val.gc_sub_tag() == Some(selune_core::gc::GC_SUB_BOXED_INT) {
        match ctx.gc.number_metatable {
            Some(mt_idx) => Ok(vec![TValue::from_table(mt_idx)]),
            None => Ok(vec![TValue::nil()]),
        }
    } else if val.is_bool() {
        match ctx.gc.boolean_metatable {
            Some(mt_idx) => Ok(vec![TValue::from_table(mt_idx)]),
            None => Ok(vec![TValue::nil()]),
        }
    } else if val.is_nil() {
        match ctx.gc.nil_metatable {
            Some(mt_idx) => Ok(vec![TValue::from_table(mt_idx)]),
            None => Ok(vec![TValue::nil()]),
        }
    } else {
        Ok(vec![TValue::nil()])
    }
}

// ---------------------------------------------------------------------------
// debug.setmetatable(value, table)
// Sets the metatable of any value, bypassing the __metatable metamethod.
// Returns the value.
// ---------------------------------------------------------------------------

fn native_debug_setmetatable(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let mt_arg = ctx.args.get(1).copied().unwrap_or(TValue::nil());

    // The metatable must be nil or a table.
    let mt = if mt_arg.is_nil() {
        None
    } else if let Some(mt_idx) = mt_arg.as_table_idx() {
        Some(mt_idx)
    } else {
        return Err(NativeError::String(
            "bad argument #2 to 'setmetatable' (nil or table expected)".into(),
        ));
    };

    if let Some(tbl_idx) = val.as_table_idx() {
        ctx.gc.get_table_mut(tbl_idx).metatable = mt;
        Ok(vec![val])
    } else if let Some(ud_idx) = val.as_userdata_idx() {
        ctx.gc.get_userdata_mut(ud_idx).metatable = mt;
        Ok(vec![val])
    } else if val.is_string() {
        ctx.gc.string_metatable = mt;
        Ok(vec![val])
    } else if val.is_number() || val.gc_sub_tag() == Some(selune_core::gc::GC_SUB_BOXED_INT) {
        ctx.gc.number_metatable = mt;
        Ok(vec![val])
    } else if val.is_bool() {
        ctx.gc.boolean_metatable = mt;
        Ok(vec![val])
    } else if val.is_nil() {
        ctx.gc.nil_metatable = mt;
        Ok(vec![val])
    } else {
        // For other types (functions, etc.), just return the value
        Ok(vec![val])
    }
}

// ---------------------------------------------------------------------------
// debug.getupvalue(f, up)
// Returns the name and value of the upvalue at index `up` of function `f`.
// Returns nil if index is out of range. For native functions, always returns nil.
// ---------------------------------------------------------------------------

fn native_debug_getupvalue(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let func = ctx.args.first().copied().unwrap_or(TValue::nil());
    let n_arg = ctx.args.get(1).copied().unwrap_or(TValue::nil());

    // Validate that first arg is a function
    if !func.is_function() {
        return Err(NativeError::String(
            "bad argument #1 to 'getupvalue' (function expected)".into(),
        ));
    }

    // Get the upvalue index (1-based)
    let n = if let Some(i) = n_arg.as_full_integer(ctx.gc) {
        i
    } else if let Some(f) = n_arg.as_float() {
        f as i64
    } else {
        return Err(NativeError::String(
            "bad argument #2 to 'getupvalue' (number expected)".into(),
        ));
    };

    if let Some(cl_idx) = func.as_closure_idx() {
        let closure = ctx.gc.get_closure(cl_idx);
        let idx = (n - 1) as usize;
        if n < 1 || idx >= closure.upvalues.len() {
            return Ok(vec![TValue::nil()]);
        }
        let uv_idx = closure.upvalues[idx];
        let uv = ctx.gc.get_upval(uv_idx);
        let val = match uv.location {
            UpValLocation::Closed(v) => v,
            // Open upvalues reference stack slots; we can't read them
            // from NativeContext. Return nil for now (will be fixed when
            // wired through dispatch.rs with full VM access).
            UpValLocation::Open(_) | UpValLocation::OpenInThread(_, _) => TValue::nil(),
        };
        // We don't have access to Proto for upvalue names from NativeContext,
        // so return a generated name.
        let name = format!("(upvalue {})", n);
        let name_sid = ctx.strings.intern_or_create(name.as_bytes());
        Ok(vec![TValue::from_string_id(name_sid), val])
    } else {
        // Native functions don't have upvalues in Lua semantics
        Ok(vec![TValue::nil()])
    }
}

// ---------------------------------------------------------------------------
// debug.setupvalue(f, up, value)
// Sets the value of the upvalue at index `up` of function `f`.
// Returns the upvalue name, or nil if the index is out of range.
// ---------------------------------------------------------------------------

fn native_debug_setupvalue(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let func = ctx.args.first().copied().unwrap_or(TValue::nil());
    let n_arg = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let new_val = ctx.args.get(2).copied().unwrap_or(TValue::nil());

    // Validate that first arg is a function
    if !func.is_function() {
        return Err(NativeError::String(
            "bad argument #1 to 'setupvalue' (function expected)".into(),
        ));
    }

    // Get the upvalue index (1-based)
    let n = if let Some(i) = n_arg.as_full_integer(ctx.gc) {
        i
    } else if let Some(f) = n_arg.as_float() {
        f as i64
    } else {
        return Err(NativeError::String(
            "bad argument #2 to 'setupvalue' (number expected)".into(),
        ));
    };

    if let Some(cl_idx) = func.as_closure_idx() {
        let closure = ctx.gc.get_closure(cl_idx);
        let idx = (n - 1) as usize;
        if n < 1 || idx >= closure.upvalues.len() {
            return Ok(vec![TValue::nil()]);
        }
        let uv_idx = closure.upvalues[idx];
        let uv = ctx.gc.get_upval_mut(uv_idx);
        match &mut uv.location {
            UpValLocation::Closed(ref mut v) => {
                *v = new_val;
            }
            // Open upvalues reference stack slots; we can't set them
            // from NativeContext. This will be fixed when wired through
            // dispatch.rs with full VM access.
            UpValLocation::Open(_) | UpValLocation::OpenInThread(_, _) => {
                // Cannot set open upvalues without VM stack access.
                // Return nil to indicate failure.
                return Ok(vec![TValue::nil()]);
            }
        }
        let name = format!("(upvalue {})", n);
        let name_sid = ctx.strings.intern_or_create(name.as_bytes());
        Ok(vec![TValue::from_string_id(name_sid)])
    } else {
        // Native functions don't have upvalues
        Ok(vec![TValue::nil()])
    }
}

// ---------------------------------------------------------------------------
// debug.upvalueid(f, n)
// Returns a unique identifier (as a light userdata / integer) for the
// upvalue at index `n` of function `f`.
// ---------------------------------------------------------------------------

fn native_debug_upvalueid(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let func = ctx.args.first().copied().unwrap_or(TValue::nil());
    let n_arg = ctx.args.get(1).copied().unwrap_or(TValue::nil());

    if !func.is_function() {
        return Err(NativeError::String(
            "bad argument #1 to 'upvalueid' (function expected)".into(),
        ));
    }

    let n = if let Some(i) = n_arg.as_full_integer(ctx.gc) {
        i
    } else if let Some(f) = n_arg.as_float() {
        f as i64
    } else {
        return Err(NativeError::String(
            "bad argument #2 to 'upvalueid' (number expected)".into(),
        ));
    };

    if let Some(cl_idx) = func.as_closure_idx() {
        let closure = ctx.gc.get_closure(cl_idx);
        let idx = (n - 1) as usize;
        if n < 1 || idx >= closure.upvalues.len() {
            // Lua 5.4: return nil for out-of-range upvalue indices
            return Ok(vec![TValue::nil()]);
        }
        let uv_idx = closure.upvalues[idx];
        // Return the raw GcIdx as an integer identifier.
        // Two closures sharing the same upvalue will return the same id.
        Ok(vec![TValue::from_light_userdata(uv_idx.0 as usize)])
    } else {
        // For C/native functions, return nil for any upvalue index
        Ok(vec![TValue::nil()])
    }
}

// ---------------------------------------------------------------------------
// debug.upvaluejoin(f1, n1, f2, n2)
// Make the n1-th upvalue of closure f1 refer to the n2-th upvalue of
// closure f2.
// ---------------------------------------------------------------------------

fn native_debug_upvaluejoin(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f1 = ctx.args.first().copied().unwrap_or(TValue::nil());
    let n1_arg = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let f2 = ctx.args.get(2).copied().unwrap_or(TValue::nil());
    let n2_arg = ctx.args.get(3).copied().unwrap_or(TValue::nil());

    let cl1_idx = f1.as_closure_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'upvaluejoin' (Lua function expected)".into())
    })?;
    let cl2_idx = f2.as_closure_idx().ok_or_else(|| {
        NativeError::String("bad argument #3 to 'upvaluejoin' (Lua function expected)".into())
    })?;

    let n1 = if let Some(i) = n1_arg.as_full_integer(ctx.gc) {
        i
    } else if let Some(f) = n1_arg.as_float() {
        f as i64
    } else {
        return Err(NativeError::String(
            "bad argument #2 to 'upvaluejoin' (number expected)".into(),
        ));
    };
    let n2 = if let Some(i) = n2_arg.as_full_integer(ctx.gc) {
        i
    } else if let Some(f) = n2_arg.as_float() {
        f as i64
    } else {
        return Err(NativeError::String(
            "bad argument #4 to 'upvaluejoin' (number expected)".into(),
        ));
    };

    let idx1 = (n1 - 1) as usize;
    let idx2 = (n2 - 1) as usize;

    // Read the upvalue GcIdx from f2 first.
    let closure2 = ctx.gc.get_closure(cl2_idx);
    if n2 < 1 || idx2 >= closure2.upvalues.len() {
        return Err(NativeError::String(format!(
            "bad argument #4 to 'upvaluejoin' (invalid upvalue index {})",
            n2
        )));
    }
    let uv2 = closure2.upvalues[idx2];

    // Now set f1's upvalue to point to f2's upvalue.
    // We need mutable access to the closure arena directly since
    // there is no get_closure_mut on GcHeap.
    let closure1 = ctx.gc.closures[cl1_idx.0 as usize]
        .as_mut()
        .expect("closure was freed");
    if n1 < 1 || idx1 >= closure1.upvalues.len() {
        return Err(NativeError::String(format!(
            "bad argument #2 to 'upvaluejoin' (invalid upvalue index {})",
            n1
        )));
    }
    closure1.upvalues[idx1] = uv2;

    Ok(vec![])
}

// ---------------------------------------------------------------------------
// debug.getuservalue(u, n)
// Returns the n-th user value of userdata u (default n=1), plus a boolean
// indicating whether the userdata has that value.
// ---------------------------------------------------------------------------

fn native_debug_getuservalue(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let n_arg = ctx.args.get(1).copied().unwrap_or(TValue::nil());

    let ud_idx = match val.as_userdata_idx() {
        Some(idx) => idx,
        None => {
            return Err(NativeError::String(
                "bad argument #1 to 'getuservalue' (userdata expected)".into(),
            ));
        }
    };

    // Default n = 1
    let n = if n_arg.is_nil() {
        1i64
    } else if let Some(i) = n_arg.as_full_integer(ctx.gc) {
        i
    } else if let Some(f) = n_arg.as_float() {
        f as i64
    } else {
        return Err(NativeError::String(
            "bad argument #2 to 'getuservalue' (number expected)".into(),
        ));
    };

    let ud = ctx.gc.get_userdata(ud_idx);
    let idx = (n - 1) as usize;
    if n >= 1 && idx < ud.user_values.len() {
        let uv = ud.user_values[idx];
        // Return the value and true (indicating it exists)
        Ok(vec![uv, TValue::from_bool(true)])
    } else {
        // Out of range: return nil, false
        Ok(vec![TValue::nil(), TValue::from_bool(false)])
    }
}

// ---------------------------------------------------------------------------
// debug.setuservalue(u, value, n)
// Sets the n-th user value of userdata u to value (default n=1).
// Returns u.
// ---------------------------------------------------------------------------

fn native_debug_setuservalue(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let new_val = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let n_arg = ctx.args.get(2).copied().unwrap_or(TValue::nil());

    let ud_idx = match val.as_userdata_idx() {
        Some(idx) => idx,
        None => {
            if val.is_light_userdata() {
                return Err(NativeError::String(
                    "bad argument #1 to 'setuservalue' (full userdata expected, got light userdata)".into(),
                ));
            }
            return Err(NativeError::String(
                "bad argument #1 to 'setuservalue' (userdata expected)".into(),
            ));
        }
    };

    // Default n = 1
    let n = if n_arg.is_nil() {
        1i64
    } else if let Some(i) = n_arg.as_full_integer(ctx.gc) {
        i
    } else if let Some(f) = n_arg.as_float() {
        f as i64
    } else {
        return Err(NativeError::String(
            "bad argument #3 to 'setuservalue' (number expected)".into(),
        ));
    };

    let idx = (n - 1) as usize;
    let ud = ctx.gc.get_userdata_mut(ud_idx);

    if n < 1 {
        return Err(NativeError::String(format!(
            "bad argument #3 to 'setuservalue' (invalid user value index {})",
            n
        )));
    }

    // If index is out of range, return false (fail)
    if idx >= ud.user_values.len() {
        return Ok(vec![TValue::from_bool(false)]);
    }
    ud.user_values[idx] = new_val;

    Ok(vec![val])
}

// ===========================================================================
// Stubs: functions requiring full VM access (call stack, hooks, locals)
// These will be wired up through dispatch.rs later.
// ===========================================================================

// ---------------------------------------------------------------------------
// debug.getinfo(f [, what])
// Stub: returns a table with minimal info. Will be fully implemented later.
// ---------------------------------------------------------------------------

fn native_debug_getinfo(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let _f = ctx.args.first().copied().unwrap_or(TValue::nil());

    // Build a minimal info table
    let tbl = ctx.gc.alloc_table(0, 8);

    let source_key = ctx.strings.intern(b"source");
    let source_val = ctx.strings.intern_or_create(b"=?");
    ctx.gc
        .get_table_mut(tbl)
        .raw_set_str(source_key, TValue::from_string_id(source_val));

    let what_key = ctx.strings.intern(b"what");
    let what_val = ctx.strings.intern_or_create(b"Lua");
    ctx.gc
        .get_table_mut(tbl)
        .raw_set_str(what_key, TValue::from_string_id(what_val));

    let short_src_key = ctx.strings.intern(b"short_src");
    let short_src_val = ctx.strings.intern_or_create(b"?");
    ctx.gc
        .get_table_mut(tbl)
        .raw_set_str(short_src_key, TValue::from_string_id(short_src_val));

    let currentline_key = ctx.strings.intern(b"currentline");
    ctx.gc
        .get_table_mut(tbl)
        .raw_set_str(currentline_key, TValue::from_integer(-1));

    let linedefined_key = ctx.strings.intern(b"linedefined");
    ctx.gc
        .get_table_mut(tbl)
        .raw_set_str(linedefined_key, TValue::from_integer(-1));

    let lastlinedefined_key = ctx.strings.intern(b"lastlinedefined");
    ctx.gc
        .get_table_mut(tbl)
        .raw_set_str(lastlinedefined_key, TValue::from_integer(-1));

    Ok(vec![TValue::from_table(tbl)])
}

// ---------------------------------------------------------------------------
// debug.traceback([message [, level]])
// Stub: returns the message argument as-is (or ""). Will produce real
// stack traces when wired up through dispatch.rs.
// ---------------------------------------------------------------------------

fn native_debug_traceback(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let msg = ctx.args.first().copied().unwrap_or(TValue::nil());

    if msg.is_nil() {
        // Return empty traceback string
        let sid = ctx.strings.intern(b"");
        Ok(vec![TValue::from_string_id(sid)])
    } else if msg.is_string() {
        // Return the message as-is (no actual traceback yet)
        Ok(vec![msg])
    } else {
        // If the message is not a string, return it directly
        // (Lua 5.4 returns the non-string message without modification)
        Ok(vec![msg])
    }
}

// ---------------------------------------------------------------------------
// debug.sethook([thread,] hook, mask [, count])
// Stub: no-op. Hook support will be implemented later.
// ---------------------------------------------------------------------------

fn native_debug_sethook(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    // No-op stub. Returns nothing.
    Ok(vec![])
}

// ---------------------------------------------------------------------------
// debug.getlocal([thread,] level, local)
// Stub: returns nil. Will be wired up when we have VM stack access.
// ---------------------------------------------------------------------------

fn native_debug_getlocal(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Ok(vec![TValue::nil()])
}

// ---------------------------------------------------------------------------
// debug.setlocal([thread,] level, local, value)
// Stub: returns nil. Will be wired up when we have VM stack access.
// ---------------------------------------------------------------------------

fn native_debug_setlocal(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Ok(vec![TValue::nil()])
}

// ---------------------------------------------------------------------------
// debug.gethook([thread])
// Stub: redirected through dispatch.rs for VM access.
// ---------------------------------------------------------------------------

fn native_debug_gethook(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Ok(vec![])
}

// ---------------------------------------------------------------------------
// debug.getregistry()
// Stub: redirected through dispatch.rs for VM access.
// ---------------------------------------------------------------------------

fn native_debug_getregistry(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Ok(vec![TValue::nil()])
}
