//! Lua 5.4 coroutine library.
//!
//! Coroutine handles are tables with:
//! - [1] = coro_id (integer index into Vm::coroutines, -1 if not yet allocated)
//! - [2] = function (the coroutine body)
//! - [3] = status string id ("suspended", "running", "normal", "dead")

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError, NativeFunction};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;

/// Native indices that need special VM dispatch.
pub struct CoroutineIndices {
    pub resume_idx: GcIdx<NativeFunction>,
    pub yield_idx: GcIdx<NativeFunction>,
    pub wrap_idx: GcIdx<NativeFunction>,
    pub wrap_resume_idx: GcIdx<NativeFunction>,
}

pub fn register(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) -> CoroutineIndices {
    let co_table = gc.alloc_table(0, 10);

    register_fn(gc, co_table, strings, "create", native_coroutine_create);
    register_fn(gc, co_table, strings, "status", native_coroutine_status);
    register_fn(gc, co_table, strings, "isyieldable", native_coroutine_isyieldable);
    register_fn(gc, co_table, strings, "close", native_coroutine_close);

    // Stubs for VM-dispatched functions
    let resume_idx = gc.alloc_native(native_stub, "coroutine.resume");
    let resume_val = TValue::from_native(resume_idx);
    let resume_name = strings.intern(b"resume");
    gc.get_table_mut(co_table).raw_set_str(resume_name, resume_val);

    let yield_idx = gc.alloc_native(native_stub, "coroutine.yield");
    let yield_val = TValue::from_native(yield_idx);
    let yield_name = strings.intern(b"yield");
    gc.get_table_mut(co_table).raw_set_str(yield_name, yield_val);

    // coroutine.wrap is also VM-dispatched (needs wrap_resume_idx to set __call)
    let wrap_stub = gc.alloc_native(native_stub, "coroutine.wrap");
    let wrap_val = TValue::from_native(wrap_stub);
    let wrap_name = strings.intern(b"wrap");
    gc.get_table_mut(co_table).raw_set_str(wrap_name, wrap_val);

    // Internal wrap resume function (not registered in coroutine table)
    let wrap_resume_idx = gc.alloc_native(native_stub, "coroutine.wrap_resume");

    // Register coroutine table into _ENV
    let name = strings.intern(b"coroutine");
    gc.get_table_mut(env_idx).raw_set_str(name, TValue::from_table(co_table));

    CoroutineIndices {
        resume_idx,
        yield_idx,
        wrap_idx: wrap_stub,
        wrap_resume_idx,
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
    let name_sid = strings.intern(name.as_bytes());
    gc.get_table_mut(table).raw_set_str(name_sid, val);
}

/// Extract the coroutine ID from a handle table. Returns None if not a coroutine.
pub fn get_coro_id(val: TValue, gc: &GcHeap) -> Option<i64> {
    let table_idx = val.as_table_idx()?;
    let id_val = gc.get_table(table_idx).raw_geti(1);
    id_val.as_integer()
}

/// Get the function stored in a coroutine handle.
pub fn get_coro_func(val: TValue, gc: &GcHeap) -> Option<TValue> {
    let table_idx = val.as_table_idx()?;
    let func = gc.get_table(table_idx).raw_geti(2);
    if func.is_function() { Some(func) } else { None }
}

// ---- Native implementations ----

/// coroutine.create(f) — create a coroutine handle.
fn native_coroutine_create(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let func = ctx.args.first().copied().unwrap_or(TValue::nil());
    if !func.is_function() {
        return Err(NativeError::String(
            "bad argument #1 to 'create' (function expected)".to_string(),
        ));
    }

    let handle = ctx.gc.alloc_table(4, 0);
    ctx.gc.get_table_mut(handle).raw_seti(1, TValue::from_integer(-1)); // coro_id = -1 (unallocated)
    ctx.gc.get_table_mut(handle).raw_seti(2, func);
    let suspended_sid = ctx.strings.intern(b"suspended");
    ctx.gc.get_table_mut(handle).raw_seti(3, TValue::from_string_id(suspended_sid));

    Ok(vec![TValue::from_table(handle)])
}

/// coroutine.status(co) — return status string.
fn native_coroutine_status(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let co_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let table_idx = co_val.as_table_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'status' (coroutine expected)".to_string())
    })?;

    let status_val = ctx.gc.get_table(table_idx).raw_geti(3);
    if status_val.as_string_id().is_some() {
        Ok(vec![status_val])
    } else {
        let sid = ctx.strings.intern(b"suspended");
        Ok(vec![TValue::from_string_id(sid)])
    }
}

/// coroutine.isyieldable() — returns false from main thread.
/// The VM dispatch overrides this when running in a coroutine.
fn native_coroutine_isyieldable(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let _ = ctx;
    Ok(vec![TValue::from_bool(false)])
}

/// coroutine.close(co) — close a suspended coroutine.
fn native_coroutine_close(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let co_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let table_idx = co_val.as_table_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'close' (coroutine expected)".to_string())
    })?;

    let status_val = ctx.gc.get_table(table_idx).raw_geti(3);
    if let Some(sid) = status_val.as_string_id() {
        let status = ctx.strings.get_bytes(sid);
        if status == b"dead" {
            return Ok(vec![TValue::from_bool(true)]);
        }
        if status != b"suspended" {
            return Err(NativeError::String(
                "cannot close a running or normal coroutine".to_string(),
            ));
        }
    }

    let dead_sid = ctx.strings.intern(b"dead");
    ctx.gc.get_table_mut(table_idx).raw_seti(3, TValue::from_string_id(dead_sid));

    Ok(vec![TValue::from_bool(true)])
}

/// Stub for VM-dispatched functions.
fn native_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "coroutine stub should not be called directly".to_string(),
    ))
}
