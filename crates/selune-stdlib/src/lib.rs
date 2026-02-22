//! Selune standard library: Lua 5.4 standard libraries.

pub mod coroutine_lib;
pub mod math;
pub mod pattern;
pub mod string_lib;
pub mod table_lib;

use selune_core::gc::{GcHeap, GcIdx, NativeFunction};
use selune_core::string::StringInterner;
use selune_core::table::Table;

/// Indices of native functions that need special VM dispatch.
pub struct StdlibIndices {
    pub table_sort_idx: GcIdx<NativeFunction>,
    pub string_gsub_idx: GcIdx<NativeFunction>,
    pub coro_resume_idx: GcIdx<NativeFunction>,
    pub coro_yield_idx: GcIdx<NativeFunction>,
    pub coro_wrap_idx: GcIdx<NativeFunction>,
    pub coro_wrap_resume_idx: GcIdx<NativeFunction>,
}

/// Register all standard library modules into _ENV.
pub fn register_all(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) -> StdlibIndices {
    math::register(env_idx, gc, strings);
    let table_sort_idx = table_lib::register(env_idx, gc, strings);
    let string_gsub_idx = string_lib::register(env_idx, gc, strings);
    let coro_indices = coroutine_lib::register(env_idx, gc, strings);
    StdlibIndices {
        table_sort_idx,
        string_gsub_idx,
        coro_resume_idx: coro_indices.resume_idx,
        coro_yield_idx: coro_indices.yield_idx,
        coro_wrap_idx: coro_indices.wrap_idx,
        coro_wrap_resume_idx: coro_indices.wrap_resume_idx,
    }
}
