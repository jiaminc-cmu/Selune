//! Selune standard library: Lua 5.4 standard libraries.

pub mod coroutine_lib;
pub mod debug_lib;
pub mod io_lib;
pub mod math;
pub mod os_lib;
pub mod package_lib;
pub mod pattern;
pub mod string_lib;
pub mod table_lib;
pub mod utf8_lib;

use selune_core::gc::{GcHeap, GcIdx, NativeFunction};
use selune_core::string::StringInterner;
use selune_core::table::Table;

/// Indices of native functions that need special VM dispatch.
pub struct StdlibIndices {
    pub table_sort_idx: GcIdx<NativeFunction>,
    pub string_gsub_idx: GcIdx<NativeFunction>,
    pub string_table_idx: GcIdx<Table>,
    pub coro_resume_idx: GcIdx<NativeFunction>,
    pub coro_yield_idx: GcIdx<NativeFunction>,
    pub coro_wrap_idx: GcIdx<NativeFunction>,
    pub coro_wrap_resume_idx: GcIdx<NativeFunction>,
    pub require_idx: GcIdx<NativeFunction>,
    pub package_loaded_idx: GcIdx<Table>,
    pub package_preload_idx: GcIdx<Table>,
    pub debug_getupvalue_idx: GcIdx<NativeFunction>,
    pub debug_setupvalue_idx: GcIdx<NativeFunction>,
}

/// Register all standard library modules into _ENV.
pub fn register_all(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) -> StdlibIndices {
    math::register(env_idx, gc, strings);
    os_lib::register(env_idx, gc, strings);
    utf8_lib::register(env_idx, gc, strings);
    let debug_indices = debug_lib::register(env_idx, gc, strings);
    io_lib::register(env_idx, gc, strings);
    let table_sort_idx = table_lib::register(env_idx, gc, strings);
    let string_indices = string_lib::register(env_idx, gc, strings);
    let coro_indices = coroutine_lib::register(env_idx, gc, strings);
    let pkg_indices = package_lib::register(env_idx, gc, strings);
    StdlibIndices {
        table_sort_idx,
        string_gsub_idx: string_indices.gsub_idx,
        string_table_idx: string_indices.string_table_idx,
        coro_resume_idx: coro_indices.resume_idx,
        coro_yield_idx: coro_indices.yield_idx,
        coro_wrap_idx: coro_indices.wrap_idx,
        coro_wrap_resume_idx: coro_indices.wrap_resume_idx,
        require_idx: pkg_indices.require_idx,
        package_loaded_idx: pkg_indices.package_loaded_idx,
        package_preload_idx: pkg_indices.package_preload_idx,
        debug_getupvalue_idx: debug_indices.getupvalue_idx,
        debug_setupvalue_idx: debug_indices.setupvalue_idx,
    }
}
