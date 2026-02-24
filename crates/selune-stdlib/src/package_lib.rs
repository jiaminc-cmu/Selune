//! Lua 5.4 package library.
//!
//! Provides `require()` and the `package` table. The `require` function
//! needs special VM dispatch (full Vm access for loadfile + call_function).

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError, NativeFunction};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;

/// Indices returned by `register()` that the VM needs for dispatch.
pub struct PackageIndices {
    pub require_idx: GcIdx<NativeFunction>,
    pub package_loaded_idx: GcIdx<Table>,
    pub package_preload_idx: GcIdx<Table>,
}

/// Register the package library into _ENV.
///
/// Creates `package.loaded`, `package.preload`, `package.path`, etc.
/// Pre-populates `package.loaded` with already-registered stdlib modules.
/// Returns indices the VM needs for special dispatch.
pub fn register(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) -> PackageIndices {
    let pkg_table = gc.alloc_table(0, 16);

    // package.loaded
    let loaded = gc.alloc_table(0, 16);
    let loaded_key = strings.intern(b"loaded");
    gc.get_table_mut(pkg_table)
        .raw_set_str(loaded_key, TValue::from_table(loaded));

    // package.preload
    let preload = gc.alloc_table(0, 8);
    let preload_key = strings.intern(b"preload");
    gc.get_table_mut(pkg_table)
        .raw_set_str(preload_key, TValue::from_table(preload));

    // package.path - default Lua search path
    let path_key = strings.intern(b"path");
    let default_path = strings.intern_or_create(b"./?.lua;./?/init.lua");
    gc.get_table_mut(pkg_table)
        .raw_set_str(path_key, TValue::from_string_id(default_path));

    // package.cpath - C library search path (stub, we don't support C modules)
    let cpath_key = strings.intern(b"cpath");
    let default_cpath = strings.intern_or_create(b"");
    gc.get_table_mut(pkg_table)
        .raw_set_str(cpath_key, TValue::from_string_id(default_cpath));

    // package.config - configuration string (separator, template, etc.)
    let config_key = strings.intern(b"config");
    let config_val = strings.intern_or_create(b"/\n;\n?\n!\n-");
    gc.get_table_mut(pkg_table)
        .raw_set_str(config_key, TValue::from_string_id(config_val));

    // package.searchpath(name, path [, sep [, rep]])
    let sp_idx = gc.alloc_native(native_searchpath, "package.searchpath");
    let sp_key = strings.intern(b"searchpath");
    gc.get_table_mut(pkg_table)
        .raw_set_str(sp_key, TValue::from_native(sp_idx));

    // package.searchers (populated with searcher functions)
    let searchers = gc.alloc_table(4, 0);

    // Searcher 1: preload searcher
    let searcher1_idx = gc.alloc_native(native_searcher_preload, "searcher_preload");
    gc.get_table_mut(searchers)
        .raw_seti(1, TValue::from_native(searcher1_idx));

    // Searcher 2: Lua file searcher (stub - the real one uses loadfile via VM)
    let searcher2_idx = gc.alloc_native(native_searcher_lua_stub, "searcher_lua");
    gc.get_table_mut(searchers)
        .raw_seti(2, TValue::from_native(searcher2_idx));

    let searchers_key = strings.intern(b"searchers");
    gc.get_table_mut(pkg_table)
        .raw_set_str(searchers_key, TValue::from_table(searchers));

    // require - stub native; real dispatch happens through VM
    let require_idx = gc.alloc_native(native_require_stub, "require");
    let require_key = strings.intern(b"require");
    gc.get_table_mut(env_idx)
        .raw_set_str(require_key, TValue::from_native(require_idx));

    // Set package table in _ENV
    let pkg_key = strings.intern(b"package");
    gc.get_table_mut(env_idx)
        .raw_set_str(pkg_key, TValue::from_table(pkg_table));

    // Pre-populate package.loaded with already-loaded stdlib modules
    pre_populate_loaded(loaded, env_idx, gc, strings);

    PackageIndices {
        require_idx,
        package_loaded_idx: loaded,
        package_preload_idx: preload,
    }
}

/// Pre-populate package.loaded with stdlib module tables that are already registered.
fn pre_populate_loaded(
    loaded: GcIdx<Table>,
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) {
    let module_names = [
        "math",
        "table",
        "string",
        "coroutine",
        "os",
        "utf8",
        "debug",
        "io",
        "package",
    ];
    for name in &module_names {
        let key = strings.intern(name.as_bytes());
        let val = gc.get_table(env_idx).raw_get_str(key);
        if !val.is_nil() {
            gc.get_table_mut(loaded).raw_set_str(key, val);
        }
    }
    // Also mark _G itself as loaded
    let g_key = strings.intern(b"_G");
    gc.get_table_mut(loaded)
        .raw_set_str(g_key, TValue::from_table(env_idx));
}

// ---------------------------------------------------------------------------
// require(modname) - stub; real dispatch in dispatch.rs via do_require()
// ---------------------------------------------------------------------------

fn native_require_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "require() must be dispatched through VM (internal error)".into(),
    ))
}

// ---------------------------------------------------------------------------
// package.searchpath(name, path [, sep [, rep]])
// ---------------------------------------------------------------------------

fn native_searchpath(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let name_arg = ctx.args.first().copied().unwrap_or(TValue::nil());
    let path_arg = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let sep_arg = ctx.args.get(2).copied().unwrap_or(TValue::nil());
    let rep_arg = ctx.args.get(3).copied().unwrap_or(TValue::nil());

    let name_sid = name_arg.as_string_id().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'searchpath' (string expected)".into())
    })?;
    let path_sid = path_arg.as_string_id().ok_or_else(|| {
        NativeError::String("bad argument #2 to 'searchpath' (string expected)".into())
    })?;

    let name = String::from_utf8_lossy(ctx.strings.get_bytes(name_sid)).into_owned();
    let path = String::from_utf8_lossy(ctx.strings.get_bytes(path_sid)).into_owned();

    let sep = if let Some(sid) = sep_arg.as_string_id() {
        String::from_utf8_lossy(ctx.strings.get_bytes(sid)).into_owned()
    } else {
        ".".to_string()
    };

    let rep = if let Some(sid) = rep_arg.as_string_id() {
        String::from_utf8_lossy(ctx.strings.get_bytes(sid)).into_owned()
    } else {
        "/".to_string()
    };

    let modname = name.replace(&sep, &rep);
    let mut tried = Vec::new();

    for template in path.split(';') {
        let filepath = template.replace('?', &modname);
        if std::path::Path::new(&filepath).exists() {
            let sid = ctx.strings.intern_or_create(filepath.as_bytes());
            return Ok(vec![TValue::from_string_id(sid)]);
        }
        tried.push(format!("\n\tno file '{}'", filepath));
    }

    let err_msg = tried.join("");
    let err_sid = ctx.strings.intern_or_create(err_msg.as_bytes());
    Ok(vec![TValue::nil(), TValue::from_string_id(err_sid)])
}

// ---------------------------------------------------------------------------
// Searcher 1: preload searcher
// Called as searcher(modname). Checks package.preload[modname].
// ---------------------------------------------------------------------------

fn native_searcher_preload(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    // This is a stub — the real preload check happens in do_require() which has
    // access to the preload table index. But for completeness, return nil.
    let _ = ctx;
    Ok(vec![TValue::nil()])
}

// ---------------------------------------------------------------------------
// Searcher 2: Lua file searcher (stub)
// The real Lua file searcher is implemented in do_require() since it needs
// loadfile via full VM access.
// ---------------------------------------------------------------------------

fn native_searcher_lua_stub(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let _ = ctx;
    Ok(vec![TValue::nil()])
}

/// Search for a module file using package.path patterns.
/// Returns the resolved file path or None.
pub fn search_lua_file(modname: &str, path: &str) -> Option<String> {
    let modname_path = modname.replace('.', "/");
    for template in path.split(';') {
        let filepath = template.replace('?', &modname_path);
        if std::path::Path::new(&filepath).exists() {
            return Some(filepath);
        }
    }
    None
}
