//! Lua VM state.

use crate::callinfo::CallInfo;
use crate::dispatch;
use crate::error::LuaError;
use crate::metamethod::MetamethodNames;
use selune_compiler::proto::Proto;
use selune_core::gc::{
    GcHeap, GcIdx, NativeContext, NativeError, NativeFunction, UpVal, UpValLocation,
};
use selune_core::string::StringInterner;
use selune_core::value::TValue;

/// Per-coroutine state (stack, call stack, upvalues).
#[derive(Clone)]
pub struct LuaThread {
    pub stack: Vec<TValue>,
    pub call_stack: Vec<CallInfo>,
    pub stack_top: usize,
    pub open_upvals: Vec<(usize, GcIdx<UpVal>)>,
    pub status: CoroutineStatus,
}

/// Coroutine lifecycle states.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoroutineStatus {
    /// Created or yielded — ready to be resumed.
    Suspended,
    /// Currently executing.
    Running,
    /// Resumed another coroutine (waiting for it to yield/finish).
    Normal,
    /// Finished execution or errored out.
    Dead,
}

/// The Lua virtual machine.
///
/// The `stack`, `call_stack`, `stack_top`, and `open_upvals` fields always
/// refer to the **currently running** thread. When a coroutine is resumed,
/// the caller's state is saved into a `LuaThread` and the coroutine's
/// state is swapped in. On yield or return, the reverse swap happens.
pub struct Vm {
    /// Value stack (registers) — belongs to the running thread.
    pub stack: Vec<TValue>,
    /// Call stack (frames) — belongs to the running thread.
    pub call_stack: Vec<CallInfo>,
    /// GC heap.
    pub gc: GcHeap,
    /// String interner (shared with compiler output).
    pub strings: StringInterner,
    /// Top of stack (index of first free slot) — belongs to the running thread.
    pub stack_top: usize,
    /// All prototypes (flattened from nested tree).
    pub protos: Vec<Proto>,
    /// Open upvalues sorted by stack index (descending) — belongs to the running thread.
    pub open_upvals: Vec<(usize, GcIdx<UpVal>)>,
    /// Max call depth before stack overflow.
    pub max_call_depth: usize,
    /// Pre-interned metamethod names.
    pub mm_names: Option<MetamethodNames>,
    /// Native indices for pcall/xpcall (set during register_natives).
    pub pcall_idx: Option<GcIdx<NativeFunction>>,
    pub xpcall_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for table.sort (needs special VM dispatch for Lua comparator).
    pub table_sort_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for table.move (needs VM dispatch for metamethods).
    pub table_move_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for string.gsub (needs special VM dispatch for function replacement).
    pub string_gsub_idx: Option<GcIdx<NativeFunction>>,
    /// Coroutine storage: suspended thread states, indexed by coroutine ID.
    pub coroutines: Vec<LuaThread>,
    /// Index of the currently running coroutine (None = main thread).
    pub running_coro: Option<usize>,
    /// Stack of caller thread states for nested coroutine resumes.
    /// When coroutine A resumes B, A's state is pushed here.
    pub coro_caller_stack: Vec<LuaThread>,
    /// Native index for coroutine.resume (needs special VM dispatch).
    pub coro_resume_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for coroutine.yield (needs special VM dispatch).
    pub coro_yield_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for coroutine.wrap (needs special VM dispatch to set __call).
    pub coro_wrap_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for coroutine.wrap's internal resume function.
    pub coro_wrap_resume_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for collectgarbage (needs full VM access for gc_collect).
    pub collectgarbage_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for tostring (needs full VM access for __tostring metamethod).
    pub tostring_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for load (needs full VM access to compile + create closure).
    pub load_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for dofile (needs full VM access to compile + execute).
    pub dofile_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for loadfile (needs full VM access to compile + create closure).
    pub loadfile_idx: Option<GcIdx<NativeFunction>>,
    /// The _ENV table GcIdx, retained for load/dofile/loadfile to get default env.
    pub env_idx: Option<GcIdx<selune_core::table::Table>>,
    /// Whether warn() output is enabled (controlled by @on/@off).
    pub warn_enabled: bool,
    /// Native index for require (needs full VM access for loadfile + call_function).
    pub require_idx: Option<GcIdx<NativeFunction>>,
    /// The package.loaded table, for require() to check/store cached modules.
    pub package_loaded_idx: Option<GcIdx<selune_core::table::Table>>,
    /// The package.preload table, for require() to check preloaded modules.
    pub package_preload_idx: Option<GcIdx<selune_core::table::Table>>,
    /// Native index for error() (needs VM access for source:line prefix).
    pub error_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for debug.getupvalue (needs VM access for Proto upvalue names).
    pub debug_getupvalue_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for debug.setupvalue (needs VM access for Proto upvalue names + open upvals).
    pub debug_setupvalue_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for debug.getinfo (needs VM access for call stack / proto info).
    pub debug_getinfo_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for coroutine.running (needs VM access to know current coroutine).
    pub coro_running_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for string.format (needs VM access for __tostring metamethod).
    pub string_format_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for string.dump (needs VM access to read protos from closures).
    pub string_dump_idx: Option<GcIdx<NativeFunction>>,
}

impl Vm {
    /// Create a new empty VM.
    pub fn new() -> Self {
        let stack = vec![TValue::nil(); 1024];
        Vm {
            stack,
            call_stack: Vec::new(),
            gc: GcHeap::new(),
            strings: StringInterner::new(),
            stack_top: 0,
            protos: Vec::new(),
            open_upvals: Vec::new(),
            max_call_depth: 200,
            mm_names: None,
            pcall_idx: None,
            xpcall_idx: None,
            table_sort_idx: None,
            table_move_idx: None,
            string_gsub_idx: None,
            coroutines: Vec::new(),
            running_coro: None,
            coro_caller_stack: Vec::new(),
            coro_resume_idx: None,
            coro_yield_idx: None,
            coro_wrap_idx: None,
            coro_wrap_resume_idx: None,
            collectgarbage_idx: None,
            tostring_idx: None,
            load_idx: None,
            dofile_idx: None,
            loadfile_idx: None,
            env_idx: None,
            warn_enabled: false,
            require_idx: None,
            package_loaded_idx: None,
            package_preload_idx: None,
            error_idx: None,
            debug_getupvalue_idx: None,
            debug_setupvalue_idx: None,
            debug_getinfo_idx: None,
            coro_running_idx: None,
            string_format_idx: None,
            string_dump_idx: None,
        }
    }

    /// Ensure the stack has at least `size` slots from `base`.
    pub fn ensure_stack(&mut self, base: usize, size: usize) {
        let needed = base + size;
        if needed > self.stack.len() {
            self.stack.resize(needed, TValue::nil());
        }
    }

    /// Flatten nested protos into a flat list, returning the index of the root.
    #[allow(dead_code)]
    fn flatten_protos(_proto: &Proto, _out: &mut Vec<Proto>) -> usize {
        // Not used — we store the proto tree as-is and navigate via protos[i]
        0
    }

    /// Execute a compiled proto with the given string interner.
    pub fn execute(
        &mut self,
        proto: &Proto,
        strings: StringInterner,
    ) -> Result<Vec<TValue>, LuaError> {
        self.strings = strings;

        // Initialize metamethod names
        self.mm_names = Some(MetamethodNames::init(&mut self.strings));

        // Store the proto tree (keep it as-is, navigate with proto_idx)
        self.protos.clear();
        self.store_proto_tree(proto);

        // Create _ENV table
        let env_idx = self.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        self.env_idx = Some(env_idx);

        // Register native functions
        self.register_natives(env_idx);

        // Register standard library modules
        let stdlib_indices = selune_stdlib::register_all(env_idx, &mut self.gc, &mut self.strings);
        self.table_sort_idx = Some(stdlib_indices.table_sort_idx);
        self.table_move_idx = Some(stdlib_indices.table_move_idx);
        self.string_gsub_idx = Some(stdlib_indices.string_gsub_idx);
        self.coro_resume_idx = Some(stdlib_indices.coro_resume_idx);
        self.coro_yield_idx = Some(stdlib_indices.coro_yield_idx);
        self.coro_wrap_idx = Some(stdlib_indices.coro_wrap_idx);
        self.coro_wrap_resume_idx = Some(stdlib_indices.coro_wrap_resume_idx);
        self.require_idx = Some(stdlib_indices.require_idx);
        self.package_loaded_idx = Some(stdlib_indices.package_loaded_idx);
        self.package_preload_idx = Some(stdlib_indices.package_preload_idx);
        self.debug_getupvalue_idx = Some(stdlib_indices.debug_getupvalue_idx);
        self.debug_setupvalue_idx = Some(stdlib_indices.debug_setupvalue_idx);
        self.debug_getinfo_idx = Some(stdlib_indices.debug_getinfo_idx);
        self.coro_running_idx = Some(stdlib_indices.coro_running_idx);
        self.string_format_idx = Some(stdlib_indices.string_format_idx);
        self.string_dump_idx = Some(stdlib_indices.string_dump_idx);

        // Create string metatable with __index = string library table
        let string_mt = self.gc.alloc_table(0, 4);
        let index_name = self.strings.intern(b"__index");
        self.gc
            .get_table_mut(string_mt)
            .raw_set_str(index_name, TValue::from_table(stdlib_indices.string_table_idx));
        self.gc.string_metatable = Some(string_mt);

        // Create a top-level closure with _ENV as upvalue[0]
        let env_upval_idx = self.gc.alloc_upval(UpValLocation::Closed(env_val));
        let top_closure_idx = self.gc.alloc_closure(0, vec![env_upval_idx]);
        let top_closure_val = TValue::from_closure(top_closure_idx);

        // Ensure stack is big enough for this proto
        let base = 1; // R[0] = function value, R[1..] = registers
        self.ensure_stack(base, proto.max_stack_size as usize + 1);
        self.stack[0] = top_closure_val;
        self.stack_top = base + proto.max_stack_size as usize;

        // Push the top-level call frame
        let mut ci = CallInfo::new(base, 0);
        ci.closure_idx = Some(top_closure_idx);
        ci.func_stack_idx = 0;
        self.call_stack.push(ci);

        let result = dispatch::execute(self, 0);

        self.call_stack.pop();
        result
    }

    /// Compile source and create a closure, reusing the VM's string interner.
    /// Returns the closure TValue (ready to call) or a compile error string.
    pub fn load_chunk(
        &mut self,
        source: &[u8],
        name: &str,
        env: Option<TValue>,
    ) -> Result<TValue, String> {
        // Take ownership of strings for compilation, then put them back
        let strings = std::mem::take(&mut self.strings);
        let (result, strings) = selune_compiler::compiler::compile_with_strings(source, name, strings);
        self.strings = strings;
        let proto = result.map_err(|e| {
            // Format: "source:line: message" matching PUC Lua error format
            let src = if name.starts_with('=') {
                &name[1..]
            } else if name.starts_with('@') {
                &name[1..]
            } else {
                name
            };
            format!("{}:{}: {}", src, e.line, e.message)
        })?;

        // Store the proto
        let proto_idx = self.protos.len();
        self.protos.push(proto);

        // Determine the _ENV upvalue: use custom env or default _ENV
        let env_val = env.unwrap_or_else(|| {
            self.env_idx
                .map(TValue::from_table)
                .unwrap_or(TValue::nil())
        });
        let env_upval_idx = self.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = self.gc.alloc_closure(proto_idx, vec![env_upval_idx]);
        Ok(TValue::from_closure(closure_idx))
    }

    /// Load a binary chunk (from string.dump) into the VM.
    pub fn load_binary_chunk(
        &mut self,
        data: &[u8],
        name: &str,
        env: Option<TValue>,
    ) -> Result<TValue, String> {
        let proto = crate::binary_chunk::undump(data, name, &mut self.strings)
            .map_err(|e| e.message)?;

        // Store the proto
        let proto_idx = self.protos.len();
        self.protos.push(proto);

        // Create upvalues — for the main chunk, first upvalue is _ENV
        let num_upvalues = self.protos[proto_idx].upvalues.len();
        let mut upval_indices = Vec::with_capacity(num_upvalues);
        for i in 0..num_upvalues {
            if i == 0 {
                // First upvalue is _ENV
                let env_val = env.unwrap_or_else(|| {
                    self.env_idx
                        .map(TValue::from_table)
                        .unwrap_or(TValue::nil())
                });
                let uv_idx = self.gc.alloc_upval(UpValLocation::Closed(env_val));
                upval_indices.push(uv_idx);
            } else {
                // Other upvalues start as nil
                let uv_idx = self.gc.alloc_upval(UpValLocation::Closed(TValue::nil()));
                upval_indices.push(uv_idx);
            }
        }

        let closure_idx = self.gc.alloc_closure(proto_idx, upval_indices);
        Ok(TValue::from_closure(closure_idx))
    }

    /// Store proto tree recursively. Returns the flat index.
    fn store_proto_tree(&mut self, proto: &Proto) -> usize {
        let idx = self.protos.len();
        self.protos.push(proto.clone());
        // Recursively store children — they're already inline in proto.protos
        // The flat indices won't match the child indices, but we access children
        // through the proto.protos[i] field directly.
        idx
    }

    /// Register built-in native functions into _ENV.
    fn register_natives(&mut self, env_idx: GcIdx<selune_core::table::Table>) {
        // print
        let print_idx = self.gc.alloc_native(native_print, "print");
        let print_val = TValue::from_native(print_idx);
        let print_name = self.strings.intern(b"print");
        self.gc
            .get_table_mut(env_idx)
            .raw_set_str(print_name, print_val);

        // type
        let type_idx = self.gc.alloc_native(native_type, "type");
        let type_val = TValue::from_native(type_idx);
        let type_name = self.strings.intern(b"type");
        self.gc
            .get_table_mut(env_idx)
            .raw_set_str(type_name, type_val);

        // tostring - stub; actual dispatch via call_function for __tostring metamethod
        let tostring_idx = self.gc.alloc_native(native_tostring_stub, "tostring");
        let tostring_val = TValue::from_native(tostring_idx);
        let tostring_name = self.strings.intern(b"tostring");
        self.gc
            .get_table_mut(env_idx)
            .raw_set_str(tostring_name, tostring_val);
        self.tostring_idx = Some(tostring_idx);

        // tonumber
        let tonumber_idx = self.gc.alloc_native(native_tonumber, "tonumber");
        let tonumber_val = TValue::from_native(tonumber_idx);
        let tonumber_name = self.strings.intern(b"tonumber");
        self.gc
            .get_table_mut(env_idx)
            .raw_set_str(tonumber_name, tonumber_val);

        // error (redirect: needs VM access for source:line prefix)
        let idx = self.gc.alloc_native(native_error, "error");
        self.error_idx = Some(idx);
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"error");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // assert
        let idx = self.gc.alloc_native(native_assert, "assert");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"assert");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // select
        let idx = self.gc.alloc_native(native_select, "select");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"select");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // rawget
        let idx = self.gc.alloc_native(native_rawget, "rawget");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"rawget");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // rawset
        let idx = self.gc.alloc_native(native_rawset, "rawset");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"rawset");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // rawequal
        let idx = self.gc.alloc_native(native_rawequal, "rawequal");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"rawequal");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // rawlen
        let idx = self.gc.alloc_native(native_rawlen, "rawlen");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"rawlen");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // setmetatable
        let idx = self.gc.alloc_native(native_setmetatable, "setmetatable");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"setmetatable");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // getmetatable
        let idx = self.gc.alloc_native(native_getmetatable, "getmetatable");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"getmetatable");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // unpack (Lua 5.1 compat, also table.unpack in 5.4)
        let idx = self.gc.alloc_native(native_unpack, "unpack");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"unpack");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // next
        let idx = self.gc.alloc_native(native_next, "next");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"next");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // pairs
        let idx = self.gc.alloc_native(native_pairs, "pairs");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"pairs");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // ipairs
        let idx = self.gc.alloc_native(native_ipairs, "ipairs");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"ipairs");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // pcall - registered as a dummy native; actual dispatch is in Call opcode
        let idx = self.gc.alloc_native(native_pcall_stub, "pcall");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"pcall");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);
        self.pcall_idx = Some(idx);

        // xpcall - registered as a dummy native; actual dispatch is in Call opcode
        let idx = self.gc.alloc_native(native_xpcall_stub, "xpcall");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"xpcall");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);
        self.xpcall_idx = Some(idx);

        // collectgarbage - stub; actual dispatch via call_function for full VM access
        let idx = self.gc.alloc_native(native_collectgarbage_stub, "collectgarbage");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"collectgarbage");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);
        self.collectgarbage_idx = Some(idx);

        // load - stub; actual dispatch via call_function
        let idx = self.gc.alloc_native(native_load_stub, "load");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"load");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);
        self.load_idx = Some(idx);

        // dofile - stub; actual dispatch via call_function
        let idx = self.gc.alloc_native(native_dofile_stub, "dofile");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"dofile");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);
        self.dofile_idx = Some(idx);

        // loadfile - stub; actual dispatch via call_function
        let idx = self.gc.alloc_native(native_loadfile_stub, "loadfile");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"loadfile");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);
        self.loadfile_idx = Some(idx);

        // warn
        let idx = self.gc.alloc_native(native_warn_stub, "warn");
        let val = TValue::from_native(idx);
        let name = self.strings.intern(b"warn");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // _VERSION
        let version_sid = self.strings.intern(b"Lua 5.4");
        let version_val = TValue::from_string_id(version_sid);
        let version_name = self.strings.intern(b"_VERSION");
        self.gc
            .get_table_mut(env_idx)
            .raw_set_str(version_name, version_val);

        // _G = _ENV (same table)
        let g_name = self.strings.intern(b"_G");
        let env_val = TValue::from_table(env_idx);
        self.gc.get_table_mut(env_idx).raw_set_str(g_name, env_val);
    }

    /// Get an upvalue's current value.
    pub fn get_upval_value(&self, uv_idx: GcIdx<UpVal>) -> TValue {
        let uv = self.gc.get_upval(uv_idx);
        match uv.location {
            UpValLocation::Open(stack_idx) => self.stack[stack_idx],
            UpValLocation::OpenInThread(stack_idx, thread_id) => {
                // Access a saved coroutine/caller thread's stack
                self.get_thread_stack_value(thread_id, stack_idx)
            }
            UpValLocation::Closed(val) => val,
        }
    }

    /// Set an upvalue's value.
    pub fn set_upval_value(&mut self, uv_idx: GcIdx<UpVal>, val: TValue) {
        let uv = self.gc.get_upval(uv_idx);
        match uv.location {
            UpValLocation::Open(stack_idx) => {
                self.stack[stack_idx] = val;
            }
            UpValLocation::OpenInThread(stack_idx, thread_id) => {
                self.set_thread_stack_value(thread_id, stack_idx, val);
            }
            UpValLocation::Closed(_) => {
                self.gc.get_upval_mut(uv_idx).location = UpValLocation::Closed(val);
            }
        }
    }

    /// Read a value from a saved thread's stack.
    fn get_thread_stack_value(&self, thread_id: usize, stack_idx: usize) -> TValue {
        // thread_id maps into coro_caller_stack (saved caller states)
        // or coroutines (saved coroutine states)
        // We use a convention: thread_id == usize::MAX means main thread saved in caller stack
        // Otherwise it's a coroutine ID
        if thread_id == usize::MAX {
            // Main thread is saved in the caller stack (most recent entry)
            if let Some(caller) = self.coro_caller_stack.last() {
                return caller.stack.get(stack_idx).copied().unwrap_or(TValue::nil());
            }
        } else if thread_id < self.coroutines.len() {
            return self.coroutines[thread_id].stack.get(stack_idx).copied().unwrap_or(TValue::nil());
        }
        TValue::nil()
    }

    /// Write a value to a saved thread's stack.
    fn set_thread_stack_value(&mut self, thread_id: usize, stack_idx: usize, val: TValue) {
        if thread_id == usize::MAX {
            if let Some(caller) = self.coro_caller_stack.last_mut() {
                if stack_idx < caller.stack.len() {
                    caller.stack[stack_idx] = val;
                }
            }
        } else if thread_id < self.coroutines.len() {
            if stack_idx < self.coroutines[thread_id].stack.len() {
                self.coroutines[thread_id].stack[stack_idx] = val;
            }
        }
    }

    /// Find or create an open upvalue for the given stack index.
    pub fn find_or_create_open_upval(&mut self, stack_idx: usize) -> GcIdx<UpVal> {
        // Search existing open upvals
        for &(si, uv_idx) in &self.open_upvals {
            if si == stack_idx {
                return uv_idx;
            }
        }
        // Create new
        let uv_idx = self.gc.alloc_upval(UpValLocation::Open(stack_idx));
        self.open_upvals.push((stack_idx, uv_idx));
        // Keep sorted by stack index descending
        self.open_upvals.sort_by(|a, b| b.0.cmp(&a.0));
        uv_idx
    }

    /// Create a new coroutine from a function value. Returns its ID (index into coroutines).
    pub fn create_coroutine(&mut self, func: TValue) -> usize {
        let id = self.coroutines.len();
        let mut thread = LuaThread {
            stack: vec![TValue::nil(); 256],
            call_stack: Vec::new(),
            stack_top: 0,
            open_upvals: Vec::new(),
            status: CoroutineStatus::Suspended,
        };
        // Place the function at R[0]
        thread.stack[0] = func;
        self.coroutines.push(thread);
        id
    }

    /// Remap open upvalues when switching threads.
    /// Converts Open(idx) upvalues belonging to the current thread to
    /// OpenInThread(idx, save_thread_id), so they remain accessible
    /// when a different thread's stack is active.
    pub fn remap_open_upvals_to_thread(&mut self, save_thread_id: usize) {
        // Iterate all open upvals on the current thread and remap them
        for &(_stack_idx, uv_idx) in &self.open_upvals {
            let uv = self.gc.get_upval(uv_idx);
            if let UpValLocation::Open(si) = uv.location {
                self.gc.get_upval_mut(uv_idx).location = UpValLocation::OpenInThread(si, save_thread_id);
            }
        }
    }

    /// Restore open upvalues for the current thread.
    /// Converts OpenInThread(idx, thread_id) back to Open(idx) for upvalues
    /// that belong to the newly active thread.
    pub fn restore_open_upvals_from_thread(&mut self, restore_thread_id: usize) {
        // Search all upvalues in the GC and convert back matching OpenInThread
        for i in 0..self.gc.upvals.len() {
            if let Some(uv) = &self.gc.upvals[i] {
                if let UpValLocation::OpenInThread(si, tid) = uv.location {
                    if tid == restore_thread_id {
                        self.gc.upvals[i].as_mut().unwrap().location = UpValLocation::Open(si);
                    }
                }
            }
        }
    }

    /// Save the current running state into a LuaThread snapshot.
    pub fn save_running_state(&self) -> LuaThread {
        LuaThread {
            stack: self.stack.clone(),
            call_stack: self.call_stack.clone(),
            stack_top: self.stack_top,
            open_upvals: self.open_upvals.clone(),
            status: CoroutineStatus::Normal, // caller becomes Normal while waiting
        }
    }

    /// Restore a LuaThread snapshot into the running state.
    pub fn restore_running_state(&mut self, thread: LuaThread) {
        self.stack = thread.stack;
        self.call_stack = thread.call_stack;
        self.stack_top = thread.stack_top;
        self.open_upvals = thread.open_upvals;
    }

    /// Save the current running state back into the coroutine slot.
    pub fn save_coro_state(&mut self, coro_id: usize) {
        self.coroutines[coro_id].stack = self.stack.clone();
        self.coroutines[coro_id].call_stack = self.call_stack.clone();
        self.coroutines[coro_id].stack_top = self.stack_top;
        self.coroutines[coro_id].open_upvals = self.open_upvals.clone();
    }

    // ---- Garbage Collection ----

    /// Run a full mark-sweep GC cycle. Returns approximate bytes freed.
    pub fn gc_collect(&mut self) -> usize {
        // Phase 1: Prepare mark bits
        self.gc.gc_prepare_marks();

        // Phase 2: Mark roots
        self.gc_mark_roots();

        // Phase 3: Propagate (traverse gray objects until none remain)
        loop {
            let work = self.gc.gc_propagate();
            if work == 0 {
                break;
            }
        }

        // Phase 4: Sweep
        self.gc.gc_sweep()
    }

    /// Mark all GC roots: stack values, call frame closures, _ENV, open upvalues,
    /// coroutine stacks, and registered native indices.
    fn gc_mark_roots(&mut self) {
        // Mark running thread's stack
        let top = self.stack_top.max(
            self.call_stack
                .last()
                .map_or(0, |ci| ci.base + 256 /* max_stack approx */),
        );
        for i in 0..top.min(self.stack.len()) {
            let val = self.stack[i];
            self.gc.gc_mark_value(val);
        }

        // Mark closures in call frames
        for ci in &self.call_stack {
            if let Some(closure_idx) = ci.closure_idx {
                let val = TValue::from_closure(closure_idx);
                self.gc.gc_mark_value(val);
            }
        }

        // Mark open upvalues (running thread)
        for &(_stack_idx, uv_idx) in &self.open_upvals {
            let val = TValue::from_gc_sub(
                selune_core::gc::GC_SUB_UPVAL,
                uv_idx.0,
            );
            self.gc.gc_mark_value(val);
        }

        // Mark coroutine states
        for coro in &self.coroutines {
            for &val in &coro.stack {
                self.gc.gc_mark_value(val);
            }
            for ci in &coro.call_stack {
                if let Some(closure_idx) = ci.closure_idx {
                    let v = TValue::from_closure(closure_idx);
                    self.gc.gc_mark_value(v);
                }
            }
            for &(_stack_idx, uv_idx) in &coro.open_upvals {
                let v = TValue::from_gc_sub(
                    selune_core::gc::GC_SUB_UPVAL,
                    uv_idx.0,
                );
                self.gc.gc_mark_value(v);
            }
        }

        // Mark caller stack (nested coroutine resumes)
        for caller in &self.coro_caller_stack {
            for &val in &caller.stack {
                self.gc.gc_mark_value(val);
            }
            for ci in &caller.call_stack {
                if let Some(closure_idx) = ci.closure_idx {
                    let v = TValue::from_closure(closure_idx);
                    self.gc.gc_mark_value(v);
                }
            }
            for &(_stack_idx, uv_idx) in &caller.open_upvals {
                let v = TValue::from_gc_sub(
                    selune_core::gc::GC_SUB_UPVAL,
                    uv_idx.0,
                );
                self.gc.gc_mark_value(v);
            }
        }

        // Mark string metatable
        if let Some(idx) = self.gc.string_metatable {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }
        // Mark number metatable
        if let Some(idx) = self.gc.number_metatable {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }
        // Mark boolean metatable
        if let Some(idx) = self.gc.boolean_metatable {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }
        // Mark nil metatable
        if let Some(idx) = self.gc.nil_metatable {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }

        // Mark registered native function indices (these are always roots)
        if let Some(idx) = self.pcall_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.xpcall_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.table_sort_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.string_gsub_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.coro_resume_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.coro_yield_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.coro_wrap_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.coro_wrap_resume_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.tostring_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.load_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.dofile_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.loadfile_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.require_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.error_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        // Mark _ENV table
        if let Some(idx) = self.env_idx {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }
        // Mark package.loaded and package.preload tables
        if let Some(idx) = self.package_loaded_idx {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }
        if let Some(idx) = self.package_preload_idx {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }
    }

    /// Check if GC should run and perform a cycle if needed.
    pub fn gc_check(&mut self) {
        if self.gc.gc_should_step() {
            self.gc_collect();
        }
    }

    /// Close all open upvalues at or above the given level.
    pub fn close_upvalues(&mut self, level: usize) {
        let mut i = 0;
        while i < self.open_upvals.len() {
            let (stack_idx, uv_idx) = self.open_upvals[i];
            if stack_idx >= level {
                let val = self.stack[stack_idx];
                self.gc.get_upval_mut(uv_idx).location = UpValLocation::Closed(val);
                self.open_upvals.remove(i);
            } else {
                i += 1;
            }
        }
    }
}

impl Default for Vm {
    fn default() -> Self {
        Self::new()
    }
}

// ---- Native functions ----

fn native_print(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let mut first = true;
    for arg in ctx.args {
        if !first {
            print!("\t");
        }
        first = false;
        print!("{}", format_value(*arg, ctx.gc, ctx.strings));
    }
    println!();
    Ok(vec![])
}

fn native_type(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    if ctx.args.is_empty() {
        return Err(NativeError::String(
            "bad argument #1 to 'type' (value expected)".to_string(),
        ));
    }
    let val = ctx.args[0];
    let type_name = selune_core::object::lua_type_name(val, ctx.gc);
    let sid = ctx.strings.intern(type_name.as_bytes());
    Ok(vec![TValue::from_string_id(sid)])
}

fn native_tostring_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "tostring stub should not be called directly".to_string(),
    ))
}

fn native_tonumber(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    if ctx.args.is_empty() {
        return Err(NativeError::String(
            "bad argument #1 to 'tonumber' (value expected)".to_string(),
        ));
    }
    let val = ctx.args[0];
    let base_arg = ctx.args.get(1).copied();

    // tonumber(s, base) — base conversion
    if let Some(base_val) = base_arg {
        if !base_val.is_nil() {
            let base = base_val
                .as_full_integer(ctx.gc)
                .ok_or_else(|| {
                    NativeError::String(
                        "bad argument #2 to 'tonumber' (number has no integer representation)"
                            .to_string(),
                    )
                })?;
            if !(2..=36).contains(&base) {
                return Err(NativeError::String(
                    "bad argument #2 to 'tonumber' (invalid base)".to_string(),
                ));
            }
            // First arg must be a string
            let sid = val.as_string_id().ok_or_else(|| {
                NativeError::String(
                    "bad argument #1 to 'tonumber' (string expected, got number)".to_string(),
                )
            })?;
            let bytes = ctx.strings.get_bytes(sid);
            let s = std::str::from_utf8(bytes).unwrap_or("");
            let s = s.trim();
            if s.is_empty() {
                return Ok(vec![TValue::nil()]);
            }
            // Parse in given base
            match i64::from_str_radix(s, base as u32) {
                Ok(i) => return Ok(vec![TValue::from_full_integer(i, ctx.gc)]),
                Err(_) => return Ok(vec![TValue::nil()]),
            }
        }
    }

    // tonumber(x) — no base
    if let Some(i) = val.as_full_integer(ctx.gc) {
        return Ok(vec![TValue::from_full_integer(i, ctx.gc)]);
    }
    if val.as_float().is_some() {
        return Ok(vec![val]);
    }
    if let Some(sid) = val.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid);
        let s = std::str::from_utf8(bytes).unwrap_or("");
        let s = s.trim();
        // Use coerce::to_number_from_str which handles hex (with sign and wrapping),
        // decimal integers, and floats
        if let Some(result) = crate::coerce::tonumber_from_str(s, ctx.gc) {
            return Ok(vec![result]);
        }
    }
    Ok(vec![TValue::nil()])
}

fn native_error(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let msg = ctx.args.first().copied().unwrap_or(TValue::nil());
    Err(NativeError::Value(msg))
}

fn native_assert(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if val.is_falsy() {
        let msg = ctx.args.get(1).copied().unwrap_or(TValue::nil());
        if let Some(sid) = msg.as_string_id() {
            // PUC Lua: assert(v, msg) raises msg directly (no prefix)
            let s = String::from_utf8_lossy(ctx.strings.get_bytes(sid)).into_owned();
            Err(NativeError::String(s))
        } else if msg.is_nil() {
            Err(NativeError::String("assertion failed!".to_string()))
        } else {
            // Non-string error value (number, table, etc.)
            Err(NativeError::Value(msg))
        }
    } else {
        // On success, return all arguments passed to assert
        Ok(ctx.args.to_vec())
    }
}

fn native_select(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let index = ctx.args.first().copied().unwrap_or(TValue::nil());
    if let Some(sid) = index.as_string_id() {
        let s = ctx.strings.get_bytes(sid);
        if s == b"#" {
            // Return count of remaining args
            let count = if ctx.args.len() > 1 {
                ctx.args.len() - 1
            } else {
                0
            };
            return Ok(vec![TValue::from_integer(count as i64)]);
        }
    }
    if let Some(i) = index.as_full_integer(ctx.gc) {
        let nargs = ctx.args.len() as i64 - 1; // exclude index itself
        let start = if i < 0 {
            // Negative index: count from end
            let adjusted = nargs + 1 + i; // e.g., -1 → nargs
            if adjusted < 1 {
                return Err(NativeError::String(
                    "bad argument #1 to 'select' (index out of range)".to_string(),
                ));
            }
            adjusted as usize
        } else if i == 0 {
            return Err(NativeError::String(
                "bad argument #1 to 'select' (index out of range)".to_string(),
            ));
        } else if i > nargs {
            // Out of range positive index: return nothing
            return Ok(vec![]);
        } else {
            i as usize
        };
        Ok(ctx.args[start..].to_vec())
    } else {
        Err(NativeError::String(
            "bad argument #1 to 'select' (number or string expected, got other)".to_string(),
        ))
    }
}

fn native_rawget(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let key = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let table_idx = table_val.as_table_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'rawget' (table expected)".to_string())
    })?;
    Ok(vec![ctx.gc.table_raw_get(table_idx, key)])
}

fn native_rawset(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let key = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let val = ctx.args.get(2).copied().unwrap_or(TValue::nil());
    let table_idx = table_val.as_table_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'rawset' (table expected)".to_string())
    })?;
    ctx.gc
        .table_raw_set(table_idx, key, val)
        .map_err(|e: &str| NativeError::String(e.to_string()))?;
    Ok(vec![table_val])
}

fn native_rawequal(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let a = ctx.args.first().copied().unwrap_or(TValue::nil());
    let b = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let (eq, _) = crate::compare::lua_eq(a, b, ctx.gc, ctx.strings);
    Ok(vec![TValue::from_bool(eq)])
}

fn native_rawlen(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if let Some(table_idx) = val.as_table_idx() {
        let len = ctx.gc.get_table(table_idx).length();
        Ok(vec![TValue::from_full_integer(len, ctx.gc)])
    } else if let Some(sid) = val.as_string_id() {
        let len = ctx.strings.get_bytes(sid).len() as i64;
        Ok(vec![TValue::from_full_integer(len, ctx.gc)])
    } else {
        Err(NativeError::String(
            "bad argument #1 to 'rawlen' (table or string expected)".to_string(),
        ))
    }
}

fn native_setmetatable(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let mt_val = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let table_idx = table_val.as_table_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'setmetatable' (table expected)".to_string())
    })?;
    // Check for __metatable protection
    if let Some(existing_mt) = ctx.gc.get_table(table_idx).metatable {
        let mm_name = ctx.strings.intern(b"__metatable");
        let mm_val = ctx.gc.get_table(existing_mt).raw_get_str(mm_name);
        if !mm_val.is_nil() {
            return Err(NativeError::String(
                "cannot change a protected metatable".to_string(),
            ));
        }
    }
    if mt_val.is_nil() {
        ctx.gc.get_table_mut(table_idx).metatable = None;
    } else {
        let mt_idx = mt_val.as_table_idx().ok_or_else(|| {
            NativeError::String(
                "bad argument #2 to 'setmetatable' (nil or table expected)".to_string(),
            )
        })?;
        ctx.gc.get_table_mut(table_idx).metatable = Some(mt_idx);
    }
    Ok(vec![table_val])
}

fn native_getmetatable(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    // Helper: given a metatable idx, check __metatable and return appropriately
    let check_mt = |mt_idx: GcIdx<selune_core::table::Table>, gc: &GcHeap, strings: &mut StringInterner| -> Vec<TValue> {
        let mm_name = strings.intern(b"__metatable");
        let mm_val = gc.get_table(mt_idx).raw_get_str(mm_name);
        if !mm_val.is_nil() {
            vec![mm_val]
        } else {
            vec![TValue::from_table(mt_idx)]
        }
    };
    if let Some(table_idx) = val.as_table_idx() {
        if let Some(mt_idx) = ctx.gc.get_table(table_idx).metatable {
            Ok(check_mt(mt_idx, ctx.gc, ctx.strings))
        } else {
            Ok(vec![TValue::nil()])
        }
    } else if val.is_string() {
        // String metatable
        if let Some(mt_idx) = ctx.gc.string_metatable {
            Ok(check_mt(mt_idx, ctx.gc, ctx.strings))
        } else {
            Ok(vec![TValue::nil()])
        }
    } else if let Some(ud_idx) = val.as_userdata_idx() {
        if let Some(mt_idx) = ctx.gc.get_userdata(ud_idx).metatable {
            Ok(check_mt(mt_idx, ctx.gc, ctx.strings))
        } else {
            Ok(vec![TValue::nil()])
        }
    } else if val.is_number() || val.gc_sub_tag() == Some(selune_core::gc::GC_SUB_BOXED_INT) {
        if let Some(mt_idx) = ctx.gc.number_metatable {
            Ok(check_mt(mt_idx, ctx.gc, ctx.strings))
        } else {
            Ok(vec![TValue::nil()])
        }
    } else if val.is_bool() {
        if let Some(mt_idx) = ctx.gc.boolean_metatable {
            Ok(check_mt(mt_idx, ctx.gc, ctx.strings))
        } else {
            Ok(vec![TValue::nil()])
        }
    } else if val.is_nil() {
        if let Some(mt_idx) = ctx.gc.nil_metatable {
            Ok(check_mt(mt_idx, ctx.gc, ctx.strings))
        } else {
            Ok(vec![TValue::nil()])
        }
    } else {
        Ok(vec![TValue::nil()])
    }
}

fn native_unpack(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let list_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let table_idx = list_val.as_table_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'unpack' (table expected)".to_string())
    })?;

    let i = ctx
        .args
        .get(1)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(1);
    let j = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or_else(|| ctx.gc.get_table(table_idx).length());

    let mut results = Vec::new();
    let mut k = i;
    while k <= j {
        results.push(ctx.gc.get_table(table_idx).raw_geti(k));
        k += 1;
    }
    Ok(results)
}

fn native_next(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let table_idx = table_val.as_table_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'next' (table expected)".to_string())
    })?;
    let key = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    match ctx.gc.get_table(table_idx).next(key) {
        Some((k, v)) => Ok(vec![k, v]),
        None => Ok(vec![TValue::nil()]),
    }
}

fn native_pairs(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let _table_idx = table_val.as_table_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'pairs' (table expected)".to_string())
    })?;
    // Return (next, table, nil)
    let next_idx = ctx.gc.alloc_native(native_next, "next");
    let next_val = TValue::from_native(next_idx);
    Ok(vec![next_val, table_val, TValue::nil()])
}

fn native_ipairs(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let _table_idx = table_val.as_table_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'ipairs' (table expected)".to_string())
    })?;
    // Return (ipairs_iter, table, 0)
    let iter_idx = ctx.gc.alloc_native(native_ipairs_iter, "ipairs_iter");
    let iter_val = TValue::from_native(iter_idx);
    Ok(vec![iter_val, table_val, TValue::from_integer(0)])
}

fn native_ipairs_iter(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let table_idx = table_val.as_table_idx().ok_or_else(|| {
        NativeError::String("bad argument #1 to 'ipairs iterator' (table expected)".to_string())
    })?;
    let i = ctx
        .args
        .get(1)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(0);
    let next_i = i + 1;
    let val = ctx.gc.get_table(table_idx).raw_geti(next_i);
    if val.is_nil() {
        Ok(vec![TValue::nil()])
    } else {
        Ok(vec![TValue::from_full_integer(next_i, ctx.gc), val])
    }
}

/// Stub for pcall - actual dispatch happens in the Call opcode.
fn native_pcall_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "pcall stub should not be called directly".to_string(),
    ))
}

/// Stub for xpcall - actual dispatch happens in the Call opcode.
fn native_xpcall_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "xpcall stub should not be called directly".to_string(),
    ))
}

fn native_collectgarbage_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "collectgarbage stub should not be called directly".to_string(),
    ))
}

fn native_load_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "load stub should not be called directly".to_string(),
    ))
}

fn native_dofile_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "dofile stub should not be called directly".to_string(),
    ))
}

fn native_loadfile_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "loadfile stub should not be called directly".to_string(),
    ))
}

fn native_warn_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    // warn is handled inline (not redirected) since it only needs string args.
    // Check for @on/@off control messages
    if let Some(first) = _ctx.args.first() {
        if let Some(sid) = first.as_string_id() {
            let s = std::str::from_utf8(_ctx.strings.get_bytes(sid)).unwrap_or("");
            if s == "@on" || s == "@off" {
                // Control messages are handled by the caller (need Vm access)
                // For now, just ignore - actual @on/@off needs Vm.warn_enabled
                return Ok(vec![]);
            }
        }
    }
    // Regular warn: just print to stderr when enabled
    // Note: actual warn_enabled check requires Vm access, so we just print here.
    // This will be refined when redirected through call_function.
    Ok(vec![])
}

/// Format a TValue for display (used by print, tostring).
pub fn format_value(
    val: TValue,
    gc: &selune_core::gc::GcHeap,
    strings: &selune_core::string::StringInterner,
) -> String {
    if val.is_nil() {
        "nil".to_string()
    } else if let Some(b) = val.as_bool() {
        if b {
            "true".to_string()
        } else {
            "false".to_string()
        }
    } else if let Some(i) = val.as_full_integer(gc) {
        format!("{}", i)
    } else if let Some(f) = val.as_float() {
        crate::coerce::lua_format_float(f)
    } else if let Some(sid) = val.as_string_id() {
        let bytes = strings.get_bytes(sid);
        String::from_utf8_lossy(bytes).into_owned()
    } else if val.is_table() {
        format!("table: 0x{:x}", val.gc_index().unwrap_or(0))
    } else if val.as_closure_idx().is_some() || val.as_native_idx().is_some() {
        format!("function: 0x{:x}", val.gc_index().unwrap_or(0))
    } else if val.is_userdata() {
        format!("userdata: 0x{:x}", val.gc_index().unwrap_or(0))
    } else {
        format!("{:?}", val)
    }
}
