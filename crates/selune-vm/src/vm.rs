//! Lua VM state.

use std::collections::{HashMap, HashSet};

use crate::callinfo::{CallInfo, JitCallInfo};
use crate::dispatch;
use crate::error::LuaError;
use crate::metamethod::MetamethodNames;
use selune_compiler::opcode::OpCode;
use selune_compiler::proto::Proto;
use selune_core::gc::{
    GcHeap, GcIdx, NativeContext, NativeError, NativeFunction, UpVal, UpValLocation,
};
use selune_core::string::StringInterner;
use selune_core::value::TValue;

/// Type alias for JIT-compiled function pointers.
/// Signature: (vm_ptr, base) -> result_count or -1 (side-exit)
pub type JitFn = unsafe extern "C" fn(*mut Vm, usize) -> i64;

/// Per-proto JIT compilation state. Replaces separate HashMap/HashSet with a single Vec lookup.
#[derive(Clone, Copy, Debug)]
pub enum JitProtoState {
    /// Not yet compiled (or never attempted).
    None,
    /// Successfully compiled to native code.
    Compiled(JitFn),
    /// Blacklisted: too many side-exits, will not be recompiled.
    Blacklisted,
}

/// Per-coroutine state (stack, call stack, upvalues).
#[derive(Clone)]
pub struct LuaThread {
    pub stack: Vec<TValue>,
    pub call_stack: Vec<CallInfo>,
    pub jit_call_stack: Vec<JitCallInfo>,
    pub stack_top: usize,
    pub open_upvals: Vec<(usize, GcIdx<UpVal>)>,
    pub status: CoroutineStatus,
    /// Thread ID for this saved state (usize::MAX = main thread, otherwise coroutine index).
    pub thread_id: usize,
    /// Per-coroutine hook function.
    pub hook_func: TValue,
    /// Per-coroutine hook mask.
    pub hook_mask: u8,
    /// Per-coroutine hook count.
    pub hook_count: u32,
    /// Per-coroutine hook counter.
    pub hook_counter: u32,
    /// Per-coroutine hooks active flag.
    pub hooks_active: bool,
    /// Per-coroutine hook last line.
    pub hook_last_line: i32,
    /// Per-coroutine hook old PC.
    pub hook_old_pc: usize,
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
    /// Lightweight JIT call stack (shadow stack) — used for JIT-to-JIT calls only.
    pub jit_call_stack: Vec<JitCallInfo>,
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
    /// Nesting depth of call_function / execute_from (tracks C-equivalent stack depth).
    /// Incremented on each call_function entry, decremented on exit. Not reset by coroutine switches.
    pub c_stack_depth: usize,
    /// Maximum C stack depth before "C stack overflow".
    pub max_c_stack_depth: usize,
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
    /// Whether warn() stores messages in _WARN global (controlled by @store/@normal).
    pub warn_store: bool,
    /// Native index for warn (needs VM access for @on/@off/@store/_WARN).
    pub warn_idx: Option<GcIdx<NativeFunction>>,
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
    /// Native index for debug.traceback (needs VM access for call stack).
    pub debug_traceback_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for coroutine.running (needs VM access to know current coroutine).
    pub coro_running_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for string.format (needs VM access for __tostring metamethod).
    pub string_format_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for string.dump (needs VM access to read protos from closures).
    pub string_dump_idx: Option<GcIdx<NativeFunction>>,
    /// Stored TValue for the global `next` function (for pairs() to return same identity).
    pub next_val: TValue,
    /// Stored TValue for the ipairs iterator function (singleton).
    pub ipairs_iter_val: TValue,
    /// Native index for pairs (needs VM access for __pairs metamethod).
    pub pairs_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for ipairs iterator (needs VM access for __index metamethod).
    pub ipairs_iter_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for table.insert (needs VM access for __len/__newindex metamethods).
    pub table_insert_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for table.remove (needs VM access for __len/__index/__newindex metamethods).
    pub table_remove_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for table.concat (needs VM access for __len/__index metamethods).
    pub table_concat_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for table.unpack (needs VM access for __len/__index metamethods).
    pub table_unpack_idx: Option<GcIdx<NativeFunction>>,
    /// Depth counter for __close metamethod calls (for debug.traceback).
    pub in_tbc_close: u32,
    /// Depth counter for unyieldable native calls (e.g., inside string.gsub callback).
    pub nonyieldable_depth: u32,
    /// Set when an error originated from a __close metamethod (for traceback).
    pub last_error_from_close: bool,
    /// Stable main thread handle (coroutine-style table with thread metatable).
    pub main_thread_handle: Option<GcIdx<selune_core::table::Table>>,
    /// Handle table for the currently running coroutine (set during resume).
    pub running_coro_handle: Option<GcIdx<selune_core::table::Table>>,
    /// Native index for coroutine.isyieldable (needs VM access).
    pub coro_isyieldable_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for coroutine.close (needs VM access for TBC __close).
    pub coro_close_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for debug.sethook.
    pub debug_sethook_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for debug.gethook.
    pub debug_gethook_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for debug.getlocal.
    pub debug_getlocal_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for debug.setlocal.
    pub debug_setlocal_idx: Option<GcIdx<NativeFunction>>,
    /// Native index for debug.getregistry.
    pub debug_getregistry_idx: Option<GcIdx<NativeFunction>>,
    /// Hook function (nil = no hook).
    pub hook_func: TValue,
    /// Hook mask: HOOK_CALL=1, HOOK_RETURN=2, HOOK_LINE=4, HOOK_COUNT=8.
    pub hook_mask: u8,
    /// Hook count threshold (for count hooks).
    pub hook_count: u32,
    /// Hook counter (counts down from hook_count).
    pub hook_counter: u32,
    /// Whether hooks are active (fast-path check in dispatch loop).
    pub hooks_active: bool,
    /// Last line reported by a line hook (to avoid duplicate events).
    pub hook_last_line: i32,
    /// Previous PC for changedline detection (PUC's L->oldpc equivalent).
    pub hook_old_pc: usize,
    /// Flag to prevent recursive hooks.
    pub in_hook: bool,
    /// Flag to mark the next pushed call frame as a hook call.
    pub pending_hook_call: bool,
    /// Registry table for debug.getregistry().
    pub registry_idx: Option<GcIdx<selune_core::table::Table>>,
    /// Flag to prevent reentrant GC collection (set during run_finalizers).
    pub in_gc: bool,
    /// Fast guard: true only when a CloseReturnYield call status has been set.
    pub needs_close_return_resume: bool,
    /// Bitset: redirect_natives[idx] = true if native at GcIdx(idx) needs VM-dispatch redirect.
    pub redirect_natives: Vec<bool>,

    // --- JIT fields ---
    /// Per-proto JIT state: None / Compiled(fn) / Blacklisted. Indexed by proto_idx for O(1) lookup.
    pub jit_proto_state: Vec<JitProtoState>,
    /// Per-proto call counter for tier-up decisions.
    pub jit_call_counts: Vec<u32>,
    /// Per-proto side-exit counter. After too many side-exits, the proto is blacklisted.
    pub jit_side_exit_counts: Vec<u32>,
    /// Threshold: compile to JIT after this many calls.
    pub jit_threshold: u32,
    /// Whether JIT is enabled.
    pub jit_enabled: bool,
    /// Optional JIT compilation callback. Called when a proto reaches the tier-up threshold.
    /// The callback should attempt compilation and store the result via vm.jit_register().
    pub jit_compile_callback: Option<fn(&mut Vm, usize)>,
    /// Per-proto back-edge counter for detecting hot loops.
    pub jit_backedge_counts: Vec<u32>,
    /// Threshold: trigger JIT compilation after this many back-edge hits.
    pub jit_backedge_threshold: u32,
    /// OSR-compiled functions: (proto_idx, entry_pc) → native function pointer.
    pub jit_osr_functions: HashMap<(usize, usize), JitFn>,
    /// OSR entries that have failed (side-exited) and should not be recompiled.
    pub jit_osr_blacklist: HashSet<(usize, usize)>,
    /// Optional OSR compilation callback. Called when a back-edge triggers OSR.
    pub jit_osr_compile_callback: Option<fn(&mut Vm, usize, usize)>,
}

/// Format a source name for error messages (matching PUC Lua behavior).
/// - `=name` → `name` (exact source)
/// - `@file` → `file` (filename, truncated)
/// - otherwise → `[string "first_line..."]` (string chunk)
pub fn format_source_name(name: &str) -> String {
    const LUA_IDSIZE: usize = 60;
    if let Some(s) = name.strip_prefix('=') {
        // Exact source: use as-is minus the '=', truncated
        if s.len() >= LUA_IDSIZE {
            s[..LUA_IDSIZE - 1].to_string()
        } else {
            s.to_string()
        }
    } else if let Some(s) = name.strip_prefix('@') {
        // File source
        if s.len() >= LUA_IDSIZE {
            // Truncate from the end, add "..."
            format!("...{}", &s[s.len() - (LUA_IDSIZE - 4)..])
        } else {
            s.to_string()
        }
    } else {
        // String source: [string "first_line..."]
        // Get first line
        let first_line = name.lines().next().unwrap_or(name);
        // Overhead: [string " (9) + ..."] (5) = 14 chars; max output = LUA_IDSIZE - 1 = 59
        let max_content = LUA_IDSIZE - 1 - 14; // 45
        if first_line.len() > max_content || name.contains('\n') {
            let truncated = if first_line.len() > max_content {
                &first_line[..max_content]
            } else {
                first_line
            };
            format!("[string \"{}...\"]", truncated)
        } else {
            format!("[string \"{}\"]", first_line)
        }
    }
}

impl Vm {
    /// Create a new empty VM.
    pub fn new() -> Self {
        let stack = vec![TValue::nil(); 1024];
        Vm {
            stack,
            call_stack: Vec::with_capacity(32),
            jit_call_stack: Vec::with_capacity(32),
            gc: GcHeap::new(),
            strings: StringInterner::new(),
            stack_top: 0,
            protos: Vec::new(),
            open_upvals: Vec::new(),
            max_call_depth: 200,
            c_stack_depth: 0,
            max_c_stack_depth: 200,
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
            warn_store: false,
            warn_idx: None,
            require_idx: None,
            package_loaded_idx: None,
            package_preload_idx: None,
            error_idx: None,
            debug_getupvalue_idx: None,
            debug_setupvalue_idx: None,
            debug_getinfo_idx: None,
            debug_traceback_idx: None,
            coro_running_idx: None,
            string_format_idx: None,
            string_dump_idx: None,
            next_val: TValue::nil(),
            ipairs_iter_val: TValue::nil(),
            pairs_idx: None,
            ipairs_iter_idx: None,
            table_insert_idx: None,
            table_remove_idx: None,
            table_concat_idx: None,
            table_unpack_idx: None,
            in_tbc_close: 0,
            nonyieldable_depth: 0,
            last_error_from_close: false,
            main_thread_handle: None,
            running_coro_handle: None,
            coro_isyieldable_idx: None,
            coro_close_idx: None,
            debug_sethook_idx: None,
            debug_gethook_idx: None,
            debug_getlocal_idx: None,
            debug_setlocal_idx: None,
            debug_getregistry_idx: None,
            hook_func: TValue::nil(),
            hook_mask: 0,
            hook_count: 0,
            hook_counter: 0,
            hooks_active: false,
            hook_last_line: -1,
            hook_old_pc: 0,
            in_hook: false,
            pending_hook_call: false,
            registry_idx: None,
            in_gc: false,
            needs_close_return_resume: false,
            redirect_natives: Vec::new(),
            jit_proto_state: Vec::new(),
            jit_call_counts: Vec::new(),
            jit_side_exit_counts: Vec::new(),
            jit_threshold: 1000,
            jit_enabled: false,
            jit_compile_callback: None,
            jit_backedge_counts: Vec::new(),
            jit_backedge_threshold: 10_000,
            jit_osr_functions: HashMap::new(),
            jit_osr_blacklist: HashSet::new(),
            jit_osr_compile_callback: None,
        }
    }

    /// Mark a native function index as needing VM-dispatch redirect.
    pub fn mark_native_redirect(&mut self, idx: GcIdx<NativeFunction>) {
        let i = idx.0 as usize;
        if i >= self.redirect_natives.len() {
            self.redirect_natives.resize(i + 1, false);
        }
        self.redirect_natives[i] = true;
    }

    /// Check if a native function index needs VM-dispatch redirect.
    #[inline]
    pub fn is_redirect_native(&self, idx: GcIdx<NativeFunction>) -> bool {
        let i = idx.0 as usize;
        i < self.redirect_natives.len() && self.redirect_natives[i]
    }

    // --- JIT helper methods ---

    /// Get the JIT function pointer for a proto, if compiled. O(1) Vec lookup.
    #[inline]
    pub fn jit_get_fn(&self, proto_idx: usize) -> Option<JitFn> {
        match self.jit_proto_state.get(proto_idx) {
            Some(JitProtoState::Compiled(f)) => Some(*f),
            _ => Option::None,
        }
    }

    /// Check if a proto should be skipped for JIT compilation (already compiled or blacklisted).
    #[inline]
    pub fn jit_should_skip(&self, proto_idx: usize) -> bool {
        matches!(
            self.jit_proto_state.get(proto_idx),
            Some(JitProtoState::Compiled(_)) | Some(JitProtoState::Blacklisted)
        )
    }

    /// Register a JIT-compiled function for a proto. Defensively resizes if needed.
    #[inline]
    pub fn jit_register(&mut self, proto_idx: usize, jit_fn: JitFn) {
        if proto_idx >= self.jit_proto_state.len() {
            self.jit_proto_state
                .resize(proto_idx + 1, JitProtoState::None);
        }
        self.jit_proto_state[proto_idx] = JitProtoState::Compiled(jit_fn);
    }

    /// Record a side-exit for a proto. After 3 exits, blacklists the proto.
    #[inline]
    pub fn jit_record_side_exit(&mut self, proto_idx: usize) {
        if proto_idx >= self.jit_side_exit_counts.len() {
            self.jit_side_exit_counts.resize(proto_idx + 1, 0);
        }
        self.jit_side_exit_counts[proto_idx] += 1;
        if self.jit_side_exit_counts[proto_idx] >= 3 {
            if proto_idx < self.jit_proto_state.len() {
                self.jit_proto_state[proto_idx] = JitProtoState::Blacklisted;
            }
        }
    }

    /// Get the closure_idx of the innermost call frame.
    /// Checks jit_call_stack first (JIT frames are always innermost when active).
    #[inline]
    pub fn current_closure_idx(&self) -> Option<GcIdx<selune_core::gc::LuaClosure>> {
        if let Some(jf) = self.jit_call_stack.last() {
            Some(GcIdx(jf.closure_idx_raw, std::marker::PhantomData))
        } else if let Some(ci) = self.call_stack.last() {
            ci.closure_idx
        } else {
            None
        }
    }

    /// Mark all redirect natives in the bitset. Called once after all stdlib registration.
    fn mark_redirect_natives(&mut self) {
        // Collect all redirect native indices
        let indices: Vec<Option<GcIdx<NativeFunction>>> = vec![
            self.table_sort_idx,
            self.table_move_idx,
            self.string_gsub_idx,
            self.pcall_idx,
            self.xpcall_idx,
            self.coro_resume_idx,
            self.coro_yield_idx,
            self.coro_wrap_idx,
            self.coro_wrap_resume_idx,
            self.collectgarbage_idx,
            self.tostring_idx,
            self.load_idx,
            self.dofile_idx,
            self.loadfile_idx,
            self.require_idx,
            self.error_idx,
            self.debug_getupvalue_idx,
            self.debug_setupvalue_idx,
            self.debug_getinfo_idx,
            self.debug_traceback_idx,
            self.debug_sethook_idx,
            self.debug_gethook_idx,
            self.debug_getlocal_idx,
            self.debug_setlocal_idx,
            self.debug_getregistry_idx,
            self.coro_running_idx,
            self.coro_isyieldable_idx,
            self.coro_close_idx,
            self.string_format_idx,
            self.string_dump_idx,
            self.pairs_idx,
            self.ipairs_iter_idx,
            self.table_insert_idx,
            self.table_remove_idx,
            self.table_concat_idx,
            self.table_unpack_idx,
            self.warn_idx,
        ];
        for opt_idx in indices {
            if let Some(idx) = opt_idx {
                self.mark_native_redirect(idx);
            }
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
        self.debug_traceback_idx = Some(stdlib_indices.debug_traceback_idx);
        self.debug_sethook_idx = Some(stdlib_indices.debug_sethook_idx);
        self.debug_gethook_idx = Some(stdlib_indices.debug_gethook_idx);
        self.debug_getlocal_idx = Some(stdlib_indices.debug_getlocal_idx);
        self.debug_setlocal_idx = Some(stdlib_indices.debug_setlocal_idx);
        self.debug_getregistry_idx = Some(stdlib_indices.debug_getregistry_idx);
        self.coro_running_idx = Some(stdlib_indices.coro_running_idx);
        self.coro_isyieldable_idx = Some(stdlib_indices.coro_isyieldable_idx);
        self.coro_close_idx = Some(stdlib_indices.coro_close_idx);
        self.string_format_idx = Some(stdlib_indices.string_format_idx);
        self.string_dump_idx = Some(stdlib_indices.string_dump_idx);
        self.table_insert_idx = Some(stdlib_indices.table_insert_idx);
        self.table_remove_idx = Some(stdlib_indices.table_remove_idx);
        self.table_concat_idx = Some(stdlib_indices.table_concat_idx);
        self.table_unpack_idx = Some(stdlib_indices.table_unpack_idx);

        // Mark all redirect natives for fast bitset lookup in Call/TailCall dispatch
        self.mark_redirect_natives();

        // Create main thread handle (stable identity for coroutine.running() in main thread)
        let main_handle = self.gc.alloc_table(4, 0);
        self.gc
            .get_table_mut(main_handle)
            .raw_seti(1, TValue::from_integer(-2)); // special marker for main thread
        let running_sid = self.strings.intern(b"running");
        self.gc
            .get_table_mut(main_handle)
            .raw_seti(3, TValue::from_string_id(running_sid));
        self.gc.get_table_mut(main_handle).metatable = self.gc.thread_metatable;
        self.main_thread_handle = Some(main_handle);

        // Create string metatable with __index = string library table
        let string_mt = self.gc.alloc_table(0, 4);
        let index_name = self.strings.intern(b"__index");
        self.gc.get_table_mut(string_mt).raw_set_str(
            index_name,
            TValue::from_table(stdlib_indices.string_table_idx),
        );
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
        // Detect binary chunk (starts with \x1bLua signature)
        if source.starts_with(b"\x1bLua") {
            return self.load_binary_chunk(source, name, env);
        }

        let compile_source = source;

        // Take ownership of strings for compilation, then put them back
        let strings = std::mem::take(&mut self.strings);
        let (result, strings) =
            selune_compiler::compiler::compile_with_strings(compile_source, name, strings);
        self.strings = strings;
        let proto = result.map_err(|e| {
            // Format: "source:line: message" matching PUC Lua error format
            let src = format_source_name(name);
            format!("{}:{}: {}", src, e.line, e.message)
        })?;

        // Store the proto (with child flattening)
        let proto_idx = self.store_proto_tree(&proto);

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
        let proto =
            crate::binary_chunk::undump(data, name, &mut self.strings).map_err(|e| e.message)?;

        // Store the proto (with child flattening)
        let proto_idx = self.store_proto_tree(&proto);

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
        // Keep JIT vectors in sync with protos
        self.jit_proto_state.push(JitProtoState::None);
        self.jit_call_counts.push(0);
        self.jit_side_exit_counts.push(0);
        self.jit_backedge_counts.push(0);
        // Recursively flatten child protos into vm.protos and record flat indices
        let num_children = self.protos[idx].protos.len();
        let mut flat_indices = Vec::with_capacity(num_children);
        for i in 0..num_children {
            // Clone child out to avoid borrow issues, then recurse
            let child = self.protos[idx].protos[i].clone();
            let child_flat_idx = self.store_proto_tree(&child);
            flat_indices.push(child_flat_idx);
        }
        self.protos[idx].child_flat_indices = flat_indices;
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
        self.next_val = val;
        let name = self.strings.intern(b"next");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // ipairs_iter (singleton — allocated once, reused by all ipairs calls)
        let iter_idx = self.gc.alloc_native(native_ipairs_iter_stub, "ipairs_iter");
        self.ipairs_iter_val = TValue::from_native(iter_idx);
        self.ipairs_iter_idx = Some(iter_idx);

        // pairs — needs VM redirect for __pairs metamethod
        let idx = self.gc.alloc_native(native_pairs_stub, "pairs");
        let val = TValue::from_native(idx);
        self.pairs_idx = Some(idx);
        let name = self.strings.intern(b"pairs");
        self.gc.get_table_mut(env_idx).raw_set_str(name, val);

        // ipairs — stores ipairs_iter singleton as upvalue so it can return the same function
        let idx = self
            .gc
            .alloc_native_with_upvalue(native_ipairs, "ipairs", self.ipairs_iter_val);
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
        let idx = self
            .gc
            .alloc_native(native_collectgarbage_stub, "collectgarbage");
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
        self.warn_idx = Some(idx);

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
        // Search the coro_caller_stack for a saved state with matching thread_id
        for saved in &self.coro_caller_stack {
            if saved.thread_id == thread_id {
                return saved.stack.get(stack_idx).copied().unwrap_or(TValue::nil());
            }
        }
        // Also check saved coroutine states (for suspended coroutines)
        if thread_id < self.coroutines.len() {
            return self.coroutines[thread_id]
                .stack
                .get(stack_idx)
                .copied()
                .unwrap_or(TValue::nil());
        }
        TValue::nil()
    }

    /// Write a value to a saved thread's stack.
    fn set_thread_stack_value(&mut self, thread_id: usize, stack_idx: usize, val: TValue) {
        // Search the coro_caller_stack for a saved state with matching thread_id
        for saved in &mut self.coro_caller_stack {
            if saved.thread_id == thread_id {
                if stack_idx < saved.stack.len() {
                    saved.stack[stack_idx] = val;
                }
                return;
            }
        }
        // Also check saved coroutine states
        if thread_id < self.coroutines.len() && stack_idx < self.coroutines[thread_id].stack.len() {
            self.coroutines[thread_id].stack[stack_idx] = val;
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
            jit_call_stack: Vec::new(),
            stack_top: 0,
            open_upvals: Vec::new(),
            status: CoroutineStatus::Suspended,
            thread_id: id,
            hook_func: TValue::nil(),
            hook_mask: 0,
            hook_count: 0,
            hook_counter: 0,
            hooks_active: false,
            hook_last_line: -1,
            hook_old_pc: 0,
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
                self.gc.get_upval_mut(uv_idx).location =
                    UpValLocation::OpenInThread(si, save_thread_id);
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
    /// Save the current VM running state into a LuaThread by swapping Vecs
    /// (zero heap allocation). The `thread` receives the current state, and
    /// the VM's stack/call_stack/open_upvals are replaced with whatever was
    /// in `thread` (typically empty Vecs from a freshly-created LuaThread).
    pub fn save_running_state_swap(&mut self, thread: &mut LuaThread) {
        std::mem::swap(&mut self.stack, &mut thread.stack);
        std::mem::swap(&mut self.call_stack, &mut thread.call_stack);
        std::mem::swap(&mut self.jit_call_stack, &mut thread.jit_call_stack);
        std::mem::swap(&mut self.open_upvals, &mut thread.open_upvals);
        thread.stack_top = self.stack_top;
        thread.hook_func = self.hook_func;
        thread.hook_mask = self.hook_mask;
        thread.hook_count = self.hook_count;
        thread.hook_counter = self.hook_counter;
        thread.hooks_active = self.hooks_active;
        thread.hook_last_line = self.hook_last_line;
        thread.hook_old_pc = self.hook_old_pc;
    }

    /// Restore a LuaThread snapshot into the running state by swapping Vecs.
    /// After this call, the `thread` contains the VM's previous state (empty
    /// Vecs if the VM was just swapped out via save_running_state_swap).
    pub fn restore_running_state_swap(&mut self, thread: &mut LuaThread) {
        std::mem::swap(&mut self.stack, &mut thread.stack);
        std::mem::swap(&mut self.call_stack, &mut thread.call_stack);
        std::mem::swap(&mut self.jit_call_stack, &mut thread.jit_call_stack);
        std::mem::swap(&mut self.open_upvals, &mut thread.open_upvals);
        self.stack_top = thread.stack_top;
        self.hook_func = thread.hook_func;
        self.hook_mask = thread.hook_mask;
        self.hook_count = thread.hook_count;
        self.hook_counter = thread.hook_counter;
        self.hooks_active = thread.hooks_active;
        self.hook_last_line = thread.hook_last_line;
        self.hook_old_pc = thread.hook_old_pc;
    }

    /// Save the current running state back into the coroutine slot by swapping.
    pub fn save_coro_state(&mut self, coro_id: usize) {
        std::mem::swap(&mut self.stack, &mut self.coroutines[coro_id].stack);
        std::mem::swap(
            &mut self.call_stack,
            &mut self.coroutines[coro_id].call_stack,
        );
        std::mem::swap(
            &mut self.jit_call_stack,
            &mut self.coroutines[coro_id].jit_call_stack,
        );
        std::mem::swap(
            &mut self.open_upvals,
            &mut self.coroutines[coro_id].open_upvals,
        );
        self.coroutines[coro_id].stack_top = self.stack_top;
        self.coroutines[coro_id].hook_func = self.hook_func;
        self.coroutines[coro_id].hook_mask = self.hook_mask;
        self.coroutines[coro_id].hook_count = self.hook_count;
        self.coroutines[coro_id].hook_counter = self.hook_counter;
        self.coroutines[coro_id].hooks_active = self.hooks_active;
        self.coroutines[coro_id].hook_last_line = self.hook_last_line;
        self.coroutines[coro_id].hook_old_pc = self.hook_old_pc;
    }

    /// Restore coroutine state from coroutines[coro_id] into the running VM state
    /// by swapping. After this, the coroutine slot contains empty Vecs.
    pub fn restore_coro_into_running(&mut self, coro_id: usize) {
        std::mem::swap(&mut self.stack, &mut self.coroutines[coro_id].stack);
        std::mem::swap(
            &mut self.call_stack,
            &mut self.coroutines[coro_id].call_stack,
        );
        std::mem::swap(
            &mut self.jit_call_stack,
            &mut self.coroutines[coro_id].jit_call_stack,
        );
        std::mem::swap(
            &mut self.open_upvals,
            &mut self.coroutines[coro_id].open_upvals,
        );
        self.stack_top = self.coroutines[coro_id].stack_top;
        self.hook_func = self.coroutines[coro_id].hook_func;
        self.hook_mask = self.coroutines[coro_id].hook_mask;
        self.hook_count = self.coroutines[coro_id].hook_count;
        self.hook_counter = self.coroutines[coro_id].hook_counter;
        self.hooks_active = self.coroutines[coro_id].hooks_active;
        self.hook_last_line = self.coroutines[coro_id].hook_last_line;
        self.hook_old_pc = self.coroutines[coro_id].hook_old_pc;
    }

    // ---- Garbage Collection ----

    /// Run a full mark-sweep GC cycle. Returns approximate bytes freed.
    pub fn gc_collect(&mut self) -> usize {
        // Phase 1: Prepare mark bits
        self.gc.gc_prepare_marks();

        // Phase 1b: Classify weak tables (read __mode from metatables)
        self.classify_weak_tables();

        // Phase 2: Mark roots
        self.gc_mark_roots();

        // Phase 3: Propagate (traverse gray objects until none remain)
        loop {
            let work = self.gc.gc_propagate();
            if work == 0 {
                break;
            }
        }

        // Phase 3b: Ephemeron loop — mark values of ephemeron entries whose keys became marked
        loop {
            if !self.gc.gc_propagate_ephemerons() {
                break;
            }
            // Re-propagate any newly marked objects
            loop {
                let work = self.gc.gc_propagate();
                if work == 0 {
                    break;
                }
            }
        }

        // Phase 3c: Identify finalizable objects (unmarked with __gc) — resurrect them
        self.identify_finalizable_objects();

        // Phase 3d: Re-propagate finalizable objects' transitive closure
        loop {
            let work = self.gc.gc_propagate();
            if work == 0 {
                break;
            }
        }

        // Phase 4: Clear weak tables (remove entries referencing dead objects)
        self.gc.gc_clear_weak_tables();

        // Phase 5: Sweep
        let freed = self.gc.gc_sweep();

        // Phase 6: Run finalizers
        self.run_finalizers();

        freed
    }

    /// Classify weak tables: scan all marked tables for __mode metatable field.
    fn classify_weak_tables(&mut self) {
        let mode_sid = self.strings.intern(b"__mode");
        for i in 0..self.gc.tables.len() {
            if self.gc.tables[i].is_none() {
                continue;
            }
            let mt_idx = match self.gc.tables[i].as_ref().unwrap().metatable {
                Some(idx) => idx,
                None => continue,
            };
            // Read __mode from metatable
            let mode_val = self.gc.get_table(mt_idx).raw_get_str(mode_sid);
            if let Some(sid) = mode_val.as_string_id() {
                let bytes = self.strings.get_bytes(sid);
                let mut weak_k = false;
                let mut weak_v = false;
                for &b in bytes {
                    if b == b'k' {
                        weak_k = true;
                    }
                    if b == b'v' {
                        weak_v = true;
                    }
                }
                if i < self.gc.gc_state.table_weak_keys.len() {
                    self.gc.gc_state.table_weak_keys[i] = weak_k;
                }
                if i < self.gc.gc_state.table_weak_values.len() {
                    self.gc.gc_state.table_weak_values[i] = weak_v;
                }
            }
        }
    }

    /// Identify unmarked objects with __gc metamethods — resurrect them for finalization.
    fn identify_finalizable_objects(&mut self) {
        let gc_sid = self.strings.intern(b"__gc");

        // Check unmarked tables with __gc in their metatable
        for i in 0..self.gc.tables.len() {
            if self.gc.tables[i].is_none() {
                continue;
            }
            if i < self.gc.gc_state.table_marks.len() && self.gc.gc_state.table_marks[i] {
                continue;
            } // already marked
            if i < self.gc.gc_state.table_finalized.len() && self.gc.gc_state.table_finalized[i] {
                continue;
            } // already finalized

            let mt_idx = match self.gc.tables[i].as_ref().unwrap().metatable {
                Some(idx) => idx,
                None => continue,
            };
            let gc_val = self.gc.get_table(mt_idx).raw_get_str(gc_sid);
            if gc_val.is_nil() {
                continue;
            }

            // Resurrect: mark the table alive and add to finalization queue
            if i < self.gc.gc_state.table_marks.len() {
                self.gc.gc_state.table_marks[i] = true;
                self.gc.gc_state.gray_tables.push(i as u32);
            }
            // Also mark the metatable so __gc can be called
            let mt_i = mt_idx.0 as usize;
            if mt_i < self.gc.gc_state.table_marks.len() && !self.gc.gc_state.table_marks[mt_i] {
                self.gc.gc_state.table_marks[mt_i] = true;
                self.gc.gc_state.gray_tables.push(mt_idx.0);
            }
            self.gc
                .gc_state
                .finalization_queue
                .push(TValue::from_table(selune_core::gc::GcIdx(
                    i as u32,
                    std::marker::PhantomData,
                )));
        }

        // Check unmarked userdata with __gc in their metatable
        for i in 0..self.gc.userdata.len() {
            if self.gc.userdata[i].is_none() {
                continue;
            }
            if i < self.gc.gc_state.userdata_marks.len() && self.gc.gc_state.userdata_marks[i] {
                continue;
            }
            if i < self.gc.gc_state.userdata_finalized.len()
                && self.gc.gc_state.userdata_finalized[i]
            {
                continue;
            }

            let mt_idx = match self.gc.userdata[i].as_ref().unwrap().metatable {
                Some(idx) => idx,
                None => continue,
            };
            let gc_val = self.gc.get_table(mt_idx).raw_get_str(gc_sid);
            if gc_val.is_nil() {
                continue;
            }

            // Resurrect
            if i < self.gc.gc_state.userdata_marks.len() {
                self.gc.gc_state.userdata_marks[i] = true;
                self.gc.gc_state.gray_userdata.push(i as u32);
            }
            let mt_i = mt_idx.0 as usize;
            if mt_i < self.gc.gc_state.table_marks.len() && !self.gc.gc_state.table_marks[mt_i] {
                self.gc.gc_state.table_marks[mt_i] = true;
                self.gc.gc_state.gray_tables.push(mt_idx.0);
            }
            self.gc
                .gc_state
                .finalization_queue
                .push(TValue::from_userdata(selune_core::gc::GcIdx(
                    i as u32,
                    std::marker::PhantomData,
                )));
        }
    }

    /// Run __gc finalizers for objects in the finalization queue (LIFO order).
    fn run_finalizers(&mut self) {
        let queue: Vec<TValue> = self.gc.gc_state.finalization_queue.drain(..).collect();
        let was_in_gc = self.in_gc;
        self.in_gc = true;
        // Run in reverse (LIFO) order
        for obj in queue.iter().rev() {
            let gc_sid = self.strings.intern(b"__gc");
            // Look up __gc in the object's metatable
            let gc_func = if let Some(table_idx) = obj.as_table_idx() {
                let i = table_idx.0 as usize;
                // Mark as finalized
                if i < self.gc.gc_state.table_finalized.len() {
                    self.gc.gc_state.table_finalized[i] = true;
                }
                let mt_idx = match self.gc.get_table(table_idx).metatable {
                    Some(idx) => idx,
                    None => continue,
                };
                self.gc.get_table(mt_idx).raw_get_str(gc_sid)
            } else if let Some(ud_idx) = obj.as_userdata_idx() {
                let i = ud_idx.0 as usize;
                if i < self.gc.gc_state.userdata_finalized.len() {
                    self.gc.gc_state.userdata_finalized[i] = true;
                }
                let mt_idx = match self.gc.get_userdata(ud_idx).metatable {
                    Some(idx) => idx,
                    None => continue,
                };
                self.gc.get_table(mt_idx).raw_get_str(gc_sid)
            } else {
                continue;
            };

            // Skip if __gc is not callable (e.g., `true` sentinel)
            if gc_func.as_closure_idx().is_none() && gc_func.as_native_idx().is_none() {
                // Also check for __call metamethod on the gc_func
                if gc_func.as_table_idx().is_none() {
                    continue;
                }
            }

            // Call the finalizer, catching any errors (like pcall)
            let _ = dispatch::call_function(self, gc_func, &[*obj]);
        }
        self.in_gc = was_in_gc;
    }

    /// Mark all GC roots: stack values, call frame closures, _ENV, open upvalues,
    /// coroutine stacks, and registered native indices.
    /// Compute the highest live register (relative to base) for a Lua frame
    /// at the given PC, using local_vars debug info.
    fn frame_max_live_reg(proto: &Proto, pc: u32) -> usize {
        let mut max_live: usize = 0;
        for lv in &proto.local_vars {
            if pc >= lv.start_pc && pc < lv.end_pc {
                let r = lv.reg as usize + 1;
                if r > max_live {
                    max_live = r;
                }
            }
        }
        max_live
    }

    fn gc_mark_roots(&mut self) {
        // Precise per-frame stack marking: only mark live registers per frame.
        // This prevents dead for-loop body locals from keeping objects alive
        // in weak tables, matching PUC Lua's precise L->top behavior.
        let num_frames = self.call_stack.len();
        for frame_idx in 0..num_frames {
            let ci = &self.call_stack[frame_idx];
            let base = ci.base;
            let is_topmost = frame_idx == num_frames - 1;

            // Always mark the function slot
            if ci.func_stack_idx < self.stack.len() {
                self.gc.gc_mark_value(self.stack[ci.func_stack_idx]);
            }

            // Mark TBC slots (may be in "dead" registers during __close processing)
            for &slot in ci.tbc_slots.as_deref().unwrap_or(&[]) {
                if slot < self.stack.len() {
                    self.gc.gc_mark_value(self.stack[slot]);
                }
            }

            // Get closure and proto for Lua frames
            let cl_idx = match ci.closure_idx {
                Some(idx) => idx,
                None => {
                    // Native frame: still mark call setup area to next frame
                    // (e.g., return hook results stored between this frame and the next)
                    if !is_topmost {
                        let next_ci = &self.call_stack[frame_idx + 1];
                        let mark_start = ci.func_stack_idx + 1;
                        let mark_end = next_ci.base.max(next_ci.func_stack_idx + 1);
                        for abs in mark_start..mark_end.min(self.stack.len()) {
                            self.gc.gc_mark_value(self.stack[abs]);
                        }
                    }
                    continue;
                }
            };
            let proto_idx = match self.gc.closures[cl_idx.0 as usize].as_ref() {
                Some(cl) => cl.proto_idx,
                None => continue,
            };
            if proto_idx >= self.protos.len() {
                continue;
            }
            let proto = &self.protos[proto_idx];
            let pc = if ci.pc > 0 { ci.pc as u32 - 1 } else { 0 };

            // Mark live locals at current PC
            let max_live = Self::frame_max_live_reg(proto, pc);
            for r in 0..max_live {
                let abs = base + r;
                if abs < self.stack.len() {
                    self.gc.gc_mark_value(self.stack[abs]);
                }
            }

            if !is_topmost {
                // Non-topmost frame: suspended at a Call/TailCall.
                // Mark the call setup area (function + args) between this frame's
                // live locals and the next frame's base.
                let next_ci = &self.call_stack[frame_idx + 1];
                let call_setup_start = base + max_live;
                let call_setup_end = next_ci.base;
                // Also include func_stack_idx of the next frame and any vararg area
                let protect_end = call_setup_end.max(next_ci.func_stack_idx + 1);
                for abs in call_setup_start..protect_end.min(self.stack.len()) {
                    self.gc.gc_mark_value(self.stack[abs]);
                }
            } else {
                // Topmost frame: mark expression temporaries.
                // The current instruction determines what's live above max_live.
                if pc < proto.code.len() as u32 {
                    let inst = proto.code[pc as usize];
                    let op = inst.opcode();
                    if matches!(op, OpCode::Call | OpCode::TailCall) {
                        // Mark from Call.A through the call arguments
                        let inst_a = inst.a() as usize;
                        let inst_b = inst.b() as usize;
                        let call_end = if inst_b == 0 {
                            // Variable args: mark up to stack_top
                            self.stack_top.saturating_sub(base)
                        } else {
                            inst_a + inst_b
                        };
                        for r in inst_a..call_end {
                            let abs = base + r;
                            if abs < self.stack.len() {
                                self.gc.gc_mark_value(self.stack[abs]);
                            }
                        }
                    } else {
                        // Not at a Call: mark up to max_stack conservatively.
                        // GC can only run at Call instructions (collectgarbage/etc),
                        // but be safe for auto-GC that could trigger anywhere.
                        let frame_top = base + proto.max_stack_size as usize;
                        for abs in (base + max_live)..frame_top.min(self.stack.len()) {
                            self.gc.gc_mark_value(self.stack[abs]);
                        }
                    }
                }
            }
        }

        // Also mark anything below the first frame's func_stack_idx
        // (e.g., the main chunk's function value at stack[0])
        if let Some(first_ci) = self.call_stack.first() {
            for i in 0..first_ci.func_stack_idx.min(self.stack.len()) {
                self.gc.gc_mark_value(self.stack[i]);
            }
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
            let val = TValue::from_gc_sub(selune_core::gc::GC_SUB_UPVAL, uv_idx.0);
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
                let v = TValue::from_gc_sub(selune_core::gc::GC_SUB_UPVAL, uv_idx.0);
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
                let v = TValue::from_gc_sub(selune_core::gc::GC_SUB_UPVAL, uv_idx.0);
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

        // Mark thread metatable
        if let Some(idx) = self.gc.thread_metatable {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }
        // Mark main thread handle
        if let Some(idx) = self.main_thread_handle {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }
        // Mark running coro handle
        if let Some(idx) = self.running_coro_handle {
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
        if let Some(idx) = self.collectgarbage_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.table_move_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.debug_getupvalue_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.debug_setupvalue_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.debug_getinfo_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.debug_traceback_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.coro_running_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.string_format_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.string_dump_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.pairs_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.ipairs_iter_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.table_insert_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.table_remove_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.table_concat_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.table_unpack_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.coro_isyieldable_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.coro_close_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.debug_sethook_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.debug_gethook_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.debug_getlocal_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.debug_setlocal_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.debug_getregistry_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        if let Some(idx) = self.warn_idx {
            self.gc.gc_mark_value(TValue::from_native(idx));
        }
        // Mark stored TValues for pairs/ipairs singletons
        if !self.next_val.is_nil() {
            self.gc.gc_mark_value(self.next_val);
        }
        if !self.ipairs_iter_val.is_nil() {
            self.gc.gc_mark_value(self.ipairs_iter_val);
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
        // Mark hook function
        if !self.hook_func.is_nil() {
            self.gc.gc_mark_value(self.hook_func);
        }
        // Mark registry table
        if let Some(idx) = self.registry_idx {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }

        // Mark io library thread-local roots (default input/output, file metatable)
        let (io_input, io_output, io_mt) = selune_stdlib::io_lib::gc_roots();
        if let Some(idx) = io_input {
            self.gc.gc_mark_value(TValue::from_userdata(idx));
        }
        if let Some(idx) = io_output {
            self.gc.gc_mark_value(TValue::from_userdata(idx));
        }
        if let Some(idx) = io_mt {
            self.gc.gc_mark_value(TValue::from_table(idx));
        }
        // Mark io.lines iterator states
        for idx in selune_stdlib::io_lib::gc_lines_roots(&self.gc) {
            self.gc.gc_mark_value(TValue::from_userdata(idx));
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
        if self.open_upvals.is_empty() {
            return;
        }
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
            let base = base_val.as_full_integer(ctx.gc).ok_or_else(|| {
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
    if ctx.args.is_empty() {
        return Err(NativeError::String(
            "bad argument #1 to 'assert' (value expected)".to_string(),
        ));
    }
    let val = ctx.args[0];
    if val.is_falsy() {
        if ctx.args.len() <= 1 {
            // No message argument provided: default "assertion failed!" with source prefix
            Err(NativeError::String("assertion failed!".to_string()))
        } else {
            // PUC Lua: assert passes the message through lua_error unchanged (no prefix)
            // This includes nil, tables, strings, etc.
            let msg = ctx.args[1];
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
    let check_mt = |mt_idx: GcIdx<selune_core::table::Table>,
                    gc: &GcHeap,
                    strings: &mut StringInterner|
     -> Vec<TValue> {
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
        Ok(Some((k, v))) => Ok(vec![k, v]),
        Ok(None) => Ok(vec![TValue::nil()]),
        Err(()) => Err(NativeError::String("invalid key to 'next'".to_string())),
    }
}

/// Stub for pairs - actual dispatch happens via call_function for __pairs metamethod support.
fn native_pairs_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "pairs stub should not be called directly".to_string(),
    ))
}

fn native_ipairs(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let table_val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if table_val.as_table_idx().is_none() {
        return Err(NativeError::String(
            "bad argument #1 to 'ipairs' (table expected)".to_string(),
        ));
    }
    // Return (ipairs_iter_singleton, table, 0) — ipairs_iter_val set via upvalue is not available here
    // We use a dummy that will be replaced in the redirect path. For now ipairs doesn't need redirect.
    // Actually, we just need the singleton from the NativeContext. Let's use a trick: store in upvalue.
    // But the simplest approach: ipairs doesn't need redirect, it just returns the stored iter.
    // Problem: we don't have access to Vm here. Let's allocate from ctx.
    // Actually the test requires identity: ipairs{} == ipairs{}. The iter must be same TValue.
    // We need upvalue to pass the singleton. Let's use the upvalue field.
    let iter_val = ctx.upvalue;
    Ok(vec![iter_val, table_val, TValue::from_integer(0)])
}

/// Stub for ipairs_iter - actual dispatch via call_function for __index support.
fn native_ipairs_iter_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "ipairs_iter stub should not be called directly".to_string(),
    ))
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
        // Check if this is a thread (coroutine handle with thread metatable)
        if let Some(thread_mt) = gc.thread_metatable {
            if let Some(tbl_idx) = val.as_table_idx() {
                if gc.get_table(tbl_idx).metatable == Some(thread_mt) {
                    return format!("thread: 0x{:x}", val.gc_index().unwrap_or(0));
                }
            }
        }
        format!("table: 0x{:x}", val.gc_index().unwrap_or(0))
    } else if val.as_closure_idx().is_some() || val.as_native_idx().is_some() {
        format!("function: 0x{:x}", val.gc_index().unwrap_or(0))
    } else if val.is_userdata() {
        format!("userdata: 0x{:x}", val.gc_index().unwrap_or(0))
    } else {
        format!("{:?}", val)
    }
}
