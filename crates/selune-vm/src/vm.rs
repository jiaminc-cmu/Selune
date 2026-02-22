//! Lua VM state.

use crate::callinfo::CallInfo;
use crate::dispatch;
use crate::error::LuaError;
use selune_compiler::proto::Proto;
use selune_core::gc::{GcHeap, GcIdx, NativeContext, UpVal, UpValLocation};
use selune_core::string::StringInterner;
use selune_core::value::TValue;

/// The Lua virtual machine.
pub struct Vm {
    /// Value stack (registers).
    pub stack: Vec<TValue>,
    /// Call stack (frames).
    pub call_stack: Vec<CallInfo>,
    /// GC heap.
    pub gc: GcHeap,
    /// String interner (shared with compiler output).
    pub strings: StringInterner,
    /// Top of stack (index of first free slot).
    pub stack_top: usize,
    /// All prototypes (flattened from nested tree).
    pub protos: Vec<Proto>,
    /// Open upvalues sorted by stack index (descending).
    pub open_upvals: Vec<(usize, GcIdx<UpVal>)>,
    /// Max call depth before stack overflow.
    pub max_call_depth: usize,
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

        // Store the proto tree (keep it as-is, navigate with proto_idx)
        self.protos.clear();
        self.store_proto_tree(proto);

        // Create _ENV table
        let env_idx = self.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);

        // Register native functions
        self.register_natives(env_idx);

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

        // tostring
        let tostring_idx = self.gc.alloc_native(native_tostring, "tostring");
        let tostring_val = TValue::from_native(tostring_idx);
        let tostring_name = self.strings.intern(b"tostring");
        self.gc
            .get_table_mut(env_idx)
            .raw_set_str(tostring_name, tostring_val);

        // tonumber
        let tonumber_idx = self.gc.alloc_native(native_tonumber, "tonumber");
        let tonumber_val = TValue::from_native(tonumber_idx);
        let tonumber_name = self.strings.intern(b"tonumber");
        self.gc
            .get_table_mut(env_idx)
            .raw_set_str(tonumber_name, tonumber_val);
    }

    /// Get an upvalue's current value.
    pub fn get_upval_value(&self, uv_idx: GcIdx<UpVal>) -> TValue {
        let uv = self.gc.get_upval(uv_idx);
        match uv.location {
            UpValLocation::Open(stack_idx) => self.stack[stack_idx],
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
            UpValLocation::Closed(_) => {
                self.gc.get_upval_mut(uv_idx).location = UpValLocation::Closed(val);
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

fn native_print(ctx: &mut NativeContext) -> Result<Vec<TValue>, String> {
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

fn native_type(ctx: &mut NativeContext) -> Result<Vec<TValue>, String> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let type_name = selune_core::object::lua_type_name(val, ctx.gc);
    let sid = ctx.strings.intern(type_name.as_bytes());
    Ok(vec![TValue::from_string_id(sid)])
}

fn native_tostring(ctx: &mut NativeContext) -> Result<Vec<TValue>, String> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    let s = format_value(val, ctx.gc, ctx.strings);
    let sid = ctx.strings.intern_or_create(s.as_bytes());
    Ok(vec![TValue::from_string_id(sid)])
}

fn native_tonumber(ctx: &mut NativeContext) -> Result<Vec<TValue>, String> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if let Some(i) = val.as_integer() {
        return Ok(vec![TValue::from_integer(i)]);
    }
    if val.as_float().is_some() {
        return Ok(vec![val]);
    }
    if let Some(sid) = val.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid);
        let s = std::str::from_utf8(bytes).unwrap_or("");
        if let Ok(i) = s.parse::<i64>() {
            return Ok(vec![TValue::from_full_integer(i, ctx.gc)]);
        }
        if let Ok(f) = s.parse::<f64>() {
            return Ok(vec![TValue::from_float(f)]);
        }
    }
    Ok(vec![TValue::nil()])
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
    } else {
        format!("{:?}", val)
    }
}
