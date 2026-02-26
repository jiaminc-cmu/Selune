//! GC heap with arena-based allocation and typed indices.

use crate::table::Table;
use crate::value::TValue;
use std::any::Any;
use std::marker::PhantomData;

/// A typed index into an arena in the GcHeap.
#[derive(Debug)]
pub struct GcIdx<T>(pub u32, pub PhantomData<T>);

impl<T> Clone for GcIdx<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for GcIdx<T> {}

impl<T> PartialEq for GcIdx<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<T> Eq for GcIdx<T> {}

impl<T> std::hash::Hash for GcIdx<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T> GcIdx<T> {
    pub fn index(self) -> u32 {
        self.0
    }
}

/// Sub-tags for GC objects (stored in bits 44-46 of payload).
pub const GC_SUB_TABLE: u64 = 0;
pub const GC_SUB_CLOSURE: u64 = 1;
pub const GC_SUB_NATIVE: u64 = 2;
pub const GC_SUB_UPVAL: u64 = 3;
pub const GC_SUB_BOXED_INT: u64 = 4;
pub const GC_SUB_STRING: u64 = 5;
pub const GC_SUB_USERDATA: u64 = 6;

/// Bits used for sub-tag within the 47-bit payload.
pub const GC_SUB_SHIFT: u64 = 44;
pub const GC_SUB_MASK: u64 = 0x7; // 3 bits
/// Mask for the index within the payload (lower 44 bits = up to 16M objects).
pub const GC_INDEX_MASK: u64 = (1u64 << 44) - 1;

/// A Lua closure (function + captured upvalues).
#[derive(Debug)]
pub struct LuaClosure {
    /// Index of the prototype in the VM's proto store.
    pub proto_idx: usize,
    /// Upvalue handles.
    pub upvalues: Vec<GcIdx<UpVal>>,
}

/// Error type for native functions.
#[derive(Debug)]
pub enum NativeError {
    /// A string error message (for internal errors).
    String(String),
    /// A Lua TValue error (for error() throwing arbitrary values).
    Value(TValue),
    /// An IO error with message and optional errno (for f:read/f:write style returns).
    /// These should NOT be raised as Lua errors; callers should convert to (nil, msg, errno).
    IoError(String, i32),
}

impl From<String> for NativeError {
    fn from(s: String) -> Self {
        NativeError::String(s)
    }
}

/// A native (Rust) function callable from Lua.
pub struct NativeFunction {
    /// The function pointer. Takes &mut Vm proxy args and returns results.
    /// We store it as a raw fn pointer; the Vm reference is passed separately.
    pub func: fn(&mut NativeContext) -> Result<Vec<TValue>, NativeError>,
    pub name: &'static str,
    /// Optional upvalue for closures (e.g., gmatch iterators).
    pub upvalue: TValue,
}

/// Context passed to native functions.
pub struct NativeContext<'a> {
    pub args: &'a [TValue],
    pub gc: &'a mut GcHeap,
    pub strings: &'a mut crate::string::StringInterner,
    /// Optional upvalue from the NativeFunction.
    pub upvalue: TValue,
}

/// An upvalue: either open (pointing to a stack slot) or closed (holding a value).
#[derive(Debug)]
pub struct UpVal {
    pub location: UpValLocation,
}

/// Where an upvalue's value lives.
#[derive(Debug)]
pub enum UpValLocation {
    /// Points to a stack index on the current thread's stack.
    Open(usize),
    /// Points to a stack index on a specific coroutine's saved stack.
    /// The usize is the stack index, the second usize is the coroutine ID.
    OpenInThread(usize, usize),
    /// Value has been captured (function returned).
    Closed(TValue),
}

/// A full userdata value: arbitrary Rust data with an optional metatable.
pub struct Userdata {
    /// The boxed payload (e.g., file handle, custom data).
    pub data: Box<dyn Any>,
    /// Optional metatable (for __gc, __index, __tostring, etc.).
    pub metatable: Option<GcIdx<Table>>,
    /// Optional "user values" (Lua values associated with the userdata).
    pub user_values: Vec<TValue>,
}

impl std::fmt::Debug for Userdata {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Userdata {{ data: <dyn Any>, metatable: {:?} }}",
            self.metatable
        )
    }
}

/// GC state for incremental mark-sweep collection.
pub struct GcState {
    /// Mark bits for each arena (true = marked/reachable).
    pub table_marks: Vec<bool>,
    pub closure_marks: Vec<bool>,
    pub upval_marks: Vec<bool>,
    pub native_marks: Vec<bool>,
    pub boxed_int_marks: Vec<bool>,
    pub userdata_marks: Vec<bool>,

    /// Gray list: objects marked but not yet traversed.
    pub gray_tables: Vec<u32>,
    pub gray_closures: Vec<u32>,
    pub gray_upvals: Vec<u32>,
    pub gray_userdata: Vec<u32>,

    /// Weak table flags (parallel to table_marks).
    pub table_weak_keys: Vec<bool>,
    pub table_weak_values: Vec<bool>,

    /// Finalization tracking (persists across GC cycles).
    pub table_finalized: Vec<bool>,
    pub userdata_finalized: Vec<bool>,
    /// Queue of objects needing __gc calls after sweep.
    pub finalization_queue: Vec<TValue>,

    /// GC control.
    pub enabled: bool,
    /// Total bytes allocated (approximate).
    pub total_alloc: usize,
    /// Allocation threshold before next collection.
    pub threshold: usize,
    /// Pause parameter (percentage: 200 = collect when alloc doubles).
    pub pause: u32,
    /// Step multiplier (how much work per allocation step).
    pub step_mul: u32,
    /// Bytes allocated since last GC step.
    pub debt: i64,
    /// Estimated live data after last sweep.
    pub estimate: usize,
    /// GC mode: 0 = incremental, 1 = generational.
    pub gc_mode: u8,
}

impl GcState {
    pub fn new() -> Self {
        GcState {
            table_marks: Vec::new(),
            closure_marks: Vec::new(),
            upval_marks: Vec::new(),
            native_marks: Vec::new(),
            boxed_int_marks: Vec::new(),
            userdata_marks: Vec::new(),
            table_weak_keys: Vec::new(),
            table_weak_values: Vec::new(),
            table_finalized: Vec::new(),
            userdata_finalized: Vec::new(),
            finalization_queue: Vec::new(),
            gray_tables: Vec::new(),
            gray_closures: Vec::new(),
            gray_upvals: Vec::new(),
            gray_userdata: Vec::new(),
            enabled: true,
            total_alloc: 0,
            threshold: 4096, // Initial threshold (bytes) before first GC
            pause: 200,
            step_mul: 200,
            debt: 0,
            estimate: 0,
            gc_mode: 0,
        }
    }

    /// Ensure mark vectors match arena sizes and clear all marks.
    pub fn prepare_marks(
        &mut self,
        tables: usize,
        closures: usize,
        upvals: usize,
        natives: usize,
        boxed_ints: usize,
        userdata: usize,
    ) {
        self.table_marks.clear();
        self.table_marks.resize(tables, false);
        self.closure_marks.clear();
        self.closure_marks.resize(closures, false);
        self.upval_marks.clear();
        self.upval_marks.resize(upvals, false);
        self.native_marks.clear();
        self.native_marks.resize(natives, false);
        self.boxed_int_marks.clear();
        self.boxed_int_marks.resize(boxed_ints, false);
        self.userdata_marks.clear();
        self.userdata_marks.resize(userdata, false);
        self.table_weak_keys.clear();
        self.table_weak_keys.resize(tables, false);
        self.table_weak_values.clear();
        self.table_weak_values.resize(tables, false);
        // Extend finalized tracking to cover new slots (don't clear — persists across cycles)
        self.table_finalized.resize(tables, false);
        self.userdata_finalized.resize(userdata, false);
        self.finalization_queue.clear();
        self.gray_tables.clear();
        self.gray_closures.clear();
        self.gray_upvals.clear();
        self.gray_userdata.clear();
    }
}

impl Default for GcState {
    fn default() -> Self {
        Self::new()
    }
}

/// Arena-based GC heap.
pub struct GcHeap {
    pub boxed_ints: Vec<Option<i64>>,
    boxed_int_free: Vec<u32>,
    pub tables: Vec<Option<Table>>,
    table_free: Vec<u32>,
    pub closures: Vec<Option<LuaClosure>>,
    closure_free: Vec<u32>,
    pub natives: Vec<Option<NativeFunction>>,
    native_free: Vec<u32>,
    pub upvals: Vec<Option<UpVal>>,
    upval_free: Vec<u32>,
    pub userdata: Vec<Option<Userdata>>,
    userdata_free: Vec<u32>,
    /// GC state for mark-sweep collection.
    pub gc_state: GcState,
    /// Shared string metatable (for string:method() calls and getmetatable("")).
    pub string_metatable: Option<GcIdx<Table>>,
    /// Shared number metatable (for type-wide metamethods on numbers).
    pub number_metatable: Option<GcIdx<Table>>,
    /// Shared boolean metatable (for type-wide metamethods on booleans).
    pub boolean_metatable: Option<GcIdx<Table>>,
    /// Shared nil metatable (for type-wide metamethods on nil).
    pub nil_metatable: Option<GcIdx<Table>>,
    /// Shared thread metatable (for coroutine handles — makes type() return "thread").
    pub thread_metatable: Option<GcIdx<Table>>,
}

impl GcHeap {
    pub fn new() -> Self {
        GcHeap {
            boxed_ints: Vec::new(),
            boxed_int_free: Vec::new(),
            tables: Vec::new(),
            table_free: Vec::new(),
            closures: Vec::new(),
            closure_free: Vec::new(),
            natives: Vec::new(),
            native_free: Vec::new(),
            upvals: Vec::new(),
            upval_free: Vec::new(),
            userdata: Vec::new(),
            userdata_free: Vec::new(),
            gc_state: GcState::new(),
            string_metatable: None,
            number_metatable: None,
            boolean_metatable: None,
            nil_metatable: None,
            thread_metatable: None,
        }
    }

    pub fn alloc_boxed_int(&mut self, val: i64) -> GcIdx<i64> {
        self.gc_state.total_alloc += 16; // ~8 bytes value + overhead
        self.gc_state.debt += 16;
        if let Some(idx) = self.boxed_int_free.pop() {
            self.boxed_ints[idx as usize] = Some(val);
            GcIdx(idx, PhantomData)
        } else {
            let idx = self.boxed_ints.len() as u32;
            self.boxed_ints.push(Some(val));
            GcIdx(idx, PhantomData)
        }
    }

    pub fn get_boxed_int(&self, idx: GcIdx<i64>) -> i64 {
        self.boxed_ints[idx.0 as usize].expect("boxed int was freed")
    }

    pub fn alloc_table(&mut self, array_hint: usize, hash_hint: usize) -> GcIdx<Table> {
        let size_est = 64 + array_hint * 8 + hash_hint * 24; // rough estimate
        self.gc_state.total_alloc += size_est;
        self.gc_state.debt += size_est as i64;
        let table = Table::new(array_hint, hash_hint);
        if let Some(idx) = self.table_free.pop() {
            self.tables[idx as usize] = Some(table);
            GcIdx(idx, PhantomData)
        } else {
            let idx = self.tables.len() as u32;
            self.tables.push(Some(table));
            GcIdx(idx, PhantomData)
        }
    }

    /// Raw get from a table, handling boxed integer keys correctly.
    /// This resolves boxed ints to their i64 value before lookup.
    pub fn table_raw_get(&self, table_idx: GcIdx<Table>, key: TValue) -> TValue {
        // Check if the key is a boxed integer
        if key.gc_sub_tag() == Some(GC_SUB_BOXED_INT) {
            if let Some(gc_idx) = key.gc_index() {
                let int_val = self.boxed_ints[gc_idx as usize].expect("boxed int was freed");
                return self.get_table(table_idx).raw_geti(int_val);
            }
        }
        self.get_table(table_idx).raw_get(key)
    }

    /// Raw set on a table, handling boxed integer keys correctly.
    pub fn table_raw_set(
        &mut self,
        table_idx: GcIdx<Table>,
        key: TValue,
        value: TValue,
    ) -> Result<(), &'static str> {
        // Check if the key is a boxed integer
        if key.gc_sub_tag() == Some(GC_SUB_BOXED_INT) {
            if let Some(gc_idx) = key.gc_index() {
                let int_val = self.boxed_ints[gc_idx as usize].expect("boxed int was freed");
                self.get_table_mut(table_idx).raw_seti(int_val, value);
                return Ok(());
            }
        }
        self.get_table_mut(table_idx).raw_set(key, value)
    }

    pub fn get_table(&self, idx: GcIdx<Table>) -> &Table {
        self.tables[idx.0 as usize]
            .as_ref()
            .expect("table was freed")
    }

    pub fn get_table_mut(&mut self, idx: GcIdx<Table>) -> &mut Table {
        self.tables[idx.0 as usize]
            .as_mut()
            .expect("table was freed")
    }

    /// Unchecked table access for JIT hot paths where the index is known valid.
    ///
    /// # Safety
    /// `idx` must be a valid, live table index.
    #[inline(always)]
    pub unsafe fn get_table_unchecked(&self, idx: GcIdx<Table>) -> &Table {
        self.tables
            .get_unchecked(idx.0 as usize)
            .as_ref()
            .unwrap_unchecked()
    }

    /// Unchecked mutable table access for JIT hot paths.
    ///
    /// # Safety
    /// `idx` must be a valid, live table index.
    #[inline(always)]
    pub unsafe fn get_table_mut_unchecked(&mut self, idx: GcIdx<Table>) -> &mut Table {
        self.tables
            .get_unchecked_mut(idx.0 as usize)
            .as_mut()
            .unwrap_unchecked()
    }

    pub fn alloc_closure(
        &mut self,
        proto_idx: usize,
        upvalues: Vec<GcIdx<UpVal>>,
    ) -> GcIdx<LuaClosure> {
        let size_est = 32 + upvalues.len() * 4;
        self.gc_state.total_alloc += size_est;
        self.gc_state.debt += size_est as i64;
        let closure = LuaClosure {
            proto_idx,
            upvalues,
        };
        if let Some(idx) = self.closure_free.pop() {
            self.closures[idx as usize] = Some(closure);
            GcIdx(idx, PhantomData)
        } else {
            let idx = self.closures.len() as u32;
            self.closures.push(Some(closure));
            GcIdx(idx, PhantomData)
        }
    }

    pub fn get_closure(&self, idx: GcIdx<LuaClosure>) -> &LuaClosure {
        self.closures[idx.0 as usize]
            .as_ref()
            .expect("closure was freed")
    }

    pub fn alloc_native(
        &mut self,
        func: fn(&mut NativeContext) -> Result<Vec<TValue>, NativeError>,
        name: &'static str,
    ) -> GcIdx<NativeFunction> {
        self.gc_state.total_alloc += 24;
        self.gc_state.debt += 24;
        let native = NativeFunction {
            func,
            name,
            upvalue: TValue::nil(),
        };
        if let Some(idx) = self.native_free.pop() {
            self.natives[idx as usize] = Some(native);
            GcIdx(idx, PhantomData)
        } else {
            let idx = self.natives.len() as u32;
            self.natives.push(Some(native));
            GcIdx(idx, PhantomData)
        }
    }

    pub fn alloc_native_with_upvalue(
        &mut self,
        func: fn(&mut NativeContext) -> Result<Vec<TValue>, NativeError>,
        name: &'static str,
        upvalue: TValue,
    ) -> GcIdx<NativeFunction> {
        self.gc_state.total_alloc += 32;
        self.gc_state.debt += 32;
        let native = NativeFunction {
            func,
            name,
            upvalue,
        };
        if let Some(idx) = self.native_free.pop() {
            self.natives[idx as usize] = Some(native);
            GcIdx(idx, PhantomData)
        } else {
            let idx = self.natives.len() as u32;
            self.natives.push(Some(native));
            GcIdx(idx, PhantomData)
        }
    }

    pub fn get_native(&self, idx: GcIdx<NativeFunction>) -> &NativeFunction {
        self.natives[idx.0 as usize]
            .as_ref()
            .expect("native fn was freed")
    }

    pub fn alloc_upval(&mut self, location: UpValLocation) -> GcIdx<UpVal> {
        self.gc_state.total_alloc += 16;
        self.gc_state.debt += 16;
        let upval = UpVal { location };
        if let Some(idx) = self.upval_free.pop() {
            self.upvals[idx as usize] = Some(upval);
            GcIdx(idx, PhantomData)
        } else {
            let idx = self.upvals.len() as u32;
            self.upvals.push(Some(upval));
            GcIdx(idx, PhantomData)
        }
    }

    pub fn get_upval(&self, idx: GcIdx<UpVal>) -> &UpVal {
        self.upvals[idx.0 as usize]
            .as_ref()
            .expect("upval was freed")
    }

    pub fn get_upval_mut(&mut self, idx: GcIdx<UpVal>) -> &mut UpVal {
        self.upvals[idx.0 as usize]
            .as_mut()
            .expect("upval was freed")
    }

    pub fn alloc_userdata(
        &mut self,
        data: Box<dyn Any>,
        metatable: Option<GcIdx<Table>>,
    ) -> GcIdx<Userdata> {
        self.gc_state.total_alloc += 64; // rough estimate
        self.gc_state.debt += 64;
        let ud = Userdata {
            data,
            metatable,
            user_values: Vec::new(),
        };
        if let Some(idx) = self.userdata_free.pop() {
            self.userdata[idx as usize] = Some(ud);
            GcIdx(idx, PhantomData)
        } else {
            let idx = self.userdata.len() as u32;
            self.userdata.push(Some(ud));
            GcIdx(idx, PhantomData)
        }
    }

    pub fn get_userdata(&self, idx: GcIdx<Userdata>) -> &Userdata {
        self.userdata[idx.0 as usize]
            .as_ref()
            .expect("userdata was freed")
    }

    pub fn get_userdata_mut(&mut self, idx: GcIdx<Userdata>) -> &mut Userdata {
        self.userdata[idx.0 as usize]
            .as_mut()
            .expect("userdata was freed")
    }

    // ---- GC mark/sweep methods ----

    /// Prepare mark bits for a new GC cycle.
    pub fn gc_prepare_marks(&mut self) {
        self.gc_state.prepare_marks(
            self.tables.len(),
            self.closures.len(),
            self.upvals.len(),
            self.natives.len(),
            self.boxed_ints.len(),
            self.userdata.len(),
        );
    }

    /// Mark a TValue as reachable. For non-leaf GC objects, adds to gray list.
    pub fn gc_mark_value(&mut self, val: TValue) {
        if !val.is_gc() {
            return;
        }
        let sub = match val.gc_sub_tag() {
            Some(s) => s,
            None => return,
        };
        let idx = match val.gc_index() {
            Some(i) => i as usize,
            None => return,
        };
        match sub {
            GC_SUB_TABLE => {
                if idx < self.gc_state.table_marks.len() && !self.gc_state.table_marks[idx] {
                    self.gc_state.table_marks[idx] = true;
                    self.gc_state.gray_tables.push(idx as u32);
                }
            }
            GC_SUB_CLOSURE => {
                if idx < self.gc_state.closure_marks.len() && !self.gc_state.closure_marks[idx] {
                    self.gc_state.closure_marks[idx] = true;
                    self.gc_state.gray_closures.push(idx as u32);
                }
            }
            GC_SUB_NATIVE => {
                if idx < self.gc_state.native_marks.len() && !self.gc_state.native_marks[idx] {
                    self.gc_state.native_marks[idx] = true;
                    // Trace the native's upvalue if it references a GC object
                    let upval = self.natives[idx]
                        .as_ref()
                        .map(|n| n.upvalue)
                        .unwrap_or(TValue::nil());
                    if upval.is_gc() {
                        self.gc_mark_value(upval);
                    }
                }
            }
            GC_SUB_UPVAL => {
                if idx < self.gc_state.upval_marks.len() && !self.gc_state.upval_marks[idx] {
                    self.gc_state.upval_marks[idx] = true;
                    self.gc_state.gray_upvals.push(idx as u32);
                }
            }
            GC_SUB_BOXED_INT => {
                if idx < self.gc_state.boxed_int_marks.len() {
                    self.gc_state.boxed_int_marks[idx] = true;
                }
                // Boxed ints are leaf objects
            }
            GC_SUB_USERDATA => {
                if idx < self.gc_state.userdata_marks.len() && !self.gc_state.userdata_marks[idx] {
                    self.gc_state.userdata_marks[idx] = true;
                    self.gc_state.gray_userdata.push(idx as u32);
                }
            }
            GC_SUB_STRING => {
                // Strings are managed by StringInterner, not by GC arenas
            }
            _ => {}
        }
    }

    /// Propagate: traverse gray objects, marking their children.
    /// Returns the number of objects propagated.
    pub fn gc_propagate(&mut self) -> usize {
        let mut work = 0;

        // Propagate gray tables
        while let Some(idx) = self.gc_state.gray_tables.pop() {
            let i = idx as usize;
            if let Some(table) = &self.tables[i] {
                let weak_k =
                    i < self.gc_state.table_weak_keys.len() && self.gc_state.table_weak_keys[i];
                let weak_v =
                    i < self.gc_state.table_weak_values.len() && self.gc_state.table_weak_values[i];

                // Mark metatable (always, even for weak tables)
                if let Some(mt_idx) = table.metatable {
                    let mt_i = mt_idx.0 as usize;
                    if mt_i < self.gc_state.table_marks.len() && !self.gc_state.table_marks[mt_i] {
                        self.gc_state.table_marks[mt_i] = true;
                        self.gc_state.gray_tables.push(mt_idx.0);
                    }
                }

                if weak_k && weak_v {
                    // Both keys and values are weak: don't mark anything
                    // (entries will be cleared if either key or value is dead)
                } else if weak_v && !weak_k {
                    // Weak values only: mark keys but not values
                    let mut children = Vec::new();
                    for (key, _v) in table.hash_entries() {
                        if let crate::table::TableKey::GcPtr(bits) = key {
                            children.push(TValue::from_raw_bits(*bits));
                        }
                    }
                    for child in children {
                        self.gc_mark_value(child);
                    }
                } else if weak_k && !weak_v {
                    // Weak keys (ephemeron): mark values only if key is already marked
                    // Values whose keys are not yet marked are deferred (handled by ephemeron loop)
                    let mut children = Vec::new();
                    for &v in table.array_values() {
                        // Array entries have integer keys (always "marked")
                        if v.is_gc() {
                            children.push(v);
                        }
                    }
                    for (key, &v) in table.hash_entries() {
                        if v.is_nil() {
                            continue;
                        }
                        let key_is_marked = match key {
                            crate::table::TableKey::GcPtr(bits) => {
                                let kv = TValue::from_raw_bits(*bits);
                                self.is_gc_marked(kv)
                            }
                            _ => true, // non-GC keys are always "alive"
                        };
                        if key_is_marked && v.is_gc() {
                            children.push(v);
                        }
                    }
                    for child in children {
                        self.gc_mark_value(child);
                    }
                } else {
                    // Strong table: mark everything
                    let mut children = Vec::new();
                    for &v in table.array_values() {
                        if v.is_gc() {
                            children.push(v);
                        }
                    }
                    for (key, &v) in table.hash_entries() {
                        if v.is_gc() {
                            children.push(v);
                        }
                        if let crate::table::TableKey::GcPtr(bits) = key {
                            children.push(TValue::from_raw_bits(*bits));
                        }
                    }
                    for child in children {
                        self.gc_mark_value(child);
                    }
                }
            }
            work += 1;
        }

        // Propagate gray closures
        while let Some(idx) = self.gc_state.gray_closures.pop() {
            let i = idx as usize;
            if let Some(closure) = &self.closures[i] {
                let upval_indices: Vec<GcIdx<UpVal>> = closure.upvalues.clone();
                for uv_idx in upval_indices {
                    let uv_i = uv_idx.0 as usize;
                    if uv_i < self.gc_state.upval_marks.len() && !self.gc_state.upval_marks[uv_i] {
                        self.gc_state.upval_marks[uv_i] = true;
                        self.gc_state.gray_upvals.push(uv_idx.0);
                    }
                }
            }
            work += 1;
        }

        // Propagate gray userdata
        while let Some(idx) = self.gc_state.gray_userdata.pop() {
            let i = idx as usize;
            if let Some(ud) = &self.userdata[i] {
                // Mark metatable
                if let Some(mt_idx) = ud.metatable {
                    let mt_i = mt_idx.0 as usize;
                    if mt_i < self.gc_state.table_marks.len() && !self.gc_state.table_marks[mt_i] {
                        self.gc_state.table_marks[mt_i] = true;
                        self.gc_state.gray_tables.push(mt_idx.0);
                    }
                }
                // Mark user values
                let user_vals: Vec<TValue> = ud.user_values.clone();
                for v in user_vals {
                    if v.is_gc() {
                        self.gc_mark_value(v);
                    }
                }
            }
            work += 1;
        }

        // Propagate gray upvalues
        while let Some(idx) = self.gc_state.gray_upvals.pop() {
            let i = idx as usize;
            if let Some(upval) = &self.upvals[i] {
                match &upval.location {
                    UpValLocation::Closed(val) => {
                        let v = *val;
                        self.gc_mark_value(v);
                    }
                    UpValLocation::Open(_) | UpValLocation::OpenInThread(_, _) => {
                        // Open upvalues point to stack slots; the stack is a root
                    }
                }
            }
            work += 1;
        }

        work
    }

    /// Check if a GC value is currently marked.
    pub fn is_gc_marked(&self, val: TValue) -> bool {
        if !val.is_gc() {
            return true; // non-GC values are always "alive"
        }
        let sub = match val.gc_sub_tag() {
            Some(s) => s,
            None => return true,
        };
        let idx = match val.gc_index() {
            Some(i) => i as usize,
            None => return true,
        };
        match sub {
            GC_SUB_TABLE => idx < self.gc_state.table_marks.len() && self.gc_state.table_marks[idx],
            GC_SUB_CLOSURE => {
                idx < self.gc_state.closure_marks.len() && self.gc_state.closure_marks[idx]
            }
            GC_SUB_NATIVE => {
                idx < self.gc_state.native_marks.len() && self.gc_state.native_marks[idx]
            }
            GC_SUB_UPVAL => idx < self.gc_state.upval_marks.len() && self.gc_state.upval_marks[idx],
            GC_SUB_BOXED_INT => {
                idx < self.gc_state.boxed_int_marks.len() && self.gc_state.boxed_int_marks[idx]
            }
            GC_SUB_USERDATA => {
                idx < self.gc_state.userdata_marks.len() && self.gc_state.userdata_marks[idx]
            }
            GC_SUB_STRING => true, // strings are never collected by GC
            _ => true,
        }
    }

    /// Check if a TValue is a collectable GC object that is unmarked (dead).
    /// Returns false for non-GC values and strings (strings are interned, not collected).
    pub fn is_collectable_dead(&self, val: TValue) -> bool {
        if !val.is_gc() {
            return false;
        }
        let sub = match val.gc_sub_tag() {
            Some(s) => s,
            None => return false,
        };
        let idx = match val.gc_index() {
            Some(i) => i as usize,
            None => return false,
        };
        match sub {
            GC_SUB_TABLE => {
                idx < self.gc_state.table_marks.len() && !self.gc_state.table_marks[idx]
            }
            GC_SUB_CLOSURE => {
                idx < self.gc_state.closure_marks.len() && !self.gc_state.closure_marks[idx]
            }
            GC_SUB_NATIVE => {
                idx < self.gc_state.native_marks.len() && !self.gc_state.native_marks[idx]
            }
            GC_SUB_UPVAL => {
                idx < self.gc_state.upval_marks.len() && !self.gc_state.upval_marks[idx]
            }
            GC_SUB_BOXED_INT => {
                idx < self.gc_state.boxed_int_marks.len() && !self.gc_state.boxed_int_marks[idx]
            }
            GC_SUB_USERDATA => {
                idx < self.gc_state.userdata_marks.len() && !self.gc_state.userdata_marks[idx]
            }
            GC_SUB_STRING => false, // strings are never dead
            _ => false,
        }
    }

    /// Propagate ephemerons: for weak-key tables, mark values whose keys are now marked.
    /// Returns true if any new marks were made.
    pub fn gc_propagate_ephemerons(&mut self) -> bool {
        let mut changed = false;
        for i in 0..self.tables.len() {
            if self.tables[i].is_none() {
                continue;
            }
            if i >= self.gc_state.table_marks.len() || !self.gc_state.table_marks[i] {
                continue;
            }
            let weak_k =
                i < self.gc_state.table_weak_keys.len() && self.gc_state.table_weak_keys[i];
            let weak_v =
                i < self.gc_state.table_weak_values.len() && self.gc_state.table_weak_values[i];
            if !weak_k || weak_v {
                continue;
            } // only ephemerons (weak keys, strong values)

            let table = self.tables[i].as_ref().unwrap();
            let mut children = Vec::new();
            for (key, &v) in table.hash_entries() {
                if v.is_nil() {
                    continue;
                }
                let key_is_marked = match key {
                    crate::table::TableKey::GcPtr(bits) => {
                        let kv = TValue::from_raw_bits(*bits);
                        self.is_gc_marked(kv)
                    }
                    _ => true,
                };
                if key_is_marked && v.is_gc() && !self.is_gc_marked(v) {
                    children.push(v);
                }
            }
            for child in children {
                self.gc_mark_value(child);
                changed = true;
            }
        }
        changed
    }

    /// Clear dead entries from weak tables after propagation is complete.
    pub fn gc_clear_weak_tables(&mut self) {
        for i in 0..self.tables.len() {
            if self.tables[i].is_none() {
                continue;
            }
            if i >= self.gc_state.table_marks.len() || !self.gc_state.table_marks[i] {
                continue;
            }
            let weak_k =
                i < self.gc_state.table_weak_keys.len() && self.gc_state.table_weak_keys[i];
            let weak_v =
                i < self.gc_state.table_weak_values.len() && self.gc_state.table_weak_values[i];
            if !weak_k && !weak_v {
                continue;
            }

            // Need to collect dead status before mutating
            let table = self.tables[i].as_ref().unwrap();
            let mut dead_array_indices = Vec::new();
            let mut dead_hash_keys = Vec::new();

            if weak_v {
                for (j, &v) in table.array_values().iter().enumerate() {
                    if !v.is_nil() && self.is_collectable_dead(v) {
                        dead_array_indices.push(j);
                    }
                }
            }

            for (key, &v) in table.hash_entries() {
                let key_dead = weak_k
                    && match key {
                        crate::table::TableKey::GcPtr(bits) => {
                            self.is_collectable_dead(TValue::from_raw_bits(*bits))
                        }
                        _ => false,
                    };
                let val_dead = weak_v && !v.is_nil() && self.is_collectable_dead(v);
                if key_dead || val_dead {
                    dead_hash_keys.push(*key);
                }
            }

            // Now mutate
            if !dead_array_indices.is_empty() || !dead_hash_keys.is_empty() {
                let table = self.tables[i].as_mut().unwrap();
                for j in dead_array_indices {
                    table.array_values_mut()[j] = TValue::nil();
                }
                for k in dead_hash_keys {
                    table.remove_hash_entry(&k);
                }
                // Trim trailing nils from array
                table.trim_array();
            }
        }
    }

    /// Sweep all arenas, freeing unmarked objects. Returns bytes freed (approximate).
    pub fn gc_sweep(&mut self) -> usize {
        let mut freed = 0;

        // Sweep tables
        for i in 0..self.tables.len() {
            if self.tables[i].is_some()
                && i < self.gc_state.table_marks.len()
                && !self.gc_state.table_marks[i]
            {
                self.tables[i] = None;
                self.table_free.push(i as u32);
                freed += 64; // approximate
            }
        }

        // Sweep closures
        for i in 0..self.closures.len() {
            if self.closures[i].is_some()
                && i < self.gc_state.closure_marks.len()
                && !self.gc_state.closure_marks[i]
            {
                self.closures[i] = None;
                self.closure_free.push(i as u32);
                freed += 32;
            }
        }

        // Sweep upvalues
        for i in 0..self.upvals.len() {
            if self.upvals[i].is_some()
                && i < self.gc_state.upval_marks.len()
                && !self.gc_state.upval_marks[i]
            {
                self.upvals[i] = None;
                self.upval_free.push(i as u32);
                freed += 16;
            }
        }

        // Sweep natives
        for i in 0..self.natives.len() {
            if self.natives[i].is_some()
                && i < self.gc_state.native_marks.len()
                && !self.gc_state.native_marks[i]
            {
                self.natives[i] = None;
                self.native_free.push(i as u32);
                freed += 24;
            }
        }

        // Sweep userdata
        for i in 0..self.userdata.len() {
            if self.userdata[i].is_some()
                && i < self.gc_state.userdata_marks.len()
                && !self.gc_state.userdata_marks[i]
            {
                self.userdata[i] = None;
                self.userdata_free.push(i as u32);
                freed += 64;
            }
        }

        // Sweep boxed ints
        for i in 0..self.boxed_ints.len() {
            if self.boxed_ints[i].is_some()
                && i < self.gc_state.boxed_int_marks.len()
                && !self.gc_state.boxed_int_marks[i]
            {
                self.boxed_ints[i] = None;
                self.boxed_int_free.push(i as u32);
                freed += 16;
            }
        }

        if self.gc_state.total_alloc >= freed {
            self.gc_state.total_alloc -= freed;
        } else {
            self.gc_state.total_alloc = 0;
        }
        self.gc_state.estimate = self.gc_state.total_alloc;
        self.gc_state.debt = 0;
        // Set next threshold based on pause
        self.gc_state.threshold =
            (self.gc_state.estimate as u64 * self.gc_state.pause as u64 / 100) as usize;
        if self.gc_state.threshold < 4096 {
            self.gc_state.threshold = 4096;
        }

        freed
    }

    /// Approximate memory usage in bytes.
    pub fn gc_memory_bytes(&self) -> usize {
        self.gc_state.total_alloc
    }

    /// Approximate memory usage in kilobytes (for collectgarbage("count")).
    pub fn gc_memory_kb(&self) -> f64 {
        self.gc_state.total_alloc as f64 / 1024.0
    }

    /// Check if GC should run based on allocation debt.
    pub fn gc_should_step(&self) -> bool {
        self.gc_state.enabled && self.gc_state.total_alloc > self.gc_state.threshold
    }
}

impl Default for GcHeap {
    fn default() -> Self {
        Self::new()
    }
}
