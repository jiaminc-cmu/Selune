//! GC heap with arena-based allocation and typed indices.

use crate::table::Table;
use crate::value::TValue;
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
}

/// Context passed to native functions.
pub struct NativeContext<'a> {
    pub args: &'a [TValue],
    pub gc: &'a mut GcHeap,
    pub strings: &'a mut crate::string::StringInterner,
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

/// GC state for incremental mark-sweep collection.
pub struct GcState {
    /// Mark bits for each arena (true = marked/reachable).
    pub table_marks: Vec<bool>,
    pub closure_marks: Vec<bool>,
    pub upval_marks: Vec<bool>,
    pub native_marks: Vec<bool>,
    pub boxed_int_marks: Vec<bool>,

    /// Gray list: objects marked but not yet traversed.
    pub gray_tables: Vec<u32>,
    pub gray_closures: Vec<u32>,
    pub gray_upvals: Vec<u32>,

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
}

impl GcState {
    pub fn new() -> Self {
        GcState {
            table_marks: Vec::new(),
            closure_marks: Vec::new(),
            upval_marks: Vec::new(),
            native_marks: Vec::new(),
            boxed_int_marks: Vec::new(),
            gray_tables: Vec::new(),
            gray_closures: Vec::new(),
            gray_upvals: Vec::new(),
            enabled: true,
            total_alloc: 0,
            threshold: 4096, // Initial threshold (bytes) before first GC
            pause: 200,
            step_mul: 200,
            debt: 0,
            estimate: 0,
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
        self.gray_tables.clear();
        self.gray_closures.clear();
        self.gray_upvals.clear();
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
    /// GC state for mark-sweep collection.
    pub gc_state: GcState,
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
            gc_state: GcState::new(),
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
        let native = NativeFunction { func, name };
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

    // ---- GC mark/sweep methods ----

    /// Prepare mark bits for a new GC cycle.
    pub fn gc_prepare_marks(&mut self) {
        self.gc_state.prepare_marks(
            self.tables.len(),
            self.closures.len(),
            self.upvals.len(),
            self.natives.len(),
            self.boxed_ints.len(),
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
                if idx < self.gc_state.native_marks.len() {
                    self.gc_state.native_marks[idx] = true;
                }
                // Natives are leaf objects (no children to traverse)
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
                // Mark metatable
                if let Some(mt_idx) = table.metatable {
                    let mt_i = mt_idx.0 as usize;
                    if mt_i < self.gc_state.table_marks.len()
                        && !self.gc_state.table_marks[mt_i]
                    {
                        self.gc_state.table_marks[mt_i] = true;
                        self.gc_state.gray_tables.push(mt_idx.0);
                    }
                }
                // Collect child values to mark (avoid borrowing self)
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
                    // Also mark GC keys
                    if let crate::table::TableKey::GcPtr(bits) = key {
                        children.push(TValue::from_raw_bits(*bits));
                    }
                }
                // Now mark children
                for child in children {
                    self.gc_mark_value(child);
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
                    if uv_i < self.gc_state.upval_marks.len()
                        && !self.gc_state.upval_marks[uv_i]
                    {
                        self.gc_state.upval_marks[uv_i] = true;
                        self.gc_state.gray_upvals.push(uv_idx.0);
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

    /// Sweep all arenas, freeing unmarked objects. Returns bytes freed (approximate).
    pub fn gc_sweep(&mut self) -> usize {
        let mut freed = 0;

        // Sweep tables
        for i in 0..self.tables.len() {
            if self.tables[i].is_some() {
                if i < self.gc_state.table_marks.len() && !self.gc_state.table_marks[i] {
                    self.tables[i] = None;
                    self.table_free.push(i as u32);
                    freed += 64; // approximate
                }
            }
        }

        // Sweep closures
        for i in 0..self.closures.len() {
            if self.closures[i].is_some() {
                if i < self.gc_state.closure_marks.len() && !self.gc_state.closure_marks[i] {
                    self.closures[i] = None;
                    self.closure_free.push(i as u32);
                    freed += 32;
                }
            }
        }

        // Sweep upvalues
        for i in 0..self.upvals.len() {
            if self.upvals[i].is_some() {
                if i < self.gc_state.upval_marks.len() && !self.gc_state.upval_marks[i] {
                    self.upvals[i] = None;
                    self.upval_free.push(i as u32);
                    freed += 16;
                }
            }
        }

        // Sweep natives
        for i in 0..self.natives.len() {
            if self.natives[i].is_some() {
                if i < self.gc_state.native_marks.len() && !self.gc_state.native_marks[i] {
                    self.natives[i] = None;
                    self.native_free.push(i as u32);
                    freed += 24;
                }
            }
        }

        // Sweep boxed ints
        for i in 0..self.boxed_ints.len() {
            if self.boxed_ints[i].is_some() {
                if i < self.gc_state.boxed_int_marks.len()
                    && !self.gc_state.boxed_int_marks[i]
                {
                    self.boxed_ints[i] = None;
                    self.boxed_int_free.push(i as u32);
                    freed += 16;
                }
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
        self.gc_state.threshold = (self.gc_state.estimate as u64
            * self.gc_state.pause as u64
            / 100) as usize;
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
