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

/// A native (Rust) function callable from Lua.
pub struct NativeFunction {
    /// The function pointer. Takes &mut Vm proxy args and returns results.
    /// We store it as a raw fn pointer; the Vm reference is passed separately.
    pub func: fn(&mut NativeContext) -> Result<Vec<TValue>, String>,
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
    /// Points to a stack index (still on the stack).
    Open(usize),
    /// Value has been captured (function returned).
    Closed(TValue),
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
        }
    }

    pub fn alloc_boxed_int(&mut self, val: i64) -> GcIdx<i64> {
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
        self.tables[idx.0 as usize].as_ref().expect("table was freed")
    }

    pub fn get_table_mut(&mut self, idx: GcIdx<Table>) -> &mut Table {
        self.tables[idx.0 as usize].as_mut().expect("table was freed")
    }

    pub fn alloc_closure(&mut self, proto_idx: usize, upvalues: Vec<GcIdx<UpVal>>) -> GcIdx<LuaClosure> {
        let closure = LuaClosure { proto_idx, upvalues };
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
        self.closures[idx.0 as usize].as_ref().expect("closure was freed")
    }

    pub fn alloc_native(
        &mut self,
        func: fn(&mut NativeContext) -> Result<Vec<TValue>, String>,
        name: &'static str,
    ) -> GcIdx<NativeFunction> {
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
        self.natives[idx.0 as usize].as_ref().expect("native fn was freed")
    }

    pub fn alloc_upval(&mut self, location: UpValLocation) -> GcIdx<UpVal> {
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
        self.upvals[idx.0 as usize].as_ref().expect("upval was freed")
    }

    pub fn get_upval_mut(&mut self, idx: GcIdx<UpVal>) -> &mut UpVal {
        self.upvals[idx.0 as usize].as_mut().expect("upval was freed")
    }
}

impl Default for GcHeap {
    fn default() -> Self {
        Self::new()
    }
}
