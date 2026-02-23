//! Metamethod infrastructure for Lua 5.4.

use selune_core::gc::GcHeap;
use selune_core::string::{StringId, StringInterner};
use selune_core::value::TValue;

/// Pre-interned metamethod name StringIds for fast lookup.
pub struct MetamethodNames {
    pub add: StringId,
    pub sub: StringId,
    pub mul: StringId,
    pub mod_: StringId,
    pub pow: StringId,
    pub div: StringId,
    pub idiv: StringId,
    pub band: StringId,
    pub bor: StringId,
    pub bxor: StringId,
    pub shl: StringId,
    pub shr: StringId,
    pub unm: StringId,
    pub bnot: StringId,
    pub eq: StringId,
    pub lt: StringId,
    pub le: StringId,
    pub index: StringId,
    pub newindex: StringId,
    pub call: StringId,
    pub len: StringId,
    pub concat: StringId,
    pub tostring: StringId,
    pub close: StringId,
}

impl MetamethodNames {
    pub fn init(strings: &mut StringInterner) -> Self {
        MetamethodNames {
            add: strings.intern(b"__add"),
            sub: strings.intern(b"__sub"),
            mul: strings.intern(b"__mul"),
            mod_: strings.intern(b"__mod"),
            pow: strings.intern(b"__pow"),
            div: strings.intern(b"__div"),
            idiv: strings.intern(b"__idiv"),
            band: strings.intern(b"__band"),
            bor: strings.intern(b"__bor"),
            bxor: strings.intern(b"__bxor"),
            shl: strings.intern(b"__shl"),
            shr: strings.intern(b"__shr"),
            unm: strings.intern(b"__unm"),
            bnot: strings.intern(b"__bnot"),
            eq: strings.intern(b"__eq"),
            lt: strings.intern(b"__lt"),
            le: strings.intern(b"__le"),
            index: strings.intern(b"__index"),
            newindex: strings.intern(b"__newindex"),
            call: strings.intern(b"__call"),
            len: strings.intern(b"__len"),
            concat: strings.intern(b"__concat"),
            tostring: strings.intern(b"__tostring"),
            close: strings.intern(b"__close"),
        }
    }

    /// Map compiler's op_to_mm index to a metamethod StringId.
    pub fn from_mm_index(&self, idx: u8) -> StringId {
        match idx {
            0 => self.add,
            1 => self.sub,
            2 => self.mul,
            3 => self.mod_,
            4 => self.pow,
            5 => self.div,
            6 => self.idiv,
            7 => self.band,
            8 => self.bor,
            9 => self.bxor,
            10 => self.shl,
            11 => self.shr,
            12 => self.concat,
            _ => self.add, // fallback
        }
    }
}

/// Look up a metamethod on a TValue. Returns Some(method_value) if found.
pub fn get_metamethod(val: TValue, mm_name: StringId, gc: &GcHeap) -> Option<TValue> {
    // Check tables
    if let Some(table_idx) = val.as_table_idx() {
        let mt_idx = gc.get_table(table_idx).metatable?;
        let mm_val = gc.get_table(mt_idx).raw_get_str(mm_name);
        if mm_val.is_nil() {
            return None;
        }
        return Some(mm_val);
    }
    // Check userdata
    if let Some(ud_idx) = val.as_userdata_idx() {
        let mt_idx = gc.get_userdata(ud_idx).metatable?;
        let mm_val = gc.get_table(mt_idx).raw_get_str(mm_name);
        if mm_val.is_nil() {
            return None;
        }
        return Some(mm_val);
    }
    // Check strings (shared string metatable)
    if val.is_string() {
        let mt_idx = gc.string_metatable?;
        let mm_val = gc.get_table(mt_idx).raw_get_str(mm_name);
        if mm_val.is_nil() {
            return None;
        }
        return Some(mm_val);
    }
    // Check numbers (inline int, float, or boxed int)
    if val.is_number() || val.gc_sub_tag() == Some(selune_core::gc::GC_SUB_BOXED_INT) {
        if let Some(mt_idx) = gc.number_metatable {
            let mm_val = gc.get_table(mt_idx).raw_get_str(mm_name);
            if !mm_val.is_nil() {
                return Some(mm_val);
            }
        }
        return None;
    }
    // Check booleans
    if val.is_bool() {
        if let Some(mt_idx) = gc.boolean_metatable {
            let mm_val = gc.get_table(mt_idx).raw_get_str(mm_name);
            if !mm_val.is_nil() {
                return Some(mm_val);
            }
        }
        return None;
    }
    // Check nil
    if val.is_nil() {
        if let Some(mt_idx) = gc.nil_metatable {
            let mm_val = gc.get_table(mt_idx).raw_get_str(mm_name);
            if !mm_val.is_nil() {
                return Some(mm_val);
            }
        }
        return None;
    }
    None
}
