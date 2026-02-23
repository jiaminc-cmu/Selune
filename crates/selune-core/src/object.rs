//! GC object types and type name helpers.

use crate::gc::*;
use crate::string::StringInterner;
use crate::value::TValue;

/// The type of a GC-managed object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GcObjectType {
    Table,
    LuaClosure,
    NativeFunction,
    UpVal,
    BoxedInt,
    String,
    Userdata,
}

impl GcObjectType {
    /// Convert from sub-tag value to enum.
    pub fn from_sub_tag(tag: u64) -> Option<Self> {
        match tag {
            GC_SUB_TABLE => Some(GcObjectType::Table),
            GC_SUB_CLOSURE => Some(GcObjectType::LuaClosure),
            GC_SUB_NATIVE => Some(GcObjectType::NativeFunction),
            GC_SUB_UPVAL => Some(GcObjectType::UpVal),
            GC_SUB_BOXED_INT => Some(GcObjectType::BoxedInt),
            GC_SUB_STRING => Some(GcObjectType::String),
            GC_SUB_USERDATA => Some(GcObjectType::Userdata),
            _ => None,
        }
    }
}

/// Get the Lua type name for a TValue.
pub fn lua_type_name(val: TValue, _heap: &GcHeap) -> &'static str {
    if val.is_nil() {
        "nil"
    } else if val.is_bool() {
        "boolean"
    } else if val.is_integer() || val.is_float() {
        "number"
    } else if val.is_gc() {
        match val.gc_sub_tag() {
            Some(GC_SUB_TABLE) => "table",
            Some(GC_SUB_CLOSURE) | Some(GC_SUB_NATIVE) => "function",
            Some(GC_SUB_STRING) => "string",
            Some(GC_SUB_BOXED_INT) => "number",
            Some(GC_SUB_USERDATA) => "userdata",
            _ => "unknown",
        }
    } else if val.is_light_userdata() {
        "userdata"
    } else {
        "unknown"
    }
}

/// Get the type name for a TValue, checking `__name` metafield on tables/userdata.
/// This matches Lua 5.4's `luaT_objtypename` behavior.
/// Uses immutable `&StringInterner` — only works if `"__name"` has already been interned.
pub fn obj_type_name(val: TValue, gc: &GcHeap, strings: &StringInterner) -> String {
    let mt_idx = if let Some(tidx) = val.as_table_idx() {
        gc.get_table(tidx).metatable
    } else if let Some(uidx) = val.as_userdata_idx() {
        gc.get_userdata(uidx).metatable
    } else {
        None
    };

    if let Some(mt_idx) = mt_idx {
        if let Some(name_key) = strings.find(b"__name") {
            let name_val = gc.get_table(mt_idx).raw_get_str(name_key);
            if let Some(sid) = name_val.as_string_id() {
                return String::from_utf8_lossy(strings.get_bytes(sid)).into_owned();
            }
        }
    }

    lua_type_name(val, gc).to_string()
}
