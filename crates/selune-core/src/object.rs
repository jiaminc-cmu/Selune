//! GC object types and type name helpers.

use crate::gc::*;
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
            _ => "userdata",
        }
    } else if val.is_light_userdata() {
        "userdata"
    } else {
        "unknown"
    }
}
