//! Lua runtime error types.

use selune_core::string::StringInterner;
use selune_core::value::TValue;
use std::fmt;

/// A Lua runtime error.
#[derive(Clone, Debug)]
pub enum LuaError {
    /// General runtime error with message.
    Runtime(String),
    /// Stack overflow (too many nested calls).
    StackOverflow,
    /// Lua error() with an arbitrary TValue (string, number, table, etc.).
    LuaValue(TValue),
}

impl LuaError {
    /// Convert this error into a TValue suitable for pcall/xpcall results.
    pub fn to_tvalue(&self, strings: &mut StringInterner) -> TValue {
        match self {
            LuaError::Runtime(msg) => {
                let sid = strings.intern_or_create(msg.as_bytes());
                TValue::from_string_id(sid)
            }
            LuaError::StackOverflow => {
                let sid = strings.intern(b"stack overflow");
                TValue::from_string_id(sid)
            }
            LuaError::LuaValue(v) => *v,
        }
    }
}

impl fmt::Display for LuaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LuaError::Runtime(msg) => write!(f, "{msg}"),
            LuaError::StackOverflow => write!(f, "stack overflow"),
            LuaError::LuaValue(v) => write!(f, "{:?}", v),
        }
    }
}

impl std::error::Error for LuaError {}
