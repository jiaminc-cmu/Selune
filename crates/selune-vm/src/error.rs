//! Lua runtime error types.

use std::fmt;

/// A Lua runtime error.
#[derive(Clone, Debug)]
pub enum LuaError {
    /// General runtime error with message.
    Runtime(String),
    /// Stack overflow (too many nested calls).
    StackOverflow,
}

impl fmt::Display for LuaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LuaError::Runtime(msg) => write!(f, "{msg}"),
            LuaError::StackOverflow => write!(f, "stack overflow"),
        }
    }
}

impl std::error::Error for LuaError {}
