//! Call frame information for the VM.

use selune_core::gc::{GcIdx, LuaClosure};

/// Status of a call frame (used for yield across pcall/xpcall).
#[derive(Clone, Debug, PartialEq)]
pub enum CallStatus {
    /// Normal execution.
    Normal,
    /// Yielded through pcall — on resume, wrap inner results with (true, ...) and
    /// place at the saved result_base with saved num_results.
    PcallYield {
        result_base: usize,
        num_results: i32,
    },
    /// Yielded through xpcall — same as PcallYield.
    XpcallYield {
        result_base: usize,
        num_results: i32,
    },
}

/// A call frame on the VM call stack.
#[derive(Clone, Debug)]
pub struct CallInfo {
    /// Stack base for registers in this frame.
    pub base: usize,
    /// Program counter (index into proto.code).
    pub pc: usize,
    /// Expected number of results (-1 = multi-return).
    pub num_results: i32,
    /// Index into the proto list (for Lua calls).
    pub proto_idx: usize,
    /// Whether this is a Lua call (vs native).
    pub is_lua: bool,
    /// The closure being executed (if Lua call).
    pub closure_idx: Option<GcIdx<LuaClosure>>,
    /// Stack position where the function value lives (for result placement).
    pub func_stack_idx: usize,
    /// Base of vararg storage (if vararg function).
    pub vararg_base: Option<usize>,
    /// Counter for tail calls to detect infinite tail recursion.
    pub tail_count: u32,
    /// Stack indices of to-be-closed variables in this frame.
    pub tbc_slots: Vec<usize>,
    /// Call status for yield across pcall/xpcall boundaries.
    pub call_status: CallStatus,
}

impl CallInfo {
    pub fn new(base: usize, proto_idx: usize) -> Self {
        CallInfo {
            base,
            pc: 0,
            num_results: -1,
            proto_idx,
            is_lua: true,
            closure_idx: None,
            func_stack_idx: 0,
            vararg_base: None,
            tail_count: 0,
            tbc_slots: Vec::new(),
            call_status: CallStatus::Normal,
        }
    }
}
