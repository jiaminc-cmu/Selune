//! Call frame information for the VM.

use selune_core::gc::{GcIdx, LuaClosure};
use selune_core::value::TValue;

/// Lightweight call frame for JIT-to-JIT calls (~32 bytes).
/// Only contains the fields needed for the JIT fast path — avoids
/// initializing the 10+ fields in CallInfo that JIT doesn't need
/// (vararg_base, tbc_slots, call_status, tail_count, hooks, etc.).
#[derive(Clone, Debug)]
pub struct JitCallInfo {
    /// Stack base for registers in this frame.
    pub base: usize,
    /// Stack position where the function value lives (for result placement).
    pub func_stack_idx: usize,
    /// Index into vm.protos[].
    pub proto_idx: usize,
    /// Raw GcIdx value for the closure (avoids Option overhead).
    pub closure_idx_raw: u32,
    /// Expected number of results (-1 = multi-return).
    pub num_results: i32,
}

/// Data for CloseReturnYield status (boxed since it's rare).
#[derive(Clone, Debug, PartialEq)]
pub struct CloseReturnYieldData {
    /// The saved return values.
    pub saved_results: Vec<TValue>,
    /// Remaining TBC slots to close (indices in reverse order).
    pub remaining_tbc_slots: Vec<usize>,
}

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
    /// Yielded through xpcall — includes error handler.
    XpcallYield {
        result_base: usize,
        num_results: i32,
        handler: TValue,
    },
    /// Yielded during __close in a Return handler.
    /// On resume, after all __close calls complete, finish the return.
    CloseReturnYield(Box<CloseReturnYieldData>),
}

// Flags for CallInfo boolean fields
const FLAG_IS_LUA: u8 = 1;
const FLAG_IS_HOOK_CALL: u8 = 2;
const FLAG_IS_TAIL_CALL: u8 = 4;
const FLAG_IS_TBC_CLOSE: u8 = 8;

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
    /// The closure being executed (if Lua call).
    pub closure_idx: Option<GcIdx<LuaClosure>>,
    /// Stack position where the function value lives (for result placement).
    pub func_stack_idx: usize,
    /// Base of vararg storage (if vararg function).
    pub vararg_base: Option<usize>,
    /// Counter for tail calls to detect infinite tail recursion.
    pub tail_count: u32,
    /// Stack indices of to-be-closed variables in this frame (None = empty).
    pub tbc_slots: Option<Vec<usize>>,
    /// Call status for yield across pcall/xpcall boundaries.
    pub call_status: CallStatus,
    /// Packed boolean flags (is_lua, is_hook_call, is_tail_call, is_tbc_close).
    flags: u8,
    /// First transferred local (1-based) for call/return hook inspection.
    pub ftransfer: u16,
    /// Number of transferred values for call/return hook inspection.
    pub ntransfer: u16,
    /// Saved hook_last_line from caller frame (restored on return).
    pub saved_hook_line: i32,
}

impl CallInfo {
    pub fn new(base: usize, proto_idx: usize) -> Self {
        CallInfo {
            base,
            pc: 0,
            num_results: -1,
            proto_idx,
            closure_idx: None,
            func_stack_idx: 0,
            vararg_base: None,
            tail_count: 0,
            tbc_slots: None,
            call_status: CallStatus::Normal,
            flags: FLAG_IS_LUA, // is_lua = true by default
            ftransfer: 0,
            ntransfer: 0,
            saved_hook_line: -1,
        }
    }

    #[inline(always)]
    pub fn is_lua(&self) -> bool {
        self.flags & FLAG_IS_LUA != 0
    }

    #[inline(always)]
    pub fn set_is_lua(&mut self, v: bool) {
        if v {
            self.flags |= FLAG_IS_LUA;
        } else {
            self.flags &= !FLAG_IS_LUA;
        }
    }

    #[inline(always)]
    pub fn is_hook_call(&self) -> bool {
        self.flags & FLAG_IS_HOOK_CALL != 0
    }

    #[inline(always)]
    pub fn set_is_hook_call(&mut self, v: bool) {
        if v {
            self.flags |= FLAG_IS_HOOK_CALL;
        } else {
            self.flags &= !FLAG_IS_HOOK_CALL;
        }
    }

    #[inline(always)]
    pub fn is_tail_call(&self) -> bool {
        self.flags & FLAG_IS_TAIL_CALL != 0
    }

    #[inline(always)]
    pub fn set_is_tail_call(&mut self, v: bool) {
        if v {
            self.flags |= FLAG_IS_TAIL_CALL;
        } else {
            self.flags &= !FLAG_IS_TAIL_CALL;
        }
    }

    #[inline(always)]
    pub fn is_tbc_close(&self) -> bool {
        self.flags & FLAG_IS_TBC_CLOSE != 0
    }

    #[inline(always)]
    pub fn set_is_tbc_close(&mut self, v: bool) {
        if v {
            self.flags |= FLAG_IS_TBC_CLOSE;
        } else {
            self.flags &= !FLAG_IS_TBC_CLOSE;
        }
    }

    /// Check if tbc_slots is empty (None or empty vec).
    #[inline(always)]
    pub fn tbc_slots_is_empty(&self) -> bool {
        match &self.tbc_slots {
            None => true,
            Some(v) => v.is_empty(),
        }
    }

    /// Push a TBC slot index.
    #[inline]
    pub fn tbc_slots_push(&mut self, slot: usize) {
        match &mut self.tbc_slots {
            Some(v) => v.push(slot),
            None => self.tbc_slots = Some(vec![slot]),
        }
    }
}
