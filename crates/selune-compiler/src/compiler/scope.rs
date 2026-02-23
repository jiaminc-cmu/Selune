/// Scope and variable management for the compiler.
use selune_core::string::StringId;

/// A local variable in the current function scope.
#[derive(Clone, Debug)]
pub struct LocalVarInfo {
    pub name: StringId,
    /// Register index.
    pub reg: u8,
    /// Scope depth when declared.
    pub scope_depth: usize,
    /// Whether this is a const variable (Lua 5.4 <const>).
    pub is_const: bool,
    /// Whether this is a to-be-closed variable (Lua 5.4 <close>).
    pub is_close: bool,
    /// Whether this local was captured as an upvalue by a nested closure.
    pub is_captured: bool,
    /// PC where the variable becomes active.
    pub start_pc: u32,
}

/// Block scope tracking.
#[derive(Clone, Debug)]
pub struct BlockScope {
    /// Number of local variables when this block started.
    pub num_locals_on_entry: usize,
    /// First register that can be freed when this block exits.
    pub first_free_reg_on_entry: u8,
    /// Whether this block is a loop (for break).
    pub is_loop: bool,
    /// Break target patch list: list of JMP PCs to backpatch.
    pub break_jumps: Vec<usize>,
    /// Pending gotos in this block.
    pub pending_gotos: Vec<PendingGoto>,
    /// Labels defined in this block.
    pub labels: Vec<LabelInfo>,
}

/// A forward goto that hasn't been resolved yet.
#[derive(Clone, Debug)]
pub struct PendingGoto {
    pub name: StringId,
    pub pc: usize,
    pub line: u32,
    pub num_locals: usize,
}

/// A label defined in the current block.
#[derive(Clone, Debug)]
pub struct LabelInfo {
    pub name: StringId,
    pub pc: usize,
    pub num_locals: usize,
    pub line: u32,
}

/// Manages scopes and local variables for a single function.
/// A finished local variable (gone out of scope) with end_pc recorded.
#[derive(Clone, Debug)]
pub struct FinishedLocal {
    pub name: StringId,
    pub reg: u8,
    pub start_pc: u32,
    pub end_pc: u32,
}

pub struct ScopeManager {
    /// All local variables in the current function.
    pub locals: Vec<LocalVarInfo>,
    /// Block scope stack.
    pub blocks: Vec<BlockScope>,
    /// Current scope depth.
    pub scope_depth: usize,
    /// Next available register.
    pub free_reg: u8,
    /// High-water mark for register usage.
    pub max_reg: u8,
    /// Locals that have gone out of scope, accumulated for proto.local_vars.
    pub finished_locals: Vec<FinishedLocal>,
    /// Flag set when register allocation would exceed the limit.
    pub reg_overflow: bool,
    /// Flag set when local variable count exceeds the limit.
    pub local_overflow: bool,
}

impl ScopeManager {
    pub fn new() -> Self {
        ScopeManager {
            locals: Vec::new(),
            blocks: Vec::new(),
            scope_depth: 0,
            free_reg: 0,
            max_reg: 0,
            finished_locals: Vec::new(),
            reg_overflow: false,
            local_overflow: false,
        }
    }

    /// Enter a new block scope.
    pub fn enter_block(&mut self, is_loop: bool) {
        self.scope_depth += 1;
        self.blocks.push(BlockScope {
            num_locals_on_entry: self.locals.len(),
            first_free_reg_on_entry: self.free_reg,
            is_loop,
            break_jumps: Vec::new(),
            pending_gotos: Vec::new(),
            labels: Vec::new(),
        });
    }

    /// Check if the current block has any to-be-closed variables.
    /// Returns the register of the first close variable in the block (if any).
    pub fn block_has_close_var(&self) -> Option<u8> {
        let block = self.blocks.last()?;
        for local in &self.locals[block.num_locals_on_entry..] {
            if local.is_close {
                return Some(local.reg);
            }
        }
        None
    }

    /// Check if the current block needs a Close instruction (has TBC or captured locals).
    /// Returns the register of the first local that needs closing.
    pub fn block_needs_close(&self) -> Option<u8> {
        let block = self.blocks.last()?;
        let mut first_reg = None;
        for local in &self.locals[block.num_locals_on_entry..] {
            if local.is_close || local.is_captured {
                match first_reg {
                    None => first_reg = Some(local.reg),
                    Some(r) if local.reg < r => first_reg = Some(local.reg),
                    _ => {}
                }
            }
        }
        first_reg
    }

    /// Check if any to-be-closed variable exists in the current function scope.
    /// When true, `return f()` cannot be compiled as a tail call.
    pub fn has_tbc_in_scope(&self) -> bool {
        self.locals.iter().any(|l| l.is_close)
    }

    /// Mark a local variable at the given register as captured by a closure.
    pub fn mark_captured(&mut self, reg: u8) {
        for local in self.locals.iter_mut() {
            if local.reg == reg {
                local.is_captured = true;
                return;
            }
        }
    }

    /// Leave the current block scope. Returns break jump PCs to patch.
    /// Unresolved pending gotos are propagated to the parent block.
    /// Goto num_locals are adjusted to the block entry level (PUC Lua semantics).
    /// Adjust labels at the end of the current block.
    /// Labels whose PC equals `current_pc` (nothing emitted after them) have their
    /// num_locals reduced to the block entry level. This implements PUC Lua's
    /// "label at block end" semantics: gotos can jump over locals to labels at block end.
    /// Returns any resolved (goto_idx, target_pc) pairs for patching.
    pub fn adjust_end_labels(&mut self, current_pc: usize) -> Vec<(usize, usize)> {
        let block = match self.blocks.last_mut() {
            Some(b) => b,
            None => return vec![],
        };
        let entry_locals = block.num_locals_on_entry;

        // Adjust labels at block end: any label whose PC == current_pc
        // (i.e., no instructions were emitted after it)
        for label in &mut block.labels {
            if label.pc == current_pc {
                label.num_locals = entry_locals;
            }
        }

        // Re-resolve pending gotos against adjusted labels
        let mut resolved = Vec::new(); // (goto_pc, target_pc)
        let mut resolved_indices = Vec::new();
        for (goto_idx, goto_info) in block.pending_gotos.iter().enumerate() {
            for label in &block.labels {
                if label.name == goto_info.name && goto_info.num_locals >= label.num_locals {
                    resolved.push((goto_info.pc, label.pc));
                    resolved_indices.push(goto_idx);
                    break;
                }
            }
        }

        // Remove resolved gotos (in reverse order to maintain indices)
        for &idx in resolved_indices.iter().rev() {
            block.pending_gotos.remove(idx);
        }

        resolved
    }

    pub fn leave_block(&mut self) -> BlockScope {
        self.leave_block_at_pc(0)
    }

    pub fn leave_block_at_pc(&mut self, end_pc: u32) -> BlockScope {
        self.scope_depth -= 1;
        let block = self.blocks.pop().expect("mismatched block");
        // Record locals going out of scope into finished_locals
        for local in &self.locals[block.num_locals_on_entry..] {
            self.finished_locals.push(FinishedLocal {
                name: local.name,
                reg: local.reg,
                start_pc: local.start_pc,
                end_pc,
            });
        }
        // Remove locals declared in this block
        self.locals.truncate(block.num_locals_on_entry);
        self.free_reg = block.first_free_reg_on_entry;

        // Propagate unresolved pending gotos to the parent block
        // Adjust num_locals down to the block entry level
        if !block.pending_gotos.is_empty() {
            if let Some(parent) = self.blocks.last_mut() {
                let adjusted_gotos = block.pending_gotos.iter().map(|g| {
                    let mut adjusted = g.clone();
                    if adjusted.num_locals > block.num_locals_on_entry {
                        adjusted.num_locals = block.num_locals_on_entry;
                    }
                    adjusted
                });
                parent.pending_gotos.extend(adjusted_gotos);
            }
        }

        block
    }

    /// Register a new local variable. Returns its register.
    pub fn add_local(
        &mut self,
        name: StringId,
        is_const: bool,
        is_close: bool,
        start_pc: u32,
    ) -> u8 {
        if self.locals.len() >= 200 {
            self.local_overflow = true;
        }
        let reg = self.free_reg;
        self.locals.push(LocalVarInfo {
            name,
            reg,
            scope_depth: self.scope_depth,
            is_const,
            is_close,
            is_captured: false,
            start_pc,
        });
        self.free_reg += 1;
        if self.free_reg > self.max_reg {
            self.max_reg = self.free_reg;
        }
        reg
    }

    /// Allocate a temporary register.
    pub fn alloc_reg(&mut self) -> u8 {
        if self.free_reg >= 249 {
            self.reg_overflow = true;
        }
        let reg = self.free_reg;
        self.free_reg = self.free_reg.wrapping_add(1);
        if self.free_reg > self.max_reg {
            self.max_reg = self.free_reg;
        }
        reg
    }

    /// Allocate n consecutive registers, returning the first.
    pub fn alloc_regs(&mut self, n: u8) -> u8 {
        if self.free_reg.checked_add(n).is_none() || self.free_reg + n > 249 {
            self.reg_overflow = true;
        }
        let first = self.free_reg;
        self.free_reg = self.free_reg.wrapping_add(n);
        if self.free_reg > self.max_reg {
            self.max_reg = self.free_reg;
        }
        first
    }

    /// Free registers down to the given free_reg level.
    pub fn free_reg_to(&mut self, level: u8) {
        if level <= self.free_reg {
            self.free_reg = level;
        }
    }

    /// Look up a local variable by name. Returns register if found.
    pub fn resolve_local(&self, name: StringId) -> Option<&LocalVarInfo> {
        self.locals.iter().rev().find(|v| v.name == name)
    }

    /// Look up a local variable by register index.
    pub fn resolve_local_by_reg(&self, reg: u8) -> Option<&LocalVarInfo> {
        self.locals.iter().rev().find(|v| v.reg == reg)
    }

    /// Get number of active locals.
    pub fn num_locals(&self) -> usize {
        self.locals.len()
    }

    /// Find the nearest enclosing loop block.
    pub fn find_loop_block(&mut self) -> Option<&mut BlockScope> {
        self.blocks.iter_mut().rev().find(|b| b.is_loop)
    }

    /// Check if a break from the current position needs to close upvalues.
    /// Scans from current locals back to the enclosing loop block's entry level.
    /// Returns the register of the first captured/TBC local, if any.
    pub fn break_needs_close(&self) -> Option<u8> {
        // Find the enclosing loop block
        let loop_block = self.blocks.iter().rev().find(|b| b.is_loop)?;
        let loop_entry_locals = loop_block.num_locals_on_entry;
        let mut first_reg = None;
        for local in &self.locals[loop_entry_locals..] {
            if local.is_close || local.is_captured {
                match first_reg {
                    None => first_reg = Some(local.reg),
                    Some(r) if local.reg < r => first_reg = Some(local.reg),
                    _ => {}
                }
            }
        }
        first_reg
    }

    /// Get the current innermost block.
    pub fn current_block_mut(&mut self) -> Option<&mut BlockScope> {
        self.blocks.last_mut()
    }
}

impl Default for ScopeManager {
    fn default() -> Self {
        Self::new()
    }
}
