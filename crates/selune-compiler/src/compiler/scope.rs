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
}

/// Manages scopes and local variables for a single function.
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
}

impl ScopeManager {
    pub fn new() -> Self {
        ScopeManager {
            locals: Vec::new(),
            blocks: Vec::new(),
            scope_depth: 0,
            free_reg: 0,
            max_reg: 0,
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

    /// Leave the current block scope. Returns break jump PCs to patch.
    pub fn leave_block(&mut self) -> BlockScope {
        self.scope_depth -= 1;
        let block = self.blocks.pop().expect("mismatched block");
        // Remove locals declared in this block
        self.locals.truncate(block.num_locals_on_entry);
        self.free_reg = block.first_free_reg_on_entry;
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
        let reg = self.free_reg;
        self.locals.push(LocalVarInfo {
            name,
            reg,
            scope_depth: self.scope_depth,
            is_const,
            is_close,
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
        let reg = self.free_reg;
        self.free_reg += 1;
        if self.free_reg > self.max_reg {
            self.max_reg = self.free_reg;
        }
        reg
    }

    /// Allocate n consecutive registers, returning the first.
    pub fn alloc_regs(&mut self, n: u8) -> u8 {
        let first = self.free_reg;
        self.free_reg += n;
        if self.free_reg > self.max_reg {
            self.max_reg = self.free_reg;
        }
        first
    }

    /// Free registers down to the given free_reg level.
    pub fn free_reg_to(&mut self, level: u8) {
        debug_assert!(level <= self.free_reg);
        self.free_reg = level;
    }

    /// Look up a local variable by name. Returns register if found.
    pub fn resolve_local(&self, name: StringId) -> Option<&LocalVarInfo> {
        self.locals.iter().rev().find(|v| v.name == name)
    }

    /// Get number of active locals.
    pub fn num_locals(&self) -> usize {
        self.locals.len()
    }

    /// Find the nearest enclosing loop block.
    pub fn find_loop_block(&mut self) -> Option<&mut BlockScope> {
        self.blocks.iter_mut().rev().find(|b| b.is_loop)
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
