use std::collections::HashMap;
use std::fmt;

use cranelift_codegen::ir::{types, AbiParam, Block, FuncRef, InstBuilder, MemFlags, Signature, Value};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{default_libcall_names, Linkage, Module};

use selune_compiler::opcode::OpCode;
use selune_compiler::proto::{Constant, Proto};
use selune_core::gc::GcHeap;
use selune_core::value::{self, TValue};

use crate::abi::{self, JitFunction};
use crate::runtime;

/// Side-exit return value: signals the caller to fall back to the interpreter.
pub const SIDE_EXIT: i64 = -1;

/// Errors from JIT compilation.
#[derive(Debug)]
pub enum JitError {
    /// Cranelift module-level error (declaration, definition, finalization).
    Module(cranelift_module::ModuleError),
    /// Failed to initialize the native code generator.
    Init(String),
    /// The proto contains an opcode we can't JIT yet.
    UnsupportedOpcode(OpCode, usize),
}

impl fmt::Display for JitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            JitError::Module(e) => write!(f, "JIT module error: {e}"),
            JitError::Init(s) => write!(f, "JIT init error: {s}"),
            JitError::UnsupportedOpcode(op, pc) => {
                write!(f, "unsupported opcode {op:?} at pc={pc}")
            }
        }
    }
}

impl From<cranelift_module::ModuleError> for JitError {
    fn from(e: cranelift_module::ModuleError) -> Self {
        JitError::Module(e)
    }
}

/// The JIT compiler. Wraps a Cranelift JITModule and reusable compilation context.
pub struct JitCompiler {
    module: JITModule,
    ctx: Context,
    func_ctx: FunctionBuilderContext,
    /// Counter for generating unique function names.
    func_counter: usize,
}

impl JitCompiler {
    /// Create a new JIT compiler targeting the host platform.
    pub fn new() -> Result<Self, JitError> {
        let mut builder = JITBuilder::new(default_libcall_names())
            .map_err(|e| JitError::Init(e.to_string()))?;

        // Register runtime helper symbols so JIT code can call them.
        builder.symbol(
            "jit_rt_set_stack_slot",
            runtime::jit_rt_set_stack_slot as *const u8,
        );
        builder.symbol(
            "jit_rt_get_stack_slot",
            runtime::jit_rt_get_stack_slot as *const u8,
        );
        builder.symbol(
            "jit_rt_get_upval",
            runtime::jit_rt_get_upval as *const u8,
        );
        builder.symbol(
            "jit_rt_set_upval",
            runtime::jit_rt_set_upval as *const u8,
        );
        builder.symbol(
            "jit_rt_get_tab_up",
            runtime::jit_rt_get_tab_up as *const u8,
        );
        builder.symbol(
            "jit_rt_set_tab_up",
            runtime::jit_rt_set_tab_up as *const u8,
        );
        builder.symbol("jit_rt_call", runtime::jit_rt_call as *const u8);
        builder.symbol("jit_rt_self", runtime::jit_rt_self as *const u8);
        builder.symbol(
            "jit_rt_table_index",
            runtime::jit_rt_table_index as *const u8,
        );
        builder.symbol(
            "jit_rt_table_newindex",
            runtime::jit_rt_table_newindex as *const u8,
        );

        let module = JITModule::new(builder);
        let ctx = module.make_context();

        Ok(JitCompiler {
            module,
            ctx,
            func_ctx: FunctionBuilderContext::new(),
            func_counter: 0,
        })
    }

    /// Generate a unique function name.
    fn next_name(&mut self, prefix: &str) -> String {
        let n = self.func_counter;
        self.func_counter += 1;
        format!("{prefix}_{n}")
    }

    /// Compile a function that simply returns a constant i64 value.
    pub fn compile_return_constant(&mut self, constant: i64) -> Result<JitFunction, JitError> {
        let name = self.next_name("ret_const");
        let sig = abi::jit_function_signature(self.module.isa().default_call_conv());

        let func_id = self.module.declare_function(&name, Linkage::Local, &sig)?;

        self.ctx.func.signature = sig;
        {
            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.func_ctx);
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let val = builder.ins().iconst(types::I64, constant);
            builder.ins().return_(&[val]);
            builder.finalize();
        }

        self.module.define_function(func_id, &mut self.ctx)?;
        self.module.clear_context(&mut self.ctx);
        self.module.finalize_definitions()?;

        let code_ptr = self.module.get_finalized_function(func_id);
        // SAFETY: Cranelift generated valid machine code matching our signature.
        let func: JitFunction = unsafe { std::mem::transmute(code_ptr) };
        Ok(func)
    }

    /// Compile a function that writes a TValue to stack[base+0] and returns 1.
    pub fn compile_return_tvalue(&mut self, raw_bits: u64) -> Result<JitFunction, JitError> {
        let name = self.next_name("ret_tval");
        let sig = abi::jit_function_signature(self.module.isa().default_call_conv());
        let func_id = self.module.declare_function(&name, Linkage::Local, &sig)?;

        let call_conv = self.module.isa().default_call_conv();
        let mut helper_sig = Signature::new(call_conv);
        helper_sig.params.push(AbiParam::new(types::I64));
        helper_sig.params.push(AbiParam::new(types::I64));
        helper_sig.params.push(AbiParam::new(types::I64));
        helper_sig.params.push(AbiParam::new(types::I64));

        let helper_id = self.module.declare_function(
            "jit_rt_set_stack_slot",
            Linkage::Import,
            &helper_sig,
        )?;

        self.ctx.func.signature = sig;
        {
            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.func_ctx);
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let vm_ptr = builder.block_params(entry)[0];
            let base = builder.block_params(entry)[1];

            let helper_ref = self.module.declare_func_in_func(helper_id, builder.func);

            let offset_val = builder.ins().iconst(types::I64, 0);
            let bits_val = builder.ins().iconst(types::I64, raw_bits as i64);
            builder
                .ins()
                .call(helper_ref, &[vm_ptr, base, offset_val, bits_val]);

            let one = builder.ins().iconst(types::I64, 1);
            builder.ins().return_(&[one]);
            builder.finalize();
        }

        self.module.define_function(func_id, &mut self.ctx)?;
        self.module.clear_context(&mut self.ctx);
        self.module.finalize_definitions()?;

        let code_ptr = self.module.get_finalized_function(func_id);
        let func: JitFunction = unsafe { std::mem::transmute(code_ptr) };
        Ok(func)
    }

    /// Compile a Lua function prototype to native code.
    ///
    /// Translates bytecodes to Cranelift IR. Supports a subset of opcodes:
    /// - Loads: Move, LoadI, LoadF, LoadK, LoadKX, LoadFalse, LFalseSkip, LoadTrue, LoadNil
    /// - Returns: Return0, Return1
    /// - Arithmetic: Add, Sub, Mul, AddK, SubK, MulK, AddI, IDiv, Mod, Div, Pow(side-exit)
    /// - Bitwise: BAnd, BOr, BXor, Shl, Shr, BAndK, BOrK, BXorK, ShrI, ShlI, Unm, BNot
    /// - Control flow: Jmp, Test, TestSet, Not
    /// - Comparisons: EqI, LtI, LeI, GtI, GeI, EqK, Eq, Lt, Le
    /// - Loops: ForPrep, ForLoop (integer fast-path only)
    /// - Table/Upvalue: GetTabUp, SetTabUp, GetUpval, SetUpval, GetTable, GetField, SetField
    /// - Calls: Call (via runtime helper), Self_
    /// - Side-exit: Return, TailCall, Closure
    /// - Skips: MMBin, MMBinI, MMBinK (skipped as part of arithmetic translation)
    ///
    /// `proto_idx` is the index of this proto in `vm.protos[]`, used by runtime
    /// helpers that need to access the proto's constant pool.
    /// Pass `0` for tests that don't use opcodes requiring proto_idx.
    ///
    /// Returns `JitError::UnsupportedOpcode` if any unhandled opcode is encountered.
    pub fn compile_proto(
        &mut self,
        proto: &Proto,
        gc: &mut GcHeap,
        proto_idx: usize,
    ) -> Result<JitFunction, JitError> {
        // First pass: check all opcodes are supported (except MMBin* which are skipped)
        let mut skip_next = false;
        for (pc, inst) in proto.code.iter().enumerate() {
            if skip_next {
                skip_next = false;
                continue;
            }
            let op = inst.opcode();
            match op {
                OpCode::Move
                | OpCode::LoadI
                | OpCode::LoadF
                | OpCode::LoadK
                | OpCode::LoadKX
                | OpCode::LoadFalse
                | OpCode::LFalseSkip
                | OpCode::LoadTrue
                | OpCode::LoadNil
                | OpCode::Return0
                | OpCode::Return1
                | OpCode::Jmp
                | OpCode::Test
                | OpCode::TestSet
                | OpCode::Not
                | OpCode::EqI
                | OpCode::LtI
                | OpCode::LeI
                | OpCode::GtI
                | OpCode::GeI
                | OpCode::EqK
                | OpCode::Eq
                | OpCode::Lt
                | OpCode::Le
                | OpCode::ForPrep
                | OpCode::ForLoop => {}
                // Unary ops: no following MMBin instruction
                | OpCode::Unm
                | OpCode::BNot => {}
                // ShrI/ShlI: no following MMBinI (compiler doesn't emit one)
                | OpCode::ShrI
                | OpCode::ShlI => {}
                // Arithmetic ops: the next instruction is MMBin/MMBinI/MMBinK (skip it)
                OpCode::Add | OpCode::Sub | OpCode::Mul
                | OpCode::Div | OpCode::IDiv | OpCode::Mod | OpCode::Pow
                | OpCode::BAnd | OpCode::BOr | OpCode::BXor
                | OpCode::Shl | OpCode::Shr
                | OpCode::AddK | OpCode::SubK | OpCode::MulK
                | OpCode::DivK | OpCode::IDivK | OpCode::ModK | OpCode::PowK
                | OpCode::BAndK | OpCode::BOrK | OpCode::BXorK
                | OpCode::AddI => {
                    skip_next = true;
                }
                // These are skipped as part of arithmetic
                OpCode::MMBin | OpCode::MMBinI | OpCode::MMBinK => {}
                // VarArgPrep: no-op in our compiler (just sets up varargs)
                OpCode::VarArgPrep => {}
                // ExtraArg: consumed by LoadKX
                OpCode::ExtraArg => {}
                // Increment 5: function calls, upvalues, table access (via runtime helpers)
                | OpCode::GetTabUp
                | OpCode::SetTabUp
                | OpCode::GetUpval
                | OpCode::SetUpval
                | OpCode::Call
                | OpCode::Self_
                | OpCode::GetTable
                | OpCode::GetField
                | OpCode::SetField => {}
                // Side-exit only: too complex for JIT fast-path
                | OpCode::Return
                | OpCode::TailCall
                | OpCode::Closure => {}
                _ => return Err(JitError::UnsupportedOpcode(op, pc)),
            }
        }

        let name = self.next_name("proto");
        let sig = abi::jit_function_signature(self.module.isa().default_call_conv());
        let func_id = self.module.declare_function(&name, Linkage::Local, &sig)?;

        // Declare runtime helpers
        let call_conv = self.module.isa().default_call_conv();

        let mut set_sig = Signature::new(call_conv);
        set_sig.params.push(AbiParam::new(types::I64)); // vm_ptr
        set_sig.params.push(AbiParam::new(types::I64)); // base
        set_sig.params.push(AbiParam::new(types::I64)); // offset
        set_sig.params.push(AbiParam::new(types::I64)); // raw_bits
        let set_id = self
            .module
            .declare_function("jit_rt_set_stack_slot", Linkage::Import, &set_sig)?;

        let mut get_sig = Signature::new(call_conv);
        get_sig.params.push(AbiParam::new(types::I64)); // vm_ptr
        get_sig.params.push(AbiParam::new(types::I64)); // base
        get_sig.params.push(AbiParam::new(types::I64)); // offset
        get_sig.returns.push(AbiParam::new(types::I64)); // raw_bits
        let get_id = self
            .module
            .declare_function("jit_rt_get_stack_slot", Linkage::Import, &get_sig)?;

        // jit_rt_get_upval(vm_ptr, upval_idx) -> u64
        let mut get_upval_sig = Signature::new(call_conv);
        get_upval_sig.params.push(AbiParam::new(types::I64));
        get_upval_sig.params.push(AbiParam::new(types::I64));
        get_upval_sig.returns.push(AbiParam::new(types::I64));
        let get_upval_id = self
            .module
            .declare_function("jit_rt_get_upval", Linkage::Import, &get_upval_sig)?;

        // jit_rt_set_upval(vm_ptr, upval_idx, val_bits)
        let mut set_upval_sig = Signature::new(call_conv);
        set_upval_sig.params.push(AbiParam::new(types::I64));
        set_upval_sig.params.push(AbiParam::new(types::I64));
        set_upval_sig.params.push(AbiParam::new(types::I64));
        let set_upval_id = self
            .module
            .declare_function("jit_rt_set_upval", Linkage::Import, &set_upval_sig)?;

        // jit_rt_get_tab_up(vm_ptr, proto_idx, upval_b, const_c) -> u64
        let mut get_tab_up_sig = Signature::new(call_conv);
        get_tab_up_sig.params.push(AbiParam::new(types::I64));
        get_tab_up_sig.params.push(AbiParam::new(types::I64));
        get_tab_up_sig.params.push(AbiParam::new(types::I64));
        get_tab_up_sig.params.push(AbiParam::new(types::I64));
        get_tab_up_sig.returns.push(AbiParam::new(types::I64));
        let get_tab_up_id = self
            .module
            .declare_function("jit_rt_get_tab_up", Linkage::Import, &get_tab_up_sig)?;

        // jit_rt_set_tab_up(vm_ptr, base, proto_idx, upval_a, const_b, val_or_c, k_flag) -> i64
        let mut set_tab_up_sig = Signature::new(call_conv);
        for _ in 0..7 {
            set_tab_up_sig.params.push(AbiParam::new(types::I64));
        }
        set_tab_up_sig.returns.push(AbiParam::new(types::I64));
        let set_tab_up_id = self
            .module
            .declare_function("jit_rt_set_tab_up", Linkage::Import, &set_tab_up_sig)?;

        // jit_rt_call(vm_ptr, base, func_off, nargs, nresults) -> i64
        let mut call_sig = Signature::new(call_conv);
        for _ in 0..5 {
            call_sig.params.push(AbiParam::new(types::I64));
        }
        call_sig.returns.push(AbiParam::new(types::I64));
        let call_id = self
            .module
            .declare_function("jit_rt_call", Linkage::Import, &call_sig)?;

        // jit_rt_self(vm_ptr, base, a, b, key_bits) -> i64
        let mut self_sig = Signature::new(call_conv);
        for _ in 0..5 {
            self_sig.params.push(AbiParam::new(types::I64));
        }
        self_sig.returns.push(AbiParam::new(types::I64));
        let self_id = self
            .module
            .declare_function("jit_rt_self", Linkage::Import, &self_sig)?;

        // jit_rt_table_index(vm_ptr, table_bits, key_bits) -> u64
        let mut tbl_idx_sig = Signature::new(call_conv);
        tbl_idx_sig.params.push(AbiParam::new(types::I64));
        tbl_idx_sig.params.push(AbiParam::new(types::I64));
        tbl_idx_sig.params.push(AbiParam::new(types::I64));
        tbl_idx_sig.returns.push(AbiParam::new(types::I64));
        let tbl_idx_id = self
            .module
            .declare_function("jit_rt_table_index", Linkage::Import, &tbl_idx_sig)?;

        // jit_rt_table_newindex(vm_ptr, table_bits, key_bits, val_bits) -> i64
        let mut tbl_ni_sig = Signature::new(call_conv);
        for _ in 0..4 {
            tbl_ni_sig.params.push(AbiParam::new(types::I64));
        }
        tbl_ni_sig.returns.push(AbiParam::new(types::I64));
        let tbl_ni_id = self
            .module
            .declare_function("jit_rt_table_newindex", Linkage::Import, &tbl_ni_sig)?;

        self.ctx.func.signature = sig;

        {
            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.func_ctx);

            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);

            let vm_ptr = builder.block_params(entry)[0];
            let base = builder.block_params(entry)[1];

            let set_ref = self.module.declare_func_in_func(set_id, builder.func);
            let get_ref = self.module.declare_func_in_func(get_id, builder.func);
            let get_upval_ref = self.module.declare_func_in_func(get_upval_id, builder.func);
            let set_upval_ref = self.module.declare_func_in_func(set_upval_id, builder.func);
            let get_tab_up_ref =
                self.module.declare_func_in_func(get_tab_up_id, builder.func);
            let set_tab_up_ref =
                self.module.declare_func_in_func(set_tab_up_id, builder.func);
            let call_ref = self.module.declare_func_in_func(call_id, builder.func);
            let self_ref = self.module.declare_func_in_func(self_id, builder.func);
            let tbl_idx_ref = self.module.declare_func_in_func(tbl_idx_id, builder.func);
            let tbl_ni_ref = self.module.declare_func_in_func(tbl_ni_id, builder.func);

            // Side-exit block: return SIDE_EXIT
            let side_exit_block = builder.create_block();

            // Pre-scan: find all jump targets and create blocks for them
            let pc_blocks = Self::create_pc_blocks(proto, &mut builder);

            // If PC 0 is a jump target, jump from entry to its block
            if let Some(&block) = pc_blocks.get(&0) {
                builder.ins().jump(block, &[]);
            }

            // Emit IR for each bytecode instruction
            let mut emitter = BytecodeEmitter {
                builder: &mut builder,
                vm_ptr,
                base,
                set_ref,
                get_ref,
                get_upval_ref,
                set_upval_ref,
                get_tab_up_ref,
                set_tab_up_ref,
                call_ref,
                self_ref,
                tbl_idx_ref,
                tbl_ni_ref,
                side_exit_block,
                proto,
                gc,
                pc_blocks: &pc_blocks,
                proto_idx,
            };

            emitter.emit_instructions()?;

            // Emit side-exit block
            emitter.builder.switch_to_block(side_exit_block);
            emitter.builder.seal_block(side_exit_block);
            let exit_val = emitter.builder.ins().iconst(types::I64, SIDE_EXIT);
            emitter.builder.ins().return_(&[exit_val]);

            // Seal entry block (after all branches are known)
            builder.seal_block(entry);

            // Seal all remaining blocks (pc blocks, side_exit, etc.)
            builder.seal_all_blocks();
            builder.finalize();
        }

        self.module.define_function(func_id, &mut self.ctx)?;
        self.module.clear_context(&mut self.ctx);
        self.module.finalize_definitions()?;

        let code_ptr = self.module.get_finalized_function(func_id);
        let func: JitFunction = unsafe { std::mem::transmute(code_ptr) };
        Ok(func)
    }

    /// Pre-scan bytecodes to find jump targets and create Cranelift blocks.
    fn create_pc_blocks(proto: &Proto, builder: &mut FunctionBuilder) -> HashMap<usize, Block> {
        let mut targets = std::collections::HashSet::new();
        let code = &proto.code;

        for (pc, inst) in code.iter().enumerate() {
            let op = inst.opcode();
            match op {
                OpCode::Jmp => {
                    let sj = inst.get_sj();
                    let target = (pc as i64 + 1 + sj as i64) as usize;
                    targets.insert(target);
                }
                // Comparisons and Test/TestSet: conditionally skip next instruction.
                // The next instruction is always Jmp, so the skip target is pc+2,
                // and the Jmp itself targets somewhere else. We need a block at pc+1
                // (the Jmp itself) and at pc+2 (the skip-over target).
                OpCode::EqI | OpCode::LtI | OpCode::LeI | OpCode::GtI | OpCode::GeI
                | OpCode::EqK | OpCode::Eq | OpCode::Lt | OpCode::Le
                | OpCode::Test | OpCode::TestSet => {
                    // The next instruction (pc+1) should be a Jmp.
                    // On skip (condition matches k), we go to pc+2.
                    // On no-skip, we fall through to pc+1 (the Jmp).
                    targets.insert(pc + 1);
                    targets.insert(pc + 2);
                }
                OpCode::LFalseSkip => {
                    targets.insert(pc + 2);
                }
                OpCode::ForPrep => {
                    let sbx = inst.sbx();
                    // ForPrep skip: dispatch does pc=(pc+1)+sbx; pc+=1
                    // So skip target = pc + 2 + sbx (lands past ForLoop)
                    let target = (pc as i64 + 2 + sbx as i64) as usize;
                    targets.insert(target);
                    // The loop body starts at pc+1
                    targets.insert(pc + 1);
                }
                OpCode::ForLoop => {
                    let sbx = inst.sbx();
                    // ForLoop: dispatch does pc = (pc+1) + sbx (sbx is negative for back-jump)
                    let target = (pc as i64 + 1 + sbx as i64) as usize;
                    targets.insert(target);
                    // Fall-through (loop exit) is pc+1
                    targets.insert(pc + 1);
                }
                _ => {}
            }
        }

        let mut pc_blocks = HashMap::new();
        for target in targets {
            if target < code.len() {
                let block = builder.create_block();
                pc_blocks.insert(target, block);
            }
        }
        pc_blocks
    }
}

/// NaN-boxing constants used by JIT codegen.
const QNAN_TAG_INT: i64 = (value::QNAN | value::TAG_INT) as i64;
const PAYLOAD_MASK: i64 = value::PAYLOAD_MASK as i64;
const SMALL_INT_MIN: i64 = value::SMALL_INT_MIN;
const SMALL_INT_MAX: i64 = value::SMALL_INT_MAX;

/// Helper struct that holds state during bytecode → IR translation.
struct BytecodeEmitter<'a, 'b> {
    builder: &'a mut FunctionBuilder<'b>,
    vm_ptr: Value,
    base: Value,
    set_ref: FuncRef,
    get_ref: FuncRef,
    get_upval_ref: FuncRef,
    set_upval_ref: FuncRef,
    get_tab_up_ref: FuncRef,
    set_tab_up_ref: FuncRef,
    call_ref: FuncRef,
    self_ref: FuncRef,
    tbl_idx_ref: FuncRef,
    tbl_ni_ref: FuncRef,
    side_exit_block: Block,
    proto: &'a Proto,
    gc: &'a mut GcHeap,
    /// Maps bytecode PC → Cranelift block (for jump targets).
    pc_blocks: &'a HashMap<usize, Block>,
    /// Index of this proto in vm.protos[], used by runtime helpers.
    proto_idx: usize,
}

impl<'a, 'b> BytecodeEmitter<'a, 'b> {
    /// Emit a call to jit_rt_set_stack_slot(vm, base, offset, raw_bits).
    fn emit_set_slot(&mut self, offset: i64, raw_bits: Value) {
        let offset_val = self.builder.ins().iconst(types::I64, offset);
        self.builder
            .ins()
            .call(self.set_ref, &[self.vm_ptr, self.base, offset_val, raw_bits]);
    }

    /// Emit a call to jit_rt_get_stack_slot(vm, base, offset) -> raw_bits.
    fn emit_get_slot(&mut self, offset: i64) -> Value {
        let offset_val = self.builder.ins().iconst(types::I64, offset);
        let call = self
            .builder
            .ins()
            .call(self.get_ref, &[self.vm_ptr, self.base, offset_val]);
        self.builder.inst_results(call)[0]
    }

    /// Logical NOT for boolean (i8) values from icmp.
    /// bnot does bitwise NOT which turns 1 → 0xFE (still truthy in brif).
    /// This does: result = (val == 0) ? 1 : 0.
    fn emit_bool_not(&mut self, val: Value) -> Value {
        let zero = self.builder.ins().iconst(types::I8, 0);
        self.builder.ins().icmp(IntCC::Equal, val, zero)
    }

    /// Convert a Constant to its raw NaN-boxed u64 bits.
    fn constant_to_raw_bits(&mut self, k: &Constant) -> u64 {
        match k {
            Constant::Nil => TValue::nil().raw_bits(),
            Constant::Boolean(b) => TValue::from_bool(*b).raw_bits(),
            Constant::Integer(i) => TValue::from_full_integer(*i, self.gc).raw_bits(),
            Constant::Float(f) => TValue::from_float(*f).raw_bits(),
            Constant::String(sid) => TValue::from_string_id(*sid).raw_bits(),
        }
    }

    /// Emit a type guard: check if `val` is an inline integer (QNAN | TAG_INT prefix).
    /// Branches to side_exit_block if NOT an integer.
    /// Returns the extracted i64 integer value (sign-extended from 47-bit payload).
    fn emit_integer_guard(&mut self, val: Value) -> Value {
        // Check: (val & ~PAYLOAD_MASK) == QNAN_TAG_INT
        let mask = self.builder.ins().iconst(types::I64, !PAYLOAD_MASK);
        let upper = self.builder.ins().band(val, mask);
        let expected = self.builder.ins().iconst(types::I64, QNAN_TAG_INT);

        let is_int = self.builder.ins().icmp(
            IntCC::Equal,
            upper,
            expected,
        );

        let cont_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(is_int, cont_block, &[], self.side_exit_block, &[]);

        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);

        // Extract the integer payload: sign-extend from 47 bits
        let payload_mask = self.builder.ins().iconst(types::I64, PAYLOAD_MASK);
        let payload = self.builder.ins().band(val, payload_mask);
        // Sign-extend: shift left 17, then arithmetic shift right 17
        let shifted = self.builder.ins().ishl_imm(payload, 17);
        self.builder.ins().sshr_imm(shifted, 17)
    }

    /// NaN-box an i64 integer back into a TValue (inline small int path only).
    /// Caller must ensure the value is in [SMALL_INT_MIN, SMALL_INT_MAX].
    fn emit_box_integer(&mut self, int_val: Value) -> Value {
        let mask = self.builder.ins().iconst(types::I64, PAYLOAD_MASK);
        let payload = self.builder.ins().band(int_val, mask);
        let tag = self.builder.ins().iconst(types::I64, QNAN_TAG_INT);
        self.builder.ins().bor(payload, tag)
    }

    /// Emit an integer overflow check + side-exit.
    /// If `result` is outside [SMALL_INT_MIN, SMALL_INT_MAX], branches to side_exit.
    fn emit_overflow_guard(&mut self, result: Value) {
        // Check: result >= SMALL_INT_MIN && result <= SMALL_INT_MAX
        // Equivalent: (result - SMALL_INT_MIN) as u64 <= (SMALL_INT_MAX - SMALL_INT_MIN) as u64
        let min_val = self.builder.ins().iconst(types::I64, SMALL_INT_MIN);
        let shifted = self.builder.ins().isub(result, min_val);
        let range = self
            .builder
            .ins()
            .iconst(types::I64, SMALL_INT_MAX - SMALL_INT_MIN);

        let in_range = self.builder.ins().icmp(
            IntCC::UnsignedLessThanOrEqual,
            shifted,
            range,
        );

        let cont_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(in_range, cont_block, &[], self.side_exit_block, &[]);

        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);
    }

    /// Transition to a new block at the given PC if it's a jump target.
    /// Emits a fallthrough jump from the current block if needed.
    fn maybe_switch_to_pc_block(&mut self, pc: usize, block_terminated: &mut bool) {
        if let Some(&target_block) = self.pc_blocks.get(&pc) {
            if !*block_terminated {
                // Fallthrough: jump from current block to the target block
                self.builder.ins().jump(target_block, &[]);
            }
            self.builder.switch_to_block(target_block);
            *block_terminated = false;
        }
    }

    /// Emit a conditional skip pattern: if `condition` is true, skip to pc+2;
    /// otherwise fall through to pc+1. This matches how comparisons and
    /// Test/TestSet interact with the following Jmp instruction.
    fn emit_cond_skip(&mut self, condition: Value, pc: usize) {
        let skip_block = self.pc_blocks.get(&(pc + 2)).copied()
            .expect("comparison skip target pc+2 should have a block");
        let fall_block = self.pc_blocks.get(&(pc + 1)).copied()
            .expect("comparison fallthrough pc+1 should have a block");
        self.builder.ins().brif(condition, skip_block, &[], fall_block, &[]);
    }

    /// Emit all bytecode instructions.
    fn emit_instructions(&mut self) -> Result<(), JitError> {
        let code = &self.proto.code;
        let mut pc = 0;
        let mut block_terminated = false;

        while pc < code.len() {
            // If this PC is a jump target, switch to its block
            self.maybe_switch_to_pc_block(pc, &mut block_terminated);

            let inst = code[pc];
            let op = inst.opcode();
            let a = inst.a() as i64;

            // If the current block was terminated (by a return/jump), skip
            // until we hit a new block (a jump target).
            if block_terminated {
                pc += 1;
                continue;
            }

            match op {
                OpCode::Move => {
                    let b = inst.b() as i64;
                    let val = self.emit_get_slot(b);
                    self.emit_set_slot(a, val);
                }

                OpCode::LoadI => {
                    let sbx = inst.sbx() as i64;
                    let raw_bits = TValue::from_integer(sbx).raw_bits();
                    let val = self.builder.ins().iconst(types::I64, raw_bits as i64);
                    self.emit_set_slot(a, val);
                }

                OpCode::LoadF => {
                    let sbx = inst.sbx() as f64;
                    let raw_bits = TValue::from_float(sbx).raw_bits();
                    let val = self.builder.ins().iconst(types::I64, raw_bits as i64);
                    self.emit_set_slot(a, val);
                }

                OpCode::LoadK => {
                    let bx = inst.bx() as usize;
                    let raw_bits = self.constant_to_raw_bits(&self.proto.constants[bx]);
                    let val = self.builder.ins().iconst(types::I64, raw_bits as i64);
                    self.emit_set_slot(a, val);
                }

                OpCode::LoadKX => {
                    pc += 1;
                    let ax = code[pc].ax_field() as usize;
                    let raw_bits = self.constant_to_raw_bits(&self.proto.constants[ax]);
                    let val = self.builder.ins().iconst(types::I64, raw_bits as i64);
                    self.emit_set_slot(a, val);
                }

                OpCode::LoadFalse => {
                    let raw_bits = TValue::from_bool(false).raw_bits();
                    let val = self.builder.ins().iconst(types::I64, raw_bits as i64);
                    self.emit_set_slot(a, val);
                }

                OpCode::LFalseSkip => {
                    let raw_bits = TValue::from_bool(false).raw_bits();
                    let val = self.builder.ins().iconst(types::I64, raw_bits as i64);
                    self.emit_set_slot(a, val);
                    // Skip next instruction — jump to pc+2
                    if let Some(&target) = self.pc_blocks.get(&(pc + 2)) {
                        self.builder.ins().jump(target, &[]);
                        block_terminated = true;
                    }
                    pc += 1;
                }

                OpCode::LoadTrue => {
                    let raw_bits = TValue::from_bool(true).raw_bits();
                    let val = self.builder.ins().iconst(types::I64, raw_bits as i64);
                    self.emit_set_slot(a, val);
                }

                OpCode::LoadNil => {
                    let b = inst.b() as i64;
                    let nil_bits = TValue::nil().raw_bits();
                    let nil_val = self.builder.ins().iconst(types::I64, nil_bits as i64);
                    for i in 0..=b {
                        self.emit_set_slot(a + i, nil_val);
                    }
                }

                OpCode::Return0 => {
                    let zero = self.builder.ins().iconst(types::I64, 0);
                    self.builder.ins().return_(&[zero]);
                    block_terminated = true;
                }

                OpCode::Return1 => {
                    if a != 0 {
                        let val = self.emit_get_slot(a);
                        self.emit_set_slot(0, val);
                    }
                    let one = self.builder.ins().iconst(types::I64, 1);
                    self.builder.ins().return_(&[one]);
                    block_terminated = true;
                }

                OpCode::Add | OpCode::Sub | OpCode::Mul => {
                    let b = inst.b() as i64;
                    let c = inst.c() as i64;

                    let vb = self.emit_get_slot(b);
                    let vc = self.emit_get_slot(c);

                    let ib = self.emit_integer_guard(vb);
                    let ic = self.emit_integer_guard(vc);

                    let result = match op {
                        OpCode::Add => self.builder.ins().iadd(ib, ic),
                        OpCode::Sub => self.builder.ins().isub(ib, ic),
                        OpCode::Mul => self.builder.ins().imul(ib, ic),
                        _ => unreachable!(),
                    };

                    self.emit_overflow_guard(result);

                    let boxed = self.emit_box_integer(result);
                    self.emit_set_slot(a, boxed);

                    // Skip the following MMBin instruction
                    pc += 1;
                }

                OpCode::AddK | OpCode::SubK | OpCode::MulK => {
                    let b = inst.b() as i64;
                    let c = inst.c() as usize;

                    let vb = self.emit_get_slot(b);
                    let ib = self.emit_integer_guard(vb);

                    let k = &self.proto.constants[c];
                    let kval = match k {
                        Constant::Integer(i) => *i,
                        _ => {
                            self.builder.ins().jump(self.side_exit_block, &[]);
                            block_terminated = true;
                            pc += 1; // skip MMBinK
                            pc += 1;
                            continue;
                        }
                    };

                    let kc = self.builder.ins().iconst(types::I64, kval);
                    let result = match op {
                        OpCode::AddK => self.builder.ins().iadd(ib, kc),
                        OpCode::SubK => self.builder.ins().isub(ib, kc),
                        OpCode::MulK => self.builder.ins().imul(ib, kc),
                        _ => unreachable!(),
                    };

                    self.emit_overflow_guard(result);

                    let boxed = self.emit_box_integer(result);
                    self.emit_set_slot(a, boxed);

                    pc += 1;
                }

                OpCode::AddI => {
                    let b = inst.b() as i64;
                    let sc = inst.c() as i8 as i64;

                    let vb = self.emit_get_slot(b);
                    let ib = self.emit_integer_guard(vb);

                    let imm = self.builder.ins().iconst(types::I64, sc);
                    let result = self.builder.ins().iadd(ib, imm);

                    self.emit_overflow_guard(result);

                    let boxed = self.emit_box_integer(result);
                    self.emit_set_slot(a, boxed);

                    pc += 1;
                }

                // ---- Integer division (R[A] = R[B] // R[C]) ----
                OpCode::IDiv => {
                    let b = inst.b() as i64;
                    let c = inst.c() as i64;

                    let vb = self.emit_get_slot(b);
                    let vc = self.emit_get_slot(c);

                    let ib = self.emit_integer_guard(vb);
                    let ic = self.emit_integer_guard(vc);

                    // Guard: divisor != 0
                    let zero = self.builder.ins().iconst(types::I64, 0);
                    let nz = self.builder.ins().icmp(IntCC::NotEqual, ic, zero);
                    let cont = self.builder.create_block();
                    self.builder.ins().brif(nz, cont, &[], self.side_exit_block, &[]);
                    self.builder.switch_to_block(cont);
                    self.builder.seal_block(cont);

                    // Lua idiv: floor division
                    let result = self.emit_lua_idiv(ib, ic);
                    // Result magnitude ≤ |dividend|, no overflow guard needed
                    let boxed = self.emit_box_integer(result);
                    self.emit_set_slot(a, boxed);

                    pc += 1; // skip MMBin
                }

                // ---- Modulo (R[A] = R[B] % R[C]) ----
                OpCode::Mod => {
                    let b = inst.b() as i64;
                    let c = inst.c() as i64;

                    let vb = self.emit_get_slot(b);
                    let vc = self.emit_get_slot(c);

                    let ib = self.emit_integer_guard(vb);
                    let ic = self.emit_integer_guard(vc);

                    // Guard: divisor != 0
                    let zero = self.builder.ins().iconst(types::I64, 0);
                    let nz = self.builder.ins().icmp(IntCC::NotEqual, ic, zero);
                    let cont = self.builder.create_block();
                    self.builder.ins().brif(nz, cont, &[], self.side_exit_block, &[]);
                    self.builder.switch_to_block(cont);
                    self.builder.seal_block(cont);

                    // Lua imod: result sign matches divisor
                    let result = self.emit_lua_imod(ib, ic);
                    let boxed = self.emit_box_integer(result);
                    self.emit_set_slot(a, boxed);

                    pc += 1; // skip MMBin
                }

                // ---- Float division (R[A] = R[B] / R[C]) — always produces float ----
                OpCode::Div => {
                    let b = inst.b() as i64;
                    let c = inst.c() as i64;

                    let vb = self.emit_get_slot(b);
                    let vc = self.emit_get_slot(c);

                    // Both must be inline integers for our fast path
                    let ib = self.emit_integer_guard(vb);
                    let ic = self.emit_integer_guard(vc);

                    // Convert to f64 and divide
                    let fb = self.builder.ins().fcvt_from_sint(types::F64, ib);
                    let fc = self.builder.ins().fcvt_from_sint(types::F64, ic);
                    let fresult = self.builder.ins().fdiv(fb, fc);

                    // Box as float TValue (floats are stored as-is, no tagging needed
                    // since their bit pattern doesn't collide with QNAN prefix)
                    let raw = self.builder.ins().bitcast(types::I64, MemFlags::new(), fresult);
                    self.emit_set_slot(a, raw);

                    pc += 1; // skip MMBin
                }

                // ---- Power (R[A] = R[B] ^ R[C]) — always produces float ----
                // Pow requires calling powf, which we can't easily do in Cranelift IR.
                // Side-exit to interpreter for now.
                OpCode::Pow => {
                    self.builder.ins().jump(self.side_exit_block, &[]);
                    block_terminated = true;
                    pc += 1; // skip MMBin
                }

                // ---- Bitwise register-register ----
                OpCode::BAnd | OpCode::BOr | OpCode::BXor | OpCode::Shl | OpCode::Shr => {
                    let b = inst.b() as i64;
                    let c = inst.c() as i64;

                    let vb = self.emit_get_slot(b);
                    let vc = self.emit_get_slot(c);

                    let ib = self.emit_integer_guard(vb);
                    let ic = self.emit_integer_guard(vc);

                    let result = match op {
                        OpCode::BAnd => self.builder.ins().band(ib, ic),
                        OpCode::BOr => self.builder.ins().bor(ib, ic),
                        OpCode::BXor => self.builder.ins().bxor(ib, ic),
                        OpCode::Shl => self.emit_lua_shl(ib, ic),
                        OpCode::Shr => self.emit_lua_shr(ib, ic),
                        _ => unreachable!(),
                    };

                    // Bitwise results always fit in 47-bit (band/bor/bxor preserve range,
                    // shifts may produce full 64-bit values but we box them)
                    let boxed = self.emit_box_integer(result);
                    self.emit_set_slot(a, boxed);

                    pc += 1; // skip MMBin
                }

                // ---- Arithmetic with constant (register + K[C]) ----
                OpCode::DivK | OpCode::IDivK | OpCode::ModK | OpCode::PowK => {
                    let b = inst.b() as i64;
                    let c = inst.c() as usize;

                    let vb = self.emit_get_slot(b);
                    let ib = self.emit_integer_guard(vb);

                    let k = &self.proto.constants[c];
                    let kval = match k {
                        Constant::Integer(i) => *i,
                        _ => {
                            self.builder.ins().jump(self.side_exit_block, &[]);
                            block_terminated = true;
                            pc += 1; // skip MMBinK
                            pc += 1;
                            continue;
                        }
                    };

                    if matches!(op, OpCode::PowK) {
                        // Pow requires powf — side exit
                        self.builder.ins().jump(self.side_exit_block, &[]);
                        block_terminated = true;
                        pc += 1;
                        pc += 1;
                        continue;
                    }

                    let kc = self.builder.ins().iconst(types::I64, kval);

                    if matches!(op, OpCode::DivK) {
                        // Float division
                        let fb = self.builder.ins().fcvt_from_sint(types::F64, ib);
                        let fc = self.builder.ins().fcvt_from_sint(types::F64, kc);
                        let fresult = self.builder.ins().fdiv(fb, fc);
                        let raw = self.builder.ins().bitcast(types::I64, MemFlags::new(), fresult);
                        self.emit_set_slot(a, raw);
                    } else {
                        // Guard: divisor != 0
                        let zero = self.builder.ins().iconst(types::I64, 0);
                        let nz = self.builder.ins().icmp(IntCC::NotEqual, kc, zero);
                        let cont = self.builder.create_block();
                        self.builder.ins().brif(nz, cont, &[], self.side_exit_block, &[]);
                        self.builder.switch_to_block(cont);
                        self.builder.seal_block(cont);

                        let result = match op {
                            OpCode::IDivK => self.emit_lua_idiv(ib, kc),
                            OpCode::ModK => self.emit_lua_imod(ib, kc),
                            _ => unreachable!(),
                        };
                        let boxed = self.emit_box_integer(result);
                        self.emit_set_slot(a, boxed);
                    }

                    pc += 1; // skip MMBinK
                }

                // ---- Bitwise with constant ----
                OpCode::BAndK | OpCode::BOrK | OpCode::BXorK => {
                    let b = inst.b() as i64;
                    let c = inst.c() as usize;

                    let vb = self.emit_get_slot(b);
                    let ib = self.emit_integer_guard(vb);

                    let k = &self.proto.constants[c];
                    let kval = match k {
                        Constant::Integer(i) => *i,
                        _ => {
                            self.builder.ins().jump(self.side_exit_block, &[]);
                            block_terminated = true;
                            pc += 1; // skip MMBinK
                            pc += 1;
                            continue;
                        }
                    };

                    let kc = self.builder.ins().iconst(types::I64, kval);
                    let result = match op {
                        OpCode::BAndK => self.builder.ins().band(ib, kc),
                        OpCode::BOrK => self.builder.ins().bor(ib, kc),
                        OpCode::BXorK => self.builder.ins().bxor(ib, kc),
                        _ => unreachable!(),
                    };

                    let boxed = self.emit_box_integer(result);
                    self.emit_set_slot(a, boxed);

                    pc += 1; // skip MMBinK
                }

                // ---- Shift with immediate (no following MMBinI) ----
                OpCode::ShrI | OpCode::ShlI => {
                    let b = inst.b() as i64;
                    let sc = inst.c() as i8 as i64;

                    let vb = self.emit_get_slot(b);
                    let ib = self.emit_integer_guard(vb);

                    let imm = self.builder.ins().iconst(types::I64, sc);
                    let result = match op {
                        OpCode::ShrI => self.emit_lua_shr(ib, imm),
                        OpCode::ShlI => self.emit_lua_shl(ib, imm),
                        _ => unreachable!(),
                    };

                    let boxed = self.emit_box_integer(result);
                    self.emit_set_slot(a, boxed);
                    // No following MMBinI to skip
                }

                // ---- Unary minus ----
                OpCode::Unm => {
                    let b = inst.b() as i64;
                    let vb = self.emit_get_slot(b);
                    let ib = self.emit_integer_guard(vb);

                    // wrapping_neg: result fits in 47-bit (magnitude ≤ |operand|)
                    let result = self.builder.ins().ineg(ib);
                    let boxed = self.emit_box_integer(result);
                    self.emit_set_slot(a, boxed);
                    // No following MM instruction
                }

                // ---- Bitwise NOT ----
                OpCode::BNot => {
                    let b = inst.b() as i64;
                    let vb = self.emit_get_slot(b);
                    let ib = self.emit_integer_guard(vb);

                    // Bitwise NOT on 64-bit integer
                    let result = self.builder.ins().bnot(ib);
                    let boxed = self.emit_box_integer(result);
                    self.emit_set_slot(a, boxed);
                    // No following MM instruction
                }

                // ---- Control flow ----

                OpCode::Jmp => {
                    let sj = inst.get_sj();
                    let target_pc = (pc as i64 + 1 + sj as i64) as usize;
                    if let Some(&target_block) = self.pc_blocks.get(&target_pc) {
                        self.builder.ins().jump(target_block, &[]);
                    } else {
                        // Jump to a PC without a block — shouldn't happen with
                        // proper pre-scan, but fall through safely
                        self.builder.ins().jump(self.side_exit_block, &[]);
                    }
                    block_terminated = true;
                }

                OpCode::Test => {
                    // if R(A).is_truthy() == k then skip next (pc += 1)
                    let k = inst.k();
                    let va = self.emit_get_slot(a);
                    let cond = self.emit_is_truthy(va, k);
                    self.emit_cond_skip(cond, pc);
                    block_terminated = true;
                }

                OpCode::TestSet => {
                    // if R(B).is_truthy() == k then skip next
                    // else R(A) = R(B)
                    let b = inst.b() as i64;
                    let k = inst.k();
                    let vb = self.emit_get_slot(b);
                    let should_skip = self.emit_is_truthy(vb, k);

                    let skip_block = self.pc_blocks.get(&(pc + 2)).copied()
                        .expect("TestSet skip target pc+2 should have a block");
                    let set_block = self.builder.create_block();

                    self.builder.ins().brif(should_skip, skip_block, &[], set_block, &[]);

                    // set_block: R(A) = R(B), then fall to pc+1
                    self.builder.switch_to_block(set_block);
                    self.builder.seal_block(set_block);
                    // Re-read vb since we're in a new block
                    let vb2 = self.emit_get_slot(b);
                    self.emit_set_slot(a, vb2);
                    let fall_block = self.pc_blocks.get(&(pc + 1)).copied()
                        .expect("TestSet fallthrough pc+1 should have a block");
                    self.builder.ins().jump(fall_block, &[]);

                    block_terminated = true;
                }

                OpCode::Not => {
                    let b = inst.b() as i64;
                    let vb = self.emit_get_slot(b);
                    // is_falsy: nil or false
                    let is_falsy = self.emit_is_falsy(vb);
                    // Convert bool to TValue: true if falsy, false if truthy
                    let true_bits = self.builder.ins().iconst(types::I64, TValue::from_bool(true).raw_bits() as i64);
                    let false_bits = self.builder.ins().iconst(types::I64, TValue::from_bool(false).raw_bits() as i64);
                    let result = self.builder.ins().select(is_falsy, true_bits, false_bits);
                    self.emit_set_slot(a, result);
                }

                // ---- Comparisons with immediate ----

                OpCode::EqI => {
                    let sb = inst.b() as i8 as i64;
                    let k = inst.k();
                    let va = self.emit_get_slot(a);
                    let ia = self.emit_integer_guard(va);
                    let imm = self.builder.ins().iconst(types::I64, sb);
                    let eq = self.builder.ins().icmp(IntCC::Equal, ia, imm);
                    // Skip if result == k (i.e., condition matches expectation)
                    let cond = if k { self.emit_bool_not(eq) } else { eq };
                    self.emit_cond_skip(cond, pc);
                    block_terminated = true;
                }

                OpCode::LtI => {
                    let sb = inst.b() as i8 as i64;
                    let k = inst.k();
                    let va = self.emit_get_slot(a);
                    let ia = self.emit_integer_guard(va);
                    let imm = self.builder.ins().iconst(types::I64, sb);
                    let lt = self.builder.ins().icmp(IntCC::SignedLessThan, ia, imm);
                    let cond = if k { self.emit_bool_not(lt) } else { lt };
                    self.emit_cond_skip(cond, pc);
                    block_terminated = true;
                }

                OpCode::LeI => {
                    let sb = inst.b() as i8 as i64;
                    let k = inst.k();
                    let va = self.emit_get_slot(a);
                    let ia = self.emit_integer_guard(va);
                    let imm = self.builder.ins().iconst(types::I64, sb);
                    let le = self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, ia, imm);
                    let cond = if k { self.emit_bool_not(le) } else { le };
                    self.emit_cond_skip(cond, pc);
                    block_terminated = true;
                }

                OpCode::GtI => {
                    let sb = inst.b() as i8 as i64;
                    let k = inst.k();
                    let va = self.emit_get_slot(a);
                    let ia = self.emit_integer_guard(va);
                    let imm = self.builder.ins().iconst(types::I64, sb);
                    let gt = self.builder.ins().icmp(IntCC::SignedGreaterThan, ia, imm);
                    let cond = if k { self.emit_bool_not(gt) } else { gt };
                    self.emit_cond_skip(cond, pc);
                    block_terminated = true;
                }

                OpCode::GeI => {
                    let sb = inst.b() as i8 as i64;
                    let k = inst.k();
                    let va = self.emit_get_slot(a);
                    let ia = self.emit_integer_guard(va);
                    let imm = self.builder.ins().iconst(types::I64, sb);
                    let ge = self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, ia, imm);
                    let cond = if k { self.emit_bool_not(ge) } else { ge };
                    self.emit_cond_skip(cond, pc);
                    block_terminated = true;
                }

                OpCode::EqK => {
                    let b = inst.b() as usize;
                    let k = inst.k();
                    // Load constant as raw bits and compare directly
                    let raw_k = self.constant_to_raw_bits(&self.proto.constants[b]);
                    let va = self.emit_get_slot(a);
                    let kval = self.builder.ins().iconst(types::I64, raw_k as i64);
                    let eq = self.builder.ins().icmp(IntCC::Equal, va, kval);
                    let cond = if k { self.emit_bool_not(eq) } else { eq };
                    self.emit_cond_skip(cond, pc);
                    block_terminated = true;
                }

                // ---- Register-register comparisons ----

                OpCode::Eq => {
                    let b = inst.b() as i64;
                    let k = inst.k();
                    let va = self.emit_get_slot(a);
                    let vb = self.emit_get_slot(b);
                    // Fast path: both must be inline integers
                    let ia = self.emit_integer_guard(va);
                    let ib = self.emit_integer_guard(vb);
                    let eq = self.builder.ins().icmp(IntCC::Equal, ia, ib);
                    let cond = if k { self.emit_bool_not(eq) } else { eq };
                    self.emit_cond_skip(cond, pc);
                    block_terminated = true;
                }

                OpCode::Lt => {
                    let b = inst.b() as i64;
                    let k = inst.k();
                    let va = self.emit_get_slot(a);
                    let vb = self.emit_get_slot(b);
                    let ia = self.emit_integer_guard(va);
                    let ib = self.emit_integer_guard(vb);
                    let lt = self.builder.ins().icmp(IntCC::SignedLessThan, ia, ib);
                    let cond = if k { self.emit_bool_not(lt) } else { lt };
                    self.emit_cond_skip(cond, pc);
                    block_terminated = true;
                }

                OpCode::Le => {
                    let b = inst.b() as i64;
                    let k = inst.k();
                    let va = self.emit_get_slot(a);
                    let vb = self.emit_get_slot(b);
                    let ia = self.emit_integer_guard(va);
                    let ib = self.emit_integer_guard(vb);
                    let le = self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, ia, ib);
                    let cond = if k { self.emit_bool_not(le) } else { le };
                    self.emit_cond_skip(cond, pc);
                    block_terminated = true;
                }

                // ---- For loops (integer fast-path only) ----

                OpCode::ForPrep => {
                    // R(A) = init, R(A+1) = limit, R(A+2) = step
                    // Integer fast-path: compute iteration count, store in R(A+1)
                    // Then jump to loop body or skip entirely
                    let v_init = self.emit_get_slot(a);
                    let v_limit = self.emit_get_slot(a + 1);
                    let v_step = self.emit_get_slot(a + 2);

                    // Guard: all three must be inline integers
                    let i_init = self.emit_integer_guard(v_init);
                    let i_limit = self.emit_integer_guard(v_limit);
                    let i_step = self.emit_integer_guard(v_step);

                    // Guard: step != 0 (side-exit)
                    let zero = self.builder.ins().iconst(types::I64, 0);
                    let step_nz = self.builder.ins().icmp(IntCC::NotEqual, i_step, zero);
                    let step_ok_block = self.builder.create_block();
                    self.builder.ins().brif(step_nz, step_ok_block, &[], self.side_exit_block, &[]);
                    self.builder.switch_to_block(step_ok_block);
                    self.builder.seal_block(step_ok_block);

                    // Check direction and compute count
                    let step_pos = self.builder.ins().icmp(IntCC::SignedGreaterThan, i_step, zero);

                    // Positive step: init <= limit → count = (limit - init) / step
                    // Negative step: init >= limit → count = (init - limit) / (-step)
                    let pos_block = self.builder.create_block();
                    let neg_block = self.builder.create_block();
                    let body_block = self.pc_blocks.get(&(pc + 1)).copied()
                        .expect("ForPrep loop body should have a block");
                    let sbx = inst.sbx();
                    // Skip target: dispatch does pc=(pc+1)+sbx; pc+=1, so target = pc+2+sbx
                    let skip_pc = (pc as i64 + 2 + sbx as i64) as usize;
                    let skip_block = self.pc_blocks.get(&skip_pc).copied()
                        .expect("ForPrep skip target should have a block");

                    self.builder.ins().brif(step_pos, pos_block, &[], neg_block, &[]);

                    // Positive step block
                    self.builder.switch_to_block(pos_block);
                    self.builder.seal_block(pos_block);
                    let pos_ok = self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, i_init, i_limit);
                    let pos_count_block = self.builder.create_block();
                    self.builder.ins().brif(pos_ok, pos_count_block, &[], skip_block, &[]);

                    self.builder.switch_to_block(pos_count_block);
                    self.builder.seal_block(pos_count_block);
                    let diff_pos = self.builder.ins().isub(i_limit, i_init);
                    let count_pos = self.builder.ins().udiv(diff_pos, i_step);
                    // Store: R(A) = init, R(A+1) = count, R(A+2) = step, R(A+3) = init
                    let boxed_init = self.emit_box_integer(i_init);
                    let boxed_count = self.emit_box_integer(count_pos);
                    let boxed_step = self.emit_box_integer(i_step);
                    self.emit_set_slot(a, boxed_init);
                    self.emit_set_slot(a + 1, boxed_count);
                    self.emit_set_slot(a + 2, boxed_step);
                    self.emit_set_slot(a + 3, boxed_init);
                    self.builder.ins().jump(body_block, &[]);

                    // Negative step block
                    self.builder.switch_to_block(neg_block);
                    self.builder.seal_block(neg_block);
                    let neg_ok = self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, i_init, i_limit);
                    let neg_count_block = self.builder.create_block();
                    self.builder.ins().brif(neg_ok, neg_count_block, &[], skip_block, &[]);

                    self.builder.switch_to_block(neg_count_block);
                    self.builder.seal_block(neg_count_block);
                    let diff_neg = self.builder.ins().isub(i_init, i_limit);
                    let neg_step = self.builder.ins().ineg(i_step);
                    let count_neg = self.builder.ins().udiv(diff_neg, neg_step);
                    let boxed_init2 = self.emit_box_integer(i_init);
                    let boxed_count2 = self.emit_box_integer(count_neg);
                    let boxed_step2 = self.emit_box_integer(i_step);
                    self.emit_set_slot(a, boxed_init2);
                    self.emit_set_slot(a + 1, boxed_count2);
                    self.emit_set_slot(a + 2, boxed_step2);
                    self.emit_set_slot(a + 3, boxed_init2);
                    self.builder.ins().jump(body_block, &[]);

                    block_terminated = true;
                }

                OpCode::ForLoop => {
                    // Integer fast-path:
                    // counter = R(A), count = R(A+1), step = R(A+2)
                    // count_u = count - 1; if count_u != u64::MAX (i.e., count > 0):
                    //   next = counter + step
                    //   R(A) = next, R(A+1) = count_u, R(A+3) = next
                    //   jump back to loop body
                    let v_counter = self.emit_get_slot(a);
                    let v_count = self.emit_get_slot(a + 1);
                    let v_step = self.emit_get_slot(a + 2);

                    let i_counter = self.emit_integer_guard(v_counter);
                    let i_count = self.emit_integer_guard(v_count);
                    let i_step = self.emit_integer_guard(v_step);

                    // Decrement count (unsigned)
                    let one = self.builder.ins().iconst(types::I64, 1);
                    let count_dec = self.builder.ins().isub(i_count, one);

                    // Check if count wrapped to u64::MAX (was 0 → loop done)
                    let neg_one = self.builder.ins().iconst(types::I64, -1i64);
                    let done = self.builder.ins().icmp(IntCC::Equal, count_dec, neg_one);

                    let sbx = inst.sbx();
                    // Dispatch does: pc = (pc+1) + sbx (sbx is negative for back-jump)
                    let loop_target_pc = (pc as i64 + 1 + sbx as i64) as usize;
                    let loop_block = self.pc_blocks.get(&loop_target_pc).copied()
                        .expect("ForLoop back-jump target should have a block");
                    let exit_pc = pc + 1;
                    let exit_block = self.pc_blocks.get(&exit_pc).copied()
                        .expect("ForLoop exit should have a block");

                    let continue_block = self.builder.create_block();
                    self.builder.ins().brif(done, exit_block, &[], continue_block, &[]);

                    self.builder.switch_to_block(continue_block);
                    self.builder.seal_block(continue_block);

                    // next = counter + step
                    let next = self.builder.ins().iadd(i_counter, i_step);
                    let boxed_next = self.emit_box_integer(next);
                    let boxed_count_dec = self.emit_box_integer(count_dec);
                    self.emit_set_slot(a, boxed_next);
                    self.emit_set_slot(a + 1, boxed_count_dec);
                    self.emit_set_slot(a + 3, boxed_next);
                    self.builder.ins().jump(loop_block, &[]);

                    block_terminated = true;
                }

                // ---- Increment 5: upvalues, table access, calls ----

                OpCode::GetUpval => {
                    let b = inst.b() as i64;
                    let upval_idx_val = self.builder.ins().iconst(types::I64, b);
                    let call = self
                        .builder
                        .ins()
                        .call(self.get_upval_ref, &[self.vm_ptr, upval_idx_val]);
                    let result = self.builder.inst_results(call)[0];
                    self.emit_set_slot(a, result);
                }

                OpCode::SetUpval => {
                    let b = inst.b() as i64;
                    let va = self.emit_get_slot(a);
                    let upval_idx_val = self.builder.ins().iconst(types::I64, b);
                    self.builder
                        .ins()
                        .call(self.set_upval_ref, &[self.vm_ptr, upval_idx_val, va]);
                }

                OpCode::GetTabUp => {
                    let b = inst.b() as i64;
                    let c = inst.c() as i64;
                    let proto_idx_val =
                        self.builder.ins().iconst(types::I64, self.proto_idx as i64);
                    let upval_b = self.builder.ins().iconst(types::I64, b);
                    let const_c = self.builder.ins().iconst(types::I64, c);
                    let call = self.builder.ins().call(
                        self.get_tab_up_ref,
                        &[self.vm_ptr, proto_idx_val, upval_b, const_c],
                    );
                    let result = self.builder.inst_results(call)[0];
                    self.emit_set_slot(a, result);
                }

                OpCode::SetTabUp => {
                    // SetTabUp: UpVal[A][K[B]] = RK(C)
                    let b = inst.b() as i64;
                    let c = inst.c() as i64;
                    let k = inst.k();
                    let proto_idx_val =
                        self.builder.ins().iconst(types::I64, self.proto_idx as i64);
                    let upval_a_val = self.builder.ins().iconst(types::I64, a);
                    let const_b_val = self.builder.ins().iconst(types::I64, b);
                    let val_or_c = self.builder.ins().iconst(types::I64, c);
                    let k_flag = self.builder.ins().iconst(types::I64, k as i64);
                    let call = self.builder.ins().call(
                        self.set_tab_up_ref,
                        &[
                            self.vm_ptr,
                            self.base,
                            proto_idx_val,
                            upval_a_val,
                            const_b_val,
                            val_or_c,
                            k_flag,
                        ],
                    );
                    let result = self.builder.inst_results(call)[0];
                    // Check for SIDE_EXIT
                    let exit_val = self.builder.ins().iconst(types::I64, SIDE_EXIT);
                    let is_exit =
                        self.builder
                            .ins()
                            .icmp(IntCC::Equal, result, exit_val);
                    let cont = self.builder.create_block();
                    self.builder
                        .ins()
                        .brif(is_exit, self.side_exit_block, &[], cont, &[]);
                    self.builder.switch_to_block(cont);
                    self.builder.seal_block(cont);
                }

                OpCode::Call => {
                    let b = inst.b() as i64;
                    let c = inst.c() as i64;
                    // b: nargs+1 (0 means use stack top)
                    // c: nresults+1 (0 means multi-return)
                    let nargs = if b > 0 { b - 1 } else { 0 };
                    let nresults = if c > 0 { c - 1 } else { -1i64 };

                    if b == 0 {
                        // Variable args (use stack top) — side-exit for now
                        self.builder.ins().jump(self.side_exit_block, &[]);
                        block_terminated = true;
                        pc += 1;
                        continue;
                    }

                    let func_off = self.builder.ins().iconst(types::I64, a);
                    let nargs_val = self.builder.ins().iconst(types::I64, nargs);
                    let nresults_val = self.builder.ins().iconst(types::I64, nresults);
                    let call = self.builder.ins().call(
                        self.call_ref,
                        &[self.vm_ptr, self.base, func_off, nargs_val, nresults_val],
                    );
                    let result = self.builder.inst_results(call)[0];
                    // Check for SIDE_EXIT
                    let exit_val = self.builder.ins().iconst(types::I64, SIDE_EXIT);
                    let is_exit =
                        self.builder
                            .ins()
                            .icmp(IntCC::Equal, result, exit_val);
                    let cont = self.builder.create_block();
                    self.builder
                        .ins()
                        .brif(is_exit, self.side_exit_block, &[], cont, &[]);
                    self.builder.switch_to_block(cont);
                    self.builder.seal_block(cont);
                }

                OpCode::Self_ => {
                    let b = inst.b() as i64;
                    let c = inst.c() as i64;
                    let k = inst.k();
                    // Get key: if k flag set, use constant; otherwise use register
                    let key = if k {
                        let raw = self
                            .constant_to_raw_bits(&self.proto.constants[c as usize]);
                        self.builder.ins().iconst(types::I64, raw as i64)
                    } else {
                        self.emit_get_slot(c)
                    };
                    let a_val = self.builder.ins().iconst(types::I64, a);
                    let b_val = self.builder.ins().iconst(types::I64, b);
                    let call = self.builder.ins().call(
                        self.self_ref,
                        &[self.vm_ptr, self.base, a_val, b_val, key],
                    );
                    let result = self.builder.inst_results(call)[0];
                    let exit_val = self.builder.ins().iconst(types::I64, SIDE_EXIT);
                    let is_exit =
                        self.builder
                            .ins()
                            .icmp(IntCC::Equal, result, exit_val);
                    let cont = self.builder.create_block();
                    self.builder
                        .ins()
                        .brif(is_exit, self.side_exit_block, &[], cont, &[]);
                    self.builder.switch_to_block(cont);
                    self.builder.seal_block(cont);
                }

                OpCode::GetTable => {
                    let b = inst.b() as i64;
                    let c = inst.c() as i64;
                    let table_val = self.emit_get_slot(b);
                    let key_val = self.emit_get_slot(c);
                    let call = self.builder.ins().call(
                        self.tbl_idx_ref,
                        &[self.vm_ptr, table_val, key_val],
                    );
                    let result = self.builder.inst_results(call)[0];
                    self.emit_set_slot(a, result);
                }

                OpCode::GetField => {
                    let b = inst.b() as i64;
                    let c = inst.c() as usize;
                    let table_val = self.emit_get_slot(b);
                    let key_raw = self
                        .constant_to_raw_bits(&self.proto.constants[c]);
                    let key_val = self.builder.ins().iconst(types::I64, key_raw as i64);
                    let call = self.builder.ins().call(
                        self.tbl_idx_ref,
                        &[self.vm_ptr, table_val, key_val],
                    );
                    let result = self.builder.inst_results(call)[0];
                    self.emit_set_slot(a, result);
                }

                OpCode::SetField => {
                    // SetField: R[A][K[B]] = RK(C)
                    let b = inst.b() as usize;
                    let c = inst.c() as usize;
                    let k = inst.k();
                    let table_val = self.emit_get_slot(a);
                    let key_raw = self
                        .constant_to_raw_bits(&self.proto.constants[b]);
                    let key_val = self.builder.ins().iconst(types::I64, key_raw as i64);
                    let val = if k {
                        let raw = self
                            .constant_to_raw_bits(&self.proto.constants[c]);
                        self.builder.ins().iconst(types::I64, raw as i64)
                    } else {
                        self.emit_get_slot(c as i64)
                    };
                    let call = self.builder.ins().call(
                        self.tbl_ni_ref,
                        &[self.vm_ptr, table_val, key_val, val],
                    );
                    let result = self.builder.inst_results(call)[0];
                    let exit_val = self.builder.ins().iconst(types::I64, SIDE_EXIT);
                    let is_exit =
                        self.builder
                            .ins()
                            .icmp(IntCC::Equal, result, exit_val);
                    let cont = self.builder.create_block();
                    self.builder
                        .ins()
                        .brif(is_exit, self.side_exit_block, &[], cont, &[]);
                    self.builder.switch_to_block(cont);
                    self.builder.seal_block(cont);
                }

                // Side-exit: complex operations handled by interpreter
                OpCode::Return | OpCode::TailCall | OpCode::Closure => {
                    self.builder.ins().jump(self.side_exit_block, &[]);
                    block_terminated = true;
                }

                // These are skipped as part of arithmetic (already incremented pc above)
                OpCode::MMBin | OpCode::MMBinI | OpCode::MMBinK => {}

                OpCode::VarArgPrep => {}

                OpCode::ExtraArg => {}

                _ => return Err(JitError::UnsupportedOpcode(op, pc)),
            }

            pc += 1;
        }

        // If we fall off the end without a return, emit one.
        if !block_terminated {
            let zero = self.builder.ins().iconst(types::I64, 0);
            self.builder.ins().return_(&[zero]);
        }

        Ok(())
    }

    /// Emit Lua floor division: a // b
    /// Semantics: d = wrapping_div(a, b); r = wrapping_rem(a, b);
    /// if r != 0 && (r ^ b) < 0 then d - 1 else d
    fn emit_lua_idiv(&mut self, a: Value, b: Value) -> Value {
        let d = self.builder.ins().sdiv(a, b);
        let r = self.builder.ins().srem(a, b);

        let zero = self.builder.ins().iconst(types::I64, 0);
        let r_nonzero = self.builder.ins().icmp(IntCC::NotEqual, r, zero);
        let xor = self.builder.ins().bxor(r, b);
        let signs_differ = self.builder.ins().icmp(IntCC::SignedLessThan, xor, zero);
        let need_adjust = self.builder.ins().band(r_nonzero, signs_differ);

        let one = self.builder.ins().iconst(types::I64, 1);
        let d_minus_1 = self.builder.ins().isub(d, one);
        self.builder.ins().select(need_adjust, d_minus_1, d)
    }

    /// Emit Lua modulo: a % b (result sign matches divisor)
    /// Semantics: r = wrapping_rem(a, b);
    /// if r != 0 && (r ^ b) < 0 then r + b else r
    fn emit_lua_imod(&mut self, a: Value, b: Value) -> Value {
        let r = self.builder.ins().srem(a, b);

        let zero = self.builder.ins().iconst(types::I64, 0);
        let r_nonzero = self.builder.ins().icmp(IntCC::NotEqual, r, zero);
        let xor = self.builder.ins().bxor(r, b);
        let signs_differ = self.builder.ins().icmp(IntCC::SignedLessThan, xor, zero);
        let need_adjust = self.builder.ins().band(r_nonzero, signs_differ);

        let r_plus_b = self.builder.ins().iadd(r, b);
        self.builder.ins().select(need_adjust, r_plus_b, r)
    }

    /// Emit Lua left shift: a << b (unsigned shift, range-clamped)
    /// Semantics: if b >= 64 || b <= -64 then 0
    ///            elif b < 0 then shr(a, -b)
    ///            else (a as u64).wrapping_shl(b as u32) as i64
    fn emit_lua_shl(&mut self, a: Value, b: Value) -> Value {
        let zero = self.builder.ins().iconst(types::I64, 0);
        let sixty_four = self.builder.ins().iconst(types::I64, 64);
        let neg_sixty_four = self.builder.ins().iconst(types::I64, -64);

        // Check b >= 64 || b <= -64
        let b_ge_64 = self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, b, sixty_four);
        let b_le_neg64 = self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, b, neg_sixty_four);
        let out_of_range = self.builder.ins().bor(b_ge_64, b_le_neg64);

        // Check b < 0
        let b_neg = self.builder.ins().icmp(IntCC::SignedLessThan, b, zero);

        // Compute both paths
        let neg_b = self.builder.ins().ineg(b);
        let shr_result = self.builder.ins().ushr(a, neg_b); // unsigned shift right
        let shl_result = self.builder.ins().ishl(a, b);       // shift left

        // Select: if b < 0 then shr else shl
        let shift_result = self.builder.ins().select(b_neg, shr_result, shl_result);
        // If out of range, result is 0
        self.builder.ins().select(out_of_range, zero, shift_result)
    }

    /// Emit Lua right shift: a >> b (unsigned shift, range-clamped)
    /// Semantics: if b >= 64 || b <= -64 then 0
    ///            elif b < 0 then shl(a, -b)
    ///            else (a as u64).wrapping_shr(b as u32) as i64
    fn emit_lua_shr(&mut self, a: Value, b: Value) -> Value {
        let zero = self.builder.ins().iconst(types::I64, 0);
        let sixty_four = self.builder.ins().iconst(types::I64, 64);
        let neg_sixty_four = self.builder.ins().iconst(types::I64, -64);

        // Check b >= 64 || b <= -64
        let b_ge_64 = self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, b, sixty_four);
        let b_le_neg64 = self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, b, neg_sixty_four);
        let out_of_range = self.builder.ins().bor(b_ge_64, b_le_neg64);

        // Check b < 0
        let b_neg = self.builder.ins().icmp(IntCC::SignedLessThan, b, zero);

        // Compute both paths
        let neg_b = self.builder.ins().ineg(b);
        let shl_result = self.builder.ins().ishl(a, neg_b);   // shift left
        let shr_result = self.builder.ins().ushr(a, b);       // unsigned shift right

        // Select: if b < 0 then shl else shr
        let shift_result = self.builder.ins().select(b_neg, shl_result, shr_result);
        // If out of range, result is 0
        self.builder.ins().select(out_of_range, zero, shift_result)
    }

    /// Emit a check for truthiness: returns a Cranelift i8 value that is 1
    /// if `(is_truthy(val) == k)`, 0 otherwise.
    /// Truthy = not nil and not false.
    fn emit_is_truthy(&mut self, val: Value, k: bool) -> Value {
        let is_falsy = self.emit_is_falsy(val);
        // Interpreter: if is_truthy() == k { skip }
        // is_truthy = !is_falsy
        if k {
            // k=true: skip when truthy → condition = !is_falsy
            self.emit_bool_not(is_falsy)
        } else {
            // k=false: skip when falsy → condition = is_falsy
            is_falsy
        }
    }

    /// Emit a check for falsiness: returns 1 if val is nil or false, 0 otherwise.
    fn emit_is_falsy(&mut self, val: Value) -> Value {
        // nil = 0x7FF8_0000_0000_0002
        // false = 0x7FF8_0002_0000_0000
        // Both are "tagged" (have QNAN prefix with tag bits set).
        // A value is falsy if it equals nil OR equals false.
        let nil_bits = self.builder.ins().iconst(types::I64, TValue::nil().raw_bits() as i64);
        let false_bits = self.builder.ins().iconst(types::I64, TValue::from_bool(false).raw_bits() as i64);
        let is_nil = self.builder.ins().icmp(IntCC::Equal, val, nil_bits);
        let is_false = self.builder.ins().icmp(IntCC::Equal, val, false_bits);
        self.builder.ins().bor(is_nil, is_false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use selune_compiler::compiler::compile;
    use selune_core::value::TValue;
    use selune_vm::vm::Vm;

    /// Helper: compile Lua source, extract the main proto, then JIT-compile it.
    fn compile_and_jit(source: &str) -> Result<(JitFunction, JitCompiler), JitError> {
        let (proto, _strings) = compile(source.as_bytes(), "test").unwrap();
        let mut compiler = JitCompiler::new()?;
        let mut gc = GcHeap::new();
        let func = compiler.compile_proto(&proto, &mut gc, 0)?;
        Ok((func, compiler))
    }

    /// Helper: compile Lua, JIT it, run it, and return the result at stack[base].
    fn jit_eval_one(source: &str) -> TValue {
        let (func, _compiler) = compile_and_jit(source).unwrap();
        let mut vm = Vm::new();
        vm.stack.resize(256, TValue::nil());
        let base = 0;
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };
        assert!(nresults >= 1, "expected at least 1 result, got {nresults}");
        vm.stack[base]
    }

    // --- Increment 1 tests (preserved) ---

    #[test]
    fn test_jit_compiler_creation() {
        let compiler = JitCompiler::new();
        assert!(
            compiler.is_ok(),
            "JitCompiler should initialize on this platform"
        );
    }

    #[test]
    fn test_jit_return_42() {
        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_return_constant(42).unwrap();

        let mut vm = Vm::new();
        let result = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(result, 42);
    }

    #[test]
    fn test_jit_return_negative() {
        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_return_constant(-1).unwrap();

        let mut vm = Vm::new();
        let result = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(result, -1);
    }

    #[test]
    fn test_jit_return_zero() {
        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_return_constant(0).unwrap();

        let mut vm = Vm::new();
        let result = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(result, 0);
    }

    #[test]
    fn test_jit_return_tvalue_integer() {
        let mut compiler = JitCompiler::new().unwrap();
        let tval = TValue::from_integer(42);
        let func = compiler.compile_return_tvalue(tval.raw_bits()).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(10, TValue::nil());
        let base = 2;

        let nresults = unsafe { func(&mut vm as *mut Vm, base) };
        assert_eq!(nresults, 1);

        let result = vm.stack[base];
        assert!(result.is_integer());
        assert_eq!(result.as_integer(), Some(42));
    }

    #[test]
    fn test_jit_return_tvalue_float() {
        let mut compiler = JitCompiler::new().unwrap();
        let tval = TValue::from_float(3.14);
        let func = compiler.compile_return_tvalue(tval.raw_bits()).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(10, TValue::nil());
        let base = 0;

        let nresults = unsafe { func(&mut vm as *mut Vm, base) };
        assert_eq!(nresults, 1);

        let result = vm.stack[base];
        assert_eq!(result.as_float(), Some(3.14));
    }

    #[test]
    fn test_jit_return_tvalue_nil() {
        let mut compiler = JitCompiler::new().unwrap();
        let tval = TValue::nil();
        let func = compiler.compile_return_tvalue(tval.raw_bits()).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(10, TValue::from_integer(999));
        let base = 3;

        let nresults = unsafe { func(&mut vm as *mut Vm, base) };
        assert_eq!(nresults, 1);

        let result = vm.stack[base];
        assert!(result.is_nil());
    }

    #[test]
    fn test_jit_return_tvalue_bool_true() {
        let mut compiler = JitCompiler::new().unwrap();
        let tval = TValue::from_bool(true);
        let func = compiler.compile_return_tvalue(tval.raw_bits()).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(10, TValue::nil());

        let nresults = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_bool(), Some(true));
    }

    #[test]
    fn test_jit_return_tvalue_bool_false() {
        let mut compiler = JitCompiler::new().unwrap();
        let tval = TValue::from_bool(false);
        let func = compiler.compile_return_tvalue(tval.raw_bits()).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(10, TValue::nil());

        let nresults = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_bool(), Some(false));
    }

    #[test]
    fn test_jit_multiple_functions() {
        let mut compiler = JitCompiler::new().unwrap();

        let f1 = compiler.compile_return_constant(10).unwrap();
        let f2 = compiler.compile_return_constant(20).unwrap();
        let f3 = compiler.compile_return_constant(30).unwrap();

        let mut vm = Vm::new();
        assert_eq!(unsafe { f1(&mut vm as *mut Vm, 0) }, 10);
        assert_eq!(unsafe { f2(&mut vm as *mut Vm, 0) }, 20);
        assert_eq!(unsafe { f3(&mut vm as *mut Vm, 0) }, 30);
    }

    #[test]
    fn test_jit_write_to_stack() {
        let mut compiler = JitCompiler::new().unwrap();
        let tval = TValue::from_integer(12345);
        let func = compiler.compile_return_tvalue(tval.raw_bits()).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(20, TValue::nil());

        let base = 7;
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };
        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[7].as_integer(), Some(12345));

        assert!(vm.stack[6].is_nil());
        assert!(vm.stack[8].is_nil());
    }

    #[test]
    fn test_jit_stack_auto_resize() {
        let mut compiler = JitCompiler::new().unwrap();
        let tval = TValue::from_integer(77);
        let func = compiler.compile_return_tvalue(tval.raw_bits()).unwrap();

        let mut vm = Vm::new();
        vm.stack.clear();

        let base = 5;
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };
        assert_eq!(nresults, 1);
        assert!(vm.stack.len() > base);
        assert_eq!(vm.stack[base].as_integer(), Some(77));
    }

    // --- Increment 2 tests: bytecode translation ---

    #[test]
    fn test_proto_return_integer() {
        // `return 42` compiles to: LoadI R0 42; Return1 R0
        let result = jit_eval_one("return 42");
        assert_eq!(result.as_integer(), Some(42));
    }

    #[test]
    fn test_proto_return_negative_integer() {
        let result = jit_eval_one("return -7");
        // -7 could be LoadI or Unm(LoadI 7), check what the compiler generates
        // If it's a constant fold, it's LoadI -7; Return1
        assert_eq!(result.as_integer(), Some(-7));
    }

    #[test]
    fn test_proto_return_float() {
        let result = jit_eval_one("return 3.14");
        assert_eq!(result.as_float(), Some(3.14));
    }

    #[test]
    fn test_proto_return_true() {
        let result = jit_eval_one("return true");
        assert_eq!(result.as_bool(), Some(true));
    }

    #[test]
    fn test_proto_return_false() {
        let result = jit_eval_one("return false");
        assert_eq!(result.as_bool(), Some(false));
    }

    #[test]
    fn test_proto_return_nil() {
        let result = jit_eval_one("return nil");
        assert!(result.is_nil());
    }

    #[test]
    fn test_proto_return_string_constant() {
        // "hello" is a string constant — LoadK with a string constant
        let (proto, _strings) = compile(b"return \"hello\"", "test").unwrap();
        let mut compiler = JitCompiler::new().unwrap();
        let mut gc = GcHeap::new();
        let func = compiler.compile_proto(&proto, &mut gc, 0).unwrap();

        let mut vm = Vm::new();
        // We need to transfer the string interner from compilation
        // For now, just verify the function compiles and returns 1 result
        vm.stack.resize(256, TValue::nil());
        let nresults = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(nresults, 1);
        // The string TValue has the right GC sub-tag
        let result = vm.stack[0];
        assert!(result.is_string());
    }

    #[test]
    fn test_proto_add_integers() {
        // `return 10 + 20` — compiler should constant-fold to LoadI 30
        // But in case it doesn't: LoadI R0 10; LoadI R1 20; Add R0 R0 R1; Return1 R0
        let result = jit_eval_one("return 10 + 20");
        assert_eq!(result.as_integer(), Some(30));
    }

    #[test]
    fn test_proto_sub_integers() {
        let result = jit_eval_one("return 50 - 17");
        assert_eq!(result.as_integer(), Some(33));
    }

    #[test]
    fn test_proto_mul_integers() {
        let result = jit_eval_one("return 6 * 7");
        assert_eq!(result.as_integer(), Some(42));
    }

    #[test]
    fn test_proto_complex_arithmetic() {
        // Multiple operations
        let result = jit_eval_one("return 2 + 3 * 4");
        assert_eq!(result.as_integer(), Some(14));
    }

    #[test]
    fn test_proto_addi_immediate() {
        // local x = 10; return x + 1
        // Compiler typically generates: LoadI R0 10; AddI R1 R0 1; Return1 R1
        let result = jit_eval_one("local x = 10; return x + 1");
        assert_eq!(result.as_integer(), Some(11));
    }

    #[test]
    fn test_proto_return0_empty() {
        // Empty function returns 0 results
        let (func, _compiler) = compile_and_jit("return").unwrap();
        let mut vm = Vm::new();
        vm.stack.resize(256, TValue::nil());
        let nresults = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(nresults, 0);
    }

    #[test]
    fn test_proto_loadnil() {
        // `local a, b, c` generates LoadNil
        let result = jit_eval_one("local a, b, c; return a");
        assert!(result.is_nil());
    }

    #[test]
    fn test_proto_move() {
        // `local a = 42; local b = a; return b` generates Move
        let result = jit_eval_one("local a = 42; local b = a; return b");
        assert_eq!(result.as_integer(), Some(42));
    }

    #[test]
    fn test_proto_side_exit_on_float_add() {
        // `return 1.5 + 2.5` — floats will fail the integer type guard → side exit
        let (proto, _strings) = compile(b"local a = 1.5; local b = 2.5; return a + b", "test").unwrap();
        let mut compiler = JitCompiler::new().unwrap();
        let mut gc = GcHeap::new();
        let func = compiler.compile_proto(&proto, &mut gc, 0).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(256, TValue::nil());
        let nresults = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(nresults, SIDE_EXIT, "float arithmetic should trigger side exit");
    }

    #[test]
    fn test_proto_unsupported_opcode() {
        // `return "a" .. "b"` uses Concat which we don't support yet
        let (proto, _strings) =
            compile(b"local a = \"x\"; local b = \"y\"; return a .. b", "test").unwrap();
        let mut compiler = JitCompiler::new().unwrap();
        let mut gc = GcHeap::new();
        let result = compiler.compile_proto(&proto, &mut gc, 0);
        assert!(
            matches!(result, Err(JitError::UnsupportedOpcode(_, _))),
            "should fail on unsupported opcode, got: {result:?}"
        );
    }

    #[test]
    fn test_proto_with_base_offset() {
        // Run JIT function with non-zero base to verify register addressing
        let (func, _compiler) = compile_and_jit("return 99").unwrap();
        let mut vm = Vm::new();
        vm.stack.resize(256, TValue::nil());
        let base = 10;
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };
        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[base].as_integer(), Some(99));
    }

    // --- Increment 3 tests: control flow ---

    #[test]
    fn test_proto_if_then_return() {
        // `local x = 10; if x > 5 then return 1 end; return 2`
        let result = jit_eval_one("local x = 10; if x > 5 then return 1 end; return 2");
        assert_eq!(result.as_integer(), Some(1));
    }

    #[test]
    fn test_proto_if_then_else() {
        let result = jit_eval_one("local x = 3; if x > 5 then return 1 else return 2 end");
        assert_eq!(result.as_integer(), Some(2));
    }

    #[test]
    fn test_proto_if_eq() {
        let result = jit_eval_one("local x = 5; if x == 5 then return 1 end; return 0");
        assert_eq!(result.as_integer(), Some(1));
    }

    #[test]
    fn test_proto_if_neq() {
        let result = jit_eval_one("local x = 3; if x == 5 then return 1 end; return 0");
        assert_eq!(result.as_integer(), Some(0));
    }

    #[test]
    fn test_proto_if_lt() {
        let result = jit_eval_one("local x = 3; if x < 5 then return 1 end; return 0");
        assert_eq!(result.as_integer(), Some(1));
    }

    #[test]
    fn test_proto_if_le() {
        let result = jit_eval_one("local x = 5; if x <= 5 then return 1 end; return 0");
        assert_eq!(result.as_integer(), Some(1));
    }

    #[test]
    fn test_proto_if_ge() {
        let result = jit_eval_one("local x = 7; if x >= 5 then return 1 end; return 0");
        assert_eq!(result.as_integer(), Some(1));
    }

    #[test]
    fn test_proto_not_true() {
        let result = jit_eval_one("local x = true; return not x");
        assert_eq!(result.as_bool(), Some(false));
    }

    #[test]
    fn test_proto_not_false() {
        let result = jit_eval_one("local x = false; return not x");
        assert_eq!(result.as_bool(), Some(true));
    }

    #[test]
    fn test_proto_not_nil() {
        let result = jit_eval_one("local x = nil; return not x");
        assert_eq!(result.as_bool(), Some(true));
    }

    #[test]
    fn test_proto_not_integer() {
        let result = jit_eval_one("local x = 42; return not x");
        assert_eq!(result.as_bool(), Some(false));
    }

    #[test]
    fn test_proto_and_short_circuit() {
        // `1 and 2` evaluates to 2 (left is truthy, return right)
        let result = jit_eval_one("local a = 1; local b = 2; return a and b");
        assert_eq!(result.as_integer(), Some(2));
    }

    #[test]
    fn test_proto_and_short_circuit_false() {
        // `false and 2` evaluates to false (left is falsy, return left)
        let result = jit_eval_one("local a = false; local b = 2; return a and b");
        assert_eq!(result.as_bool(), Some(false));
    }

    #[test]
    fn test_proto_or_short_circuit() {
        // `false or 2` evaluates to 2 (left is falsy, return right)
        let result = jit_eval_one("local a = false; local b = 2; return a or b");
        assert_eq!(result.as_integer(), Some(2));
    }

    #[test]
    fn test_proto_or_short_circuit_truthy() {
        // `1 or 2` evaluates to 1 (left is truthy, return left)
        let result = jit_eval_one("local a = 1; local b = 2; return a or b");
        assert_eq!(result.as_integer(), Some(1));
    }

    #[test]
    fn test_proto_for_loop_sum() {
        // Sum 1..10
        let result = jit_eval_one(
            "local s = 0; for i = 1, 10 do s = s + i end; return s"
        );
        assert_eq!(result.as_integer(), Some(55));
    }

    #[test]
    fn test_proto_for_loop_step() {
        // Sum even numbers 2..10
        let result = jit_eval_one(
            "local s = 0; for i = 2, 10, 2 do s = s + i end; return s"
        );
        assert_eq!(result.as_integer(), Some(30));
    }

    #[test]
    fn test_proto_for_loop_negative_step() {
        // Count down from 5 to 1
        let result = jit_eval_one(
            "local s = 0; for i = 5, 1, -1 do s = s + i end; return s"
        );
        assert_eq!(result.as_integer(), Some(15));
    }

    #[test]
    fn test_proto_for_loop_skip() {
        // Loop with impossible range should not execute
        let result = jit_eval_one(
            "local s = 99; for i = 10, 1 do s = 0 end; return s"
        );
        assert_eq!(result.as_integer(), Some(99));
    }

    #[test]
    fn test_proto_while_loop() {
        // While loop summing
        let result = jit_eval_one(
            "local s = 0; local i = 1; while i <= 10 do s = s + i; i = i + 1 end; return s"
        );
        assert_eq!(result.as_integer(), Some(55));
    }

    #[test]
    fn test_proto_nested_if() {
        let result = jit_eval_one(
            "local x = 10; if x > 0 then if x > 5 then return 2 else return 1 end end; return 0"
        );
        assert_eq!(result.as_integer(), Some(2));
    }

    #[test]
    fn test_proto_comparison_side_exit() {
        // Float comparison should trigger side exit
        let (proto, _strings) = compile(
            b"local x = 1.5; if x > 1 then return 1 end; return 0",
            "test",
        ).unwrap();
        let mut compiler = JitCompiler::new().unwrap();
        let mut gc = GcHeap::new();
        let func = compiler.compile_proto(&proto, &mut gc, 0).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(256, TValue::nil());
        let nresults = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(nresults, SIDE_EXIT, "float comparison should trigger side exit");
    }

    // --- Increment 4 tests: more arithmetic opcodes ---

    #[test]
    fn test_proto_idiv() {
        let result = jit_eval_one("local a = 7; local b = 2; return a // b");
        assert_eq!(result.as_integer(), Some(3));
    }

    #[test]
    fn test_proto_idiv_negative() {
        // Floor division: -7 // 2 = -4 (rounds toward negative infinity)
        let result = jit_eval_one("local a = -7; local b = 2; return a // b");
        assert_eq!(result.as_integer(), Some(-4));
    }

    #[test]
    fn test_proto_idiv_exact() {
        let result = jit_eval_one("local a = 10; local b = 5; return a // b");
        assert_eq!(result.as_integer(), Some(2));
    }

    #[test]
    fn test_proto_mod() {
        let result = jit_eval_one("local a = 7; local b = 3; return a % b");
        assert_eq!(result.as_integer(), Some(1));
    }

    #[test]
    fn test_proto_mod_negative() {
        // Lua mod: sign matches divisor. -7 % 3 = 2 (not -1)
        let result = jit_eval_one("local a = -7; local b = 3; return a % b");
        assert_eq!(result.as_integer(), Some(2));
    }

    #[test]
    fn test_proto_mod_negative_divisor() {
        // 7 % -3 = -2 (sign matches divisor)
        let result = jit_eval_one("local a = 7; local b = -3; return a % b");
        assert_eq!(result.as_integer(), Some(-2));
    }

    #[test]
    fn test_proto_div_float_result() {
        // Float division always produces float
        let result = jit_eval_one("local a = 7; local b = 2; return a / b");
        assert_eq!(result.as_float(), Some(3.5));
    }

    #[test]
    fn test_proto_div_exact() {
        let result = jit_eval_one("local a = 10; local b = 5; return a / b");
        assert_eq!(result.as_float(), Some(2.0));
    }

    #[test]
    fn test_proto_band() {
        let result = jit_eval_one("local a = 0xFF; local b = 0x0F; return a & b");
        assert_eq!(result.as_integer(), Some(0x0F));
    }

    #[test]
    fn test_proto_bor() {
        let result = jit_eval_one("local a = 0xF0; local b = 0x0F; return a | b");
        assert_eq!(result.as_integer(), Some(0xFF));
    }

    #[test]
    fn test_proto_bxor() {
        let result = jit_eval_one("local a = 0xFF; local b = 0x0F; return a ~ b");
        assert_eq!(result.as_integer(), Some(0xF0));
    }

    #[test]
    fn test_proto_shl() {
        let result = jit_eval_one("local a = 1; local b = 4; return a << b");
        assert_eq!(result.as_integer(), Some(16));
    }

    #[test]
    fn test_proto_shr() {
        let result = jit_eval_one("local a = 16; local b = 2; return a >> b");
        assert_eq!(result.as_integer(), Some(4));
    }

    #[test]
    fn test_proto_shl_large_shift() {
        // Shift >= 64 produces 0
        let result = jit_eval_one("local a = 1; local b = 64; return a << b");
        assert_eq!(result.as_integer(), Some(0));
    }

    #[test]
    fn test_proto_shr_negative_shift() {
        // Negative shift: right shift by -2 = left shift by 2
        let result = jit_eval_one("local a = 4; local b = -2; return a >> b");
        assert_eq!(result.as_integer(), Some(16));
    }

    #[test]
    fn test_proto_unm() {
        let result = jit_eval_one("local a = 42; return -a");
        assert_eq!(result.as_integer(), Some(-42));
    }

    #[test]
    fn test_proto_unm_negative() {
        let result = jit_eval_one("local a = -10; return -a");
        assert_eq!(result.as_integer(), Some(10));
    }

    #[test]
    fn test_proto_bnot() {
        // ~0 = -1, ~-1 = 0
        let result = jit_eval_one("local a = 0; return ~a");
        assert_eq!(result.as_integer(), Some(-1));
    }

    #[test]
    fn test_proto_bnot_neg() {
        let result = jit_eval_one("local a = -1; return ~a");
        assert_eq!(result.as_integer(), Some(0));
    }

    #[test]
    fn test_proto_pow_side_exit() {
        // Pow should side-exit (we can't call powf from JIT)
        let (proto, _strings) = compile(
            b"local a = 2; local b = 3; return a ^ b",
            "test",
        ).unwrap();
        let mut compiler = JitCompiler::new().unwrap();
        let mut gc = GcHeap::new();
        let func = compiler.compile_proto(&proto, &mut gc, 0).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(256, TValue::nil());
        let nresults = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(nresults, SIDE_EXIT, "pow should trigger side exit");
    }

    #[test]
    fn test_proto_idivk() {
        // `x // 3` where 3 is a constant
        let result = jit_eval_one("local x = 10; return x // 3");
        assert_eq!(result.as_integer(), Some(3));
    }

    #[test]
    fn test_proto_modk() {
        let result = jit_eval_one("local x = 10; return x % 3");
        assert_eq!(result.as_integer(), Some(1));
    }

    #[test]
    fn test_proto_divk() {
        let result = jit_eval_one("local x = 7; return x / 2");
        assert_eq!(result.as_float(), Some(3.5));
    }

    #[test]
    fn test_proto_bandk() {
        let result = jit_eval_one("local x = 0xFF; return x & 0x0F");
        assert_eq!(result.as_integer(), Some(0x0F));
    }

    #[test]
    fn test_proto_bork() {
        let result = jit_eval_one("local x = 0xF0; return x | 0x0F");
        assert_eq!(result.as_integer(), Some(0xFF));
    }

    #[test]
    fn test_proto_bxork() {
        let result = jit_eval_one("local x = 0xFF; return x ~ 0x0F");
        assert_eq!(result.as_integer(), Some(0xF0));
    }

    #[test]
    fn test_proto_combined_arithmetic() {
        // Mix of operations
        let result = jit_eval_one(
            "local a = 20; local b = 3; return (a // b) + (a % b)"
        );
        // 20 // 3 = 6, 20 % 3 = 2, 6 + 2 = 8
        assert_eq!(result.as_integer(), Some(8));
    }

    #[test]
    fn test_proto_for_loop_with_idiv() {
        // Use idiv inside a for loop
        let result = jit_eval_one(
            "local s = 0; for i = 1, 10 do s = s + i // 2 end; return s"
        );
        // 0+1+1+2+2+3+3+4+4+5 = 25
        assert_eq!(result.as_integer(), Some(25));
    }

    // --- Increment 5 tests: function calls, upvalues, table access ---

    use selune_core::gc::UpValLocation;
    use selune_vm::callinfo::CallInfo;
    use selune_vm::metamethod::MetamethodNames;

    /// Helper: set up a full VM from source, store protos, create _ENV + closure + call frame,
    /// then JIT-compile the main proto and run the JIT function.
    /// Returns the TValue at stack[base] after execution.
    fn jit_eval_with_vm(source: &str) -> (Vm, i64) {
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        // Store protos (flattens children into vm.protos)
        vm.protos.clear();
        let main_proto_idx = {
            let idx = vm.protos.len();
            vm.protos.push(proto.clone());
            let num_children = vm.protos[idx].protos.len();
            let mut flat_indices = Vec::with_capacity(num_children);
            for i in 0..num_children {
                let child = vm.protos[idx].protos[i].clone();
                let child_idx = vm.protos.len();
                vm.protos.push(child);
                flat_indices.push(child_idx);
            }
            vm.protos[idx].child_flat_indices = flat_indices;
            idx
        };

        // Create _ENV table
        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        // Create _ENV upvalue and main closure
        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        // Push call frame
        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        // JIT compile
        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();

        // Run JIT function
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        // Pop call frame
        vm.call_stack.pop();

        (vm, nresults)
    }

    #[test]
    fn test_proto_closure_side_exit() {
        // `local function f() end` uses Closure opcode → side exit
        let source = "local function f() end; return 1";
        let (proto, _strings) = compile(source.as_bytes(), "test").unwrap();
        let mut compiler = JitCompiler::new().unwrap();
        let mut gc = GcHeap::new();
        let func = compiler.compile_proto(&proto, &mut gc, 0).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(256, TValue::nil());
        let nresults = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(nresults, SIDE_EXIT, "Closure opcode should trigger side exit");
    }

    #[test]
    fn test_proto_return_general_side_exit() {
        // `return 1, 2, 3` uses general Return opcode → side exit
        let (proto, _strings) = compile(b"return 1, 2, 3", "test").unwrap();
        let mut compiler = JitCompiler::new().unwrap();
        let mut gc = GcHeap::new();
        let func = compiler.compile_proto(&proto, &mut gc, 0).unwrap();

        let mut vm = Vm::new();
        vm.stack.resize(256, TValue::nil());
        let nresults = unsafe { func(&mut vm as *mut Vm, 0) };
        assert_eq!(nresults, SIDE_EXIT, "general Return should trigger side exit");
    }

    #[test]
    fn test_proto_get_tab_up() {
        // `return x` where x is a global reads _ENV["x"] via GetTabUp
        let (vm, nresults) = jit_eval_with_vm("return 42");
        // This doesn't use GetTabUp, just verifies basic setup works
        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(42));
    }

    #[test]
    fn test_proto_get_tab_up_global() {
        // Set a global in _ENV, then read it via GetTabUp
        let source = "return x";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        // Create _ENV table with x = 99
        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        let key_x = vm.strings.intern(b"x");
        let key_tv = TValue::from_string_id(key_x);
        vm.gc.table_raw_set(env_idx, key_tv, TValue::from_integer(99)).unwrap();

        // Create closure with _ENV upvalue
        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(99));
    }

    #[test]
    fn test_proto_set_tab_up_global() {
        // `x = 42` writes to _ENV via SetTabUp
        let source = "x = 42";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert!(nresults >= 0, "SetTabUp should succeed, got {nresults}");

        // Verify x was set in _ENV
        let key_x = vm.strings.intern(b"x");
        let key_tv = TValue::from_string_id(key_x);
        let stored = vm.gc.table_raw_get(env_idx, key_tv);
        assert_eq!(stored.as_integer(), Some(42));
    }

    #[test]
    fn test_proto_get_upval() {
        // A function that reads a captured upvalue
        // `local x = 42; local function f() return x end; return f()`
        // This is complex — the inner function reads upvalue x.
        // Instead, test with a simpler case: the main proto's upvalue is _ENV,
        // which we set up. GetUpval reads upvalue 0.
        // We can use: `local _ = _ENV` which does GetUpval 0 → Move to local.
        // Actually, let's test a clear upvalue scenario by creating a manual upvalue.

        // Create a proto that uses GetUpval: `return x` where x is an upvalue
        // Actually, the simplest test is to just call GetTabUp which internally
        // does GetUpval (for _ENV). Let me test with a direct upvalue.

        // Build a simple function with a captured upvalue manually:
        // The Lua code `do local x = 42; return function() return x end end`
        // produces a child proto with GetUpval. But we can't easily JIT just the
        // child proto without a full setup.

        // Simpler: use GetUpval opcode directly in a main proto.
        // `return _ENV` would be GetUpval R0 0; Return1 R0
        let source = "local e = _ENV; return 42";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        // The function reads _ENV into a local, then returns 42
        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(42));
    }

    #[test]
    fn test_proto_set_upval() {
        // `_ENV = _ENV` does GetUpval then SetUpval on upvalue 0
        // Actually SetUpval is R[A] -> UpVal[B]. Let's find a pattern...
        // For a direct test: the simplest is to check that SetUpval doesn't crash.
        // `_ENV = {}` would use NewTable which isn't supported.
        // Let's try `_ENV = _ENV` which should be GetUpval + SetUpval (no-op).
        // Actually the compiler likely optimizes this away. Let me check.
        // `local e = _ENV; _ENV = e` would be: GetUpval R0 0; SetUpval 0 R0
        // Wait, SetUpval encoding is: UpVal[A] = R[B], so it's SetUpval A=0 B=0.
        // This might get optimized. Let's use a different approach.
        // We'll just verify the JIT compiles and runs without crashing.
        let source = "local e = _ENV; _ENV = e; return 42";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(42));
    }

    #[test]
    fn test_proto_call_simple() {
        // Call a function and return the result
        // Use `local r = f(); return r` to avoid TailCall optimization
        let source = "local r = f(); return r";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        // Register a native function "f" that returns 99
        let f_idx = vm.gc.alloc_native(|_ctx| {
            Ok(vec![TValue::from_integer(99)])
        }, "f");
        let f_val = TValue::from_native(f_idx);
        let key_f = vm.strings.intern(b"f");
        let key_f_tv = TValue::from_string_id(key_f);
        vm.gc.table_raw_set(env_idx, key_f_tv, f_val).unwrap();

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(99));
    }

    #[test]
    fn test_proto_call_with_args() {
        // Call with arguments: `local r = f(10, 20); return r` (avoids TailCall)
        let source = "local r = f(10, 20); return r";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        // f(a, b) returns a + b
        let f_idx = vm.gc.alloc_native(|ctx| {
            let a = ctx.args.get(0).copied().unwrap_or(TValue::nil());
            let b = ctx.args.get(1).copied().unwrap_or(TValue::nil());
            let sum = a.as_integer().unwrap_or(0) + b.as_integer().unwrap_or(0);
            Ok(vec![TValue::from_integer(sum)])
        }, "f");
        let f_val = TValue::from_native(f_idx);
        let key_f = vm.strings.intern(b"f");
        let key_f_tv = TValue::from_string_id(key_f);
        vm.gc.table_raw_set(env_idx, key_f_tv, f_val).unwrap();

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(30));
    }

    #[test]
    fn test_proto_call_results() {
        // Call discarding results: `f(); return 1`
        let source = "f(); return 1";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        // f() returns nothing (side-effect only)
        let f_idx = vm.gc.alloc_native(|_ctx| {
            Ok(vec![])
        }, "f");
        let f_val = TValue::from_native(f_idx);
        let key_f = vm.strings.intern(b"f");
        let key_f_tv = TValue::from_string_id(key_f);
        vm.gc.table_raw_set(env_idx, key_f_tv, f_val).unwrap();

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(1));
    }

    #[test]
    fn test_proto_get_field() {
        // `t.name` uses GetField
        let source = "return t.x";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        // Create table t with t.x = 77
        let t_idx = vm.gc.alloc_table(0, 4);
        let key_x = vm.strings.intern(b"x");
        let key_x_tv = TValue::from_string_id(key_x);
        vm.gc.table_raw_set(t_idx, key_x_tv, TValue::from_integer(77)).unwrap();
        let t_val = TValue::from_table(t_idx);

        // Set t in _ENV
        let key_t = vm.strings.intern(b"t");
        let key_t_tv = TValue::from_string_id(key_t);
        vm.gc.table_raw_set(env_idx, key_t_tv, t_val).unwrap();

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(77));
    }

    #[test]
    fn test_proto_set_field() {
        // `t.x = 55` uses SetField
        let source = "t.x = 55";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        // Create table t (empty)
        let t_idx = vm.gc.alloc_table(0, 4);
        let t_val = TValue::from_table(t_idx);
        let key_t = vm.strings.intern(b"t");
        let key_t_tv = TValue::from_string_id(key_t);
        vm.gc.table_raw_set(env_idx, key_t_tv, t_val).unwrap();

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert!(nresults >= 0, "SetField should succeed, got {nresults}");

        // Verify t.x was set
        let key_x = vm.strings.intern(b"x");
        let key_x_tv = TValue::from_string_id(key_x);
        let stored = vm.gc.table_raw_get(t_idx, key_x_tv);
        assert_eq!(stored.as_integer(), Some(55));
    }

    #[test]
    fn test_proto_get_table() {
        // `t[k]` with dynamic key uses GetTable
        let source = "local k = 1; return t[k]";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        // Create table t with t[1] = 88
        let t_idx = vm.gc.alloc_table(4, 0);
        vm.gc.table_raw_set(t_idx, TValue::from_integer(1), TValue::from_integer(88)).unwrap();
        let t_val = TValue::from_table(t_idx);
        let key_t = vm.strings.intern(b"t");
        let key_t_tv = TValue::from_string_id(key_t);
        vm.gc.table_raw_set(env_idx, key_t_tv, t_val).unwrap();

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(88));
    }

    #[test]
    fn test_proto_self_call() {
        // `t:method()` uses Self_ + Call (avoid TailCall with local)
        let source = "local r = t:f(); return r";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        // Create table t with t.f = native that returns self's "val" field
        let t_idx = vm.gc.alloc_table(0, 4);
        let f_idx = vm.gc.alloc_native(|_ctx| {
            // self is first arg (the table)
            Ok(vec![TValue::from_integer(66)])
        }, "f");
        let f_val = TValue::from_native(f_idx);
        let key_f = vm.strings.intern(b"f");
        let key_f_tv = TValue::from_string_id(key_f);
        vm.gc.table_raw_set(t_idx, key_f_tv, f_val).unwrap();

        let t_val = TValue::from_table(t_idx);
        let key_t = vm.strings.intern(b"t");
        let key_t_tv = TValue::from_string_id(key_t);
        vm.gc.table_raw_set(env_idx, key_t_tv, t_val).unwrap();

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(66));
    }

    #[test]
    fn test_proto_call_nested() {
        // Nested call with fixed arg count (avoid multi-return)
        let source = "local x = g(); local r = f(x); return r";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();
        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        // g() returns 5
        let g_idx = vm.gc.alloc_native(|_ctx| {
            Ok(vec![TValue::from_integer(5)])
        }, "g");
        let g_val = TValue::from_native(g_idx);
        let key_g = vm.strings.intern(b"g");
        let key_g_tv = TValue::from_string_id(key_g);
        vm.gc.table_raw_set(env_idx, key_g_tv, g_val).unwrap();

        // f(x) returns x * 10
        let f_idx = vm.gc.alloc_native(|ctx| {
            let x = ctx.args.get(0).and_then(|v| v.as_integer()).unwrap_or(0);
            Ok(vec![TValue::from_integer(x * 10)])
        }, "f");
        let f_val = TValue::from_native(f_idx);
        let key_f = vm.strings.intern(b"f");
        let key_f_tv = TValue::from_string_id(key_f);
        vm.gc.table_raw_set(env_idx, key_f_tv, f_val).unwrap();

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        // f(g()) = f(5) = 50
        assert_eq!(nresults, 1);
        assert_eq!(vm.stack[0].as_integer(), Some(50));
    }

    #[test]
    fn test_proto_tailcall_side_exit() {
        // TailCall should side-exit
        // `return f()` where f is a global function generates TailCall
        // Actually Return1 handles single-value return. TailCall is generated
        // when a function call is in tail position and can be optimized.
        // Let's try: `return f(1, 2, 3)` which may generate TailCall.
        // Actually, `return f()` typically generates TailCall opcode.
        let source = "return f()";
        let (proto, strings) = compile(source.as_bytes(), "test").unwrap();

        // Check if TailCall is in the bytecode
        let has_tailcall = proto.code.iter().any(|i| i.opcode() == OpCode::TailCall);
        if !has_tailcall {
            // If compiler doesn't generate TailCall for this, skip
            return;
        }

        let mut vm = Vm::new();
        vm.strings = strings;
        vm.mm_names = Some(MetamethodNames::init(&mut vm.strings));

        vm.protos.clear();
        let main_proto_idx = vm.protos.len();
        vm.protos.push(proto.clone());

        let env_idx = vm.gc.alloc_table(0, 16);
        let env_val = TValue::from_table(env_idx);
        vm.env_idx = Some(env_idx);

        let env_upval_idx = vm.gc.alloc_upval(UpValLocation::Closed(env_val));
        let closure_idx = vm.gc.alloc_closure(main_proto_idx, vec![env_upval_idx]);

        let base = 0usize;
        vm.stack.resize(256, TValue::nil());
        let mut ci = CallInfo::new(base, main_proto_idx);
        ci.closure_idx = Some(closure_idx);
        vm.call_stack.push(ci);

        let mut compiler = JitCompiler::new().unwrap();
        let func = compiler.compile_proto(&proto, &mut vm.gc, main_proto_idx).unwrap();
        let nresults = unsafe { func(&mut vm as *mut Vm, base) };

        assert_eq!(nresults, SIDE_EXIT, "TailCall should trigger side exit");
    }
}

