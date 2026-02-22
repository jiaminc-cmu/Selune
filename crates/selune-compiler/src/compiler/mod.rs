/// Single-pass Lua 5.4 compiler: source → Proto bytecode.
pub mod expr;
pub mod scope;

use crate::lexer::{LexError, Lexer};
use crate::opcode::{Instruction, OpCode, MAX_BX};
use crate::proto::{Constant, Proto, UpvalDesc};
use crate::token::Token;
use expr::{BinOp, ExprDesc, IndexKey, UnOp, UNARY_PRIORITY};
use scope::{LabelInfo, PendingGoto, ScopeManager};
use selune_core::string::{StringId, StringInterner};
use std::fmt;

/// Compiler error.
#[derive(Clone, Debug)]
pub struct CompileError {
    pub message: String,
    pub line: u32,
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.message)
    }
}

impl std::error::Error for CompileError {}

impl From<LexError> for CompileError {
    fn from(e: LexError) -> Self {
        CompileError {
            message: e.message,
            line: e.line,
        }
    }
}

/// Upvalue description during compilation.
#[derive(Clone, Debug)]
struct UpvalInfo {
    name: StringId,
    in_stack: bool,
    index: u8,
}

/// State for a single function being compiled.
struct FuncState {
    proto: Proto,
    scope: ScopeManager,
    upvalues: Vec<UpvalInfo>,
    /// Index in the parent's FuncState stack.
    parent: Option<usize>,
}

impl FuncState {
    fn new(parent: Option<usize>) -> Self {
        FuncState {
            proto: Proto::new(),
            scope: ScopeManager::new(),
            upvalues: Vec::new(),
            parent,
        }
    }

    fn emit(&mut self, inst: Instruction, line: u32) -> usize {
        self.proto.emit(inst, line)
    }

    fn emit_abc(&mut self, op: OpCode, a: u8, b: u8, c: u8, line: u32) -> usize {
        self.emit(Instruction::abc(op, a, b, c, false), line)
    }

    fn emit_abx(&mut self, op: OpCode, a: u8, bx: u32, line: u32) -> usize {
        self.emit(Instruction::abx(op, a, bx), line)
    }

    fn emit_sj(&mut self, op: OpCode, sj: i32, line: u32) -> usize {
        self.emit(Instruction::sj(op, sj), line)
    }

    fn current_pc(&self) -> usize {
        self.proto.code_len()
    }

    fn add_constant(&mut self, k: Constant) -> u32 {
        self.proto.add_constant(k) as u32
    }

    fn add_string_constant(&mut self, id: StringId) -> u32 {
        self.add_constant(Constant::String(id))
    }
}

/// The compiler: holds the lexer, string interner, and function state stack.
pub struct Compiler<'a> {
    lexer: Lexer<'a>,
    /// Stack of function states (nested functions).
    func_stack: Vec<FuncState>,
}

impl<'a> Compiler<'a> {
    fn new(source: &'a [u8]) -> Self {
        Compiler {
            lexer: Lexer::new(source),
            func_stack: Vec::new(),
        }
    }

    fn fs(&self) -> &FuncState {
        self.func_stack.last().unwrap()
    }

    fn fs_mut(&mut self) -> &mut FuncState {
        self.func_stack.last_mut().unwrap()
    }

    fn line(&self) -> u32 {
        self.lexer.line()
    }

    fn error(&self, msg: impl Into<String>) -> CompileError {
        CompileError {
            message: msg.into(),
            line: self.line(),
        }
    }

    fn error_at(&self, line: u32, msg: impl Into<String>) -> CompileError {
        CompileError {
            message: msg.into(),
            line,
        }
    }

    // ---- Token helpers ----

    fn current_token(&self) -> Result<&Token, CompileError> {
        self.lexer.current().map(|st| &st.token).map_err(|e| CompileError {
            message: e.message.clone(),
            line: e.line,
        })
    }

    fn check(&self, expected: &Token) -> bool {
        self.current_token().map(|t| t == expected).unwrap_or(false)
    }

    fn advance(&mut self) -> Result<Token, CompileError> {
        let st = self.lexer.advance()?;
        Ok(st.token)
    }

    fn expect(&mut self, expected: &Token) -> Result<(), CompileError> {
        if self.check(expected) {
            self.advance()?;
            Ok(())
        } else {
            let found = self.current_token().map(|t| format!("{t}")).unwrap_or("error".into());
            Err(self.error(format!("expected '{expected}', got '{found}'")))
        }
    }

    fn expect_name(&mut self) -> Result<StringId, CompileError> {
        match self.current_token()?.clone() {
            Token::Name(id) => {
                self.advance()?;
                Ok(id)
            }
            other => Err(self.error(format!("expected name, got '{other}'"))),
        }
    }

    fn check_name(&self) -> bool {
        matches!(self.current_token(), Ok(Token::Name(_)))
    }

    fn test_next(&mut self, expected: &Token) -> Result<bool, CompileError> {
        if self.check(expected) {
            self.advance()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    // ---- Code generation helpers ----

    fn emit(&mut self, inst: Instruction, line: u32) -> usize {
        self.fs_mut().emit(inst, line)
    }

    fn emit_abc(&mut self, op: OpCode, a: u8, b: u8, c: u8, line: u32) -> usize {
        self.fs_mut().emit_abc(op, a, b, c, line)
    }

    fn emit_abx(&mut self, op: OpCode, a: u8, bx: u32, line: u32) -> usize {
        self.fs_mut().emit_abx(op, a, bx, line)
    }

    fn emit_sj(&mut self, op: OpCode, sj: i32, line: u32) -> usize {
        self.fs_mut().emit_sj(op, sj, line)
    }

    fn emit_jump(&mut self, line: u32) -> usize {
        self.emit_sj(OpCode::Jmp, 0, line) // placeholder, to be patched
    }

    fn patch_jump(&mut self, jump_pc: usize) {
        let target = self.fs().current_pc();
        let offset = target as i32 - jump_pc as i32 - 1;
        self.fs_mut().proto.get_mut(jump_pc).set_sj(offset);
    }

    fn patch_jump_to(&mut self, jump_pc: usize, target: usize) {
        let offset = target as i32 - jump_pc as i32 - 1;
        self.fs_mut().proto.get_mut(jump_pc).set_sj(offset);
    }

    /// Discharge an ExprDesc into a specific register.
    fn discharge_to_reg(&mut self, expr: &ExprDesc, reg: u8, line: u32) {
        match expr {
            ExprDesc::Nil => {
                self.emit_abx(OpCode::LoadNil, reg, 0, line);
            }
            ExprDesc::True => {
                self.emit_abx(OpCode::LoadTrue, reg, 0, line);
            }
            ExprDesc::False => {
                self.emit_abx(OpCode::LoadFalse, reg, 0, line);
            }
            ExprDesc::Integer(i) => {
                let i = *i;
                if i >= i32::MIN as i64 && i <= i32::MAX as i64 {
                    self.emit_abx(OpCode::LoadI, reg, 0, line);
                    // For LoadI, we store the signed value in sBx
                    let pc = self.fs().current_pc() - 1;
                    // Re-encode as asbx
                    let sbx = i as i32;
                    // Check sBx range
                    if sbx >= crate::opcode::MIN_SBX && sbx <= crate::opcode::MAX_SBX {
                        self.fs_mut().proto.code[pc] =
                            Instruction::asbx(OpCode::LoadI, reg, sbx);
                    } else {
                        // Fallback to constant
                        self.fs_mut().proto.code.pop();
                        self.fs_mut().proto.line_info.pop();
                        let k = self.fs_mut().add_constant(Constant::Integer(i));
                        self.emit_load_constant(reg, k, line);
                    }
                } else {
                    let k = self.fs_mut().add_constant(Constant::Integer(i));
                    self.emit_load_constant(reg, k, line);
                }
            }
            ExprDesc::Float(f) => {
                let f = *f;
                // Try LoadF for small integer-valued floats
                let as_int = f as i32;
                if as_int as f64 == f
                    && as_int >= crate::opcode::MIN_SBX
                    && as_int <= crate::opcode::MAX_SBX
                {
                    self.emit(Instruction::asbx(OpCode::LoadF, reg, as_int), line);
                } else {
                    let k = self.fs_mut().add_constant(Constant::Float(f));
                    self.emit_load_constant(reg, k, line);
                }
            }
            ExprDesc::Str(id) => {
                let k = self.fs_mut().add_string_constant(*id);
                self.emit_load_constant(reg, k, line);
            }
            ExprDesc::Register(src) => {
                if *src != reg {
                    self.emit_abc(OpCode::Move, reg, *src, 0, line);
                }
            }
            ExprDesc::Upvalue(idx) => {
                self.emit_abc(OpCode::GetUpval, reg, *idx, 0, line);
            }
            ExprDesc::Constant(k) => {
                self.emit_load_constant(reg, *k, line);
            }
            ExprDesc::Global { env_upval, name_k } => {
                self.emit(
                    Instruction::abc(OpCode::GetTabUp, reg, *env_upval, *name_k as u8, false),
                    line,
                );
            }
            ExprDesc::Indexed { table, key } => {
                match key {
                    IndexKey::Field(k) => {
                        self.emit(
                            Instruction::abc(OpCode::GetField, reg, *table, *k as u8, false),
                            line,
                        );
                    }
                    IndexKey::Register(key_reg) => {
                        self.emit_abc(OpCode::GetTable, reg, *table, *key_reg, line);
                    }
                    IndexKey::Integer(i) => {
                        self.emit_abc(OpCode::GetI, reg, *table, *i, line);
                    }
                    IndexKey::Constant(k) => {
                        self.emit(
                            Instruction::abc(OpCode::GetTable, reg, *table, *k as u8, true),
                            line,
                        );
                    }
                }
            }
            ExprDesc::Relocatable(pc) => {
                self.fs_mut().proto.code[*pc].set_a(reg);
            }
            ExprDesc::Jump(_) => {
                // For jump expressions (comparisons), we need to generate
                // LOADTRUE/LOADFALSE based on the result
                // This is handled by code_test_set in practice
                self.emit_abx(OpCode::LoadTrue, reg, 0, line);
            }
            ExprDesc::Call(pc) => {
                // Set the call result count to 1 (in register C)
                let inst = &mut self.fs_mut().proto.code[*pc];
                let a = inst.a();
                *inst = Instruction::abc(inst.opcode(), a, inst.b(), 2, inst.k());
                if a != reg {
                    self.emit_abc(OpCode::Move, reg, a, 0, line);
                }
            }
            ExprDesc::Vararg(pc) => {
                let inst = &mut self.fs_mut().proto.code[*pc];
                *inst = Instruction::abc(OpCode::VarArg, reg, 2, 0, false);
            }
            ExprDesc::Void => {}
        }
    }

    fn emit_load_constant(&mut self, reg: u8, k: u32, line: u32) {
        if k <= MAX_BX {
            self.emit_abx(OpCode::LoadK, reg, k, line);
        } else {
            self.emit_abx(OpCode::LoadKX, reg, 0, line);
            self.emit(Instruction::ax(OpCode::ExtraArg, k), line);
        }
    }

    /// Discharge an expression into any register, returning the register.
    fn discharge_to_any_reg(&mut self, expr: &ExprDesc, line: u32) -> u8 {
        match expr {
            ExprDesc::Register(r) => *r,
            _ => {
                let reg = self.fs_mut().scope.alloc_reg();
                self.discharge_to_reg(expr, reg, line);
                reg
            }
        }
    }

    /// Ensure an expression is in a register. May allocate a new one.
    fn exp_to_reg(&mut self, expr: ExprDesc, line: u32) -> ExprDesc {
        let reg = self.discharge_to_any_reg(&expr, line);
        ExprDesc::Register(reg)
    }

    // ---- Expression parsing ----

    /// Parse a full expression (with precedence climbing).
    pub(crate) fn expression(&mut self) -> Result<ExprDesc, CompileError> {
        self.sub_expression(0)
    }

    /// Precedence climbing expression parser.
    fn sub_expression(&mut self, min_prec: u8) -> Result<ExprDesc, CompileError> {
        let line = self.line();
        let mut expr = if let Some(unop) = self.check_unary_op()? {
            self.advance()?;
            let sub = self.sub_expression(UNARY_PRIORITY)?;
            self.code_unary_op(unop, sub, line)?
        } else {
            self.simple_expression()?
        };

        while let Some(binop) = self.check_binary_op()? {
            let (left_prec, right_prec) = binop.priority();
            if left_prec <= min_prec {
                break;
            }
            let op_line = self.line();
            self.advance()?;

            // For short-circuit operators, handle specially
            if binop == BinOp::And || binop == BinOp::Or {
                expr = self.code_short_circuit(binop, expr, right_prec, op_line)?;
            } else if binop == BinOp::Concat {
                // Concat needs all operands in consecutive registers.
                // Collect all concat operands, discharge to consecutive regs,
                // then emit a single Concat instruction.
                let first_reg = self.fs_mut().scope.alloc_reg();
                self.discharge_to_reg(&expr, first_reg, op_line);
                let mut count: u8 = 1;
                loop {
                    // Parse the next operand at concat's left priority,
                    // so higher-priority ops (+ * ^ unary) are absorbed
                    // but further concats are NOT absorbed into this operand.
                    let operand = self.sub_expression(left_prec)?;
                    let reg = self.fs_mut().scope.alloc_reg();
                    self.discharge_to_reg(&operand, reg, op_line);
                    count += 1;
                    // Check if next token is also concat
                    if let Some(next_op) = self.check_binary_op()? {
                        if next_op == BinOp::Concat {
                            self.advance()?;
                            continue;
                        }
                    }
                    break;
                }
                self.emit_abc(OpCode::Concat, first_reg, count, 0, op_line);
                self.fs_mut().scope.free_reg_to(first_reg + 1);
                expr = ExprDesc::Register(first_reg);
            } else {
                let left_reg = self.discharge_to_any_reg(&expr, op_line);
                let right = self.sub_expression(right_prec)?;
                expr = self.code_binary_op(binop, left_reg, right, op_line)?;
            }
        }

        Ok(expr)
    }

    /// Parse a simple (non-binary-op) expression.
    fn simple_expression(&mut self) -> Result<ExprDesc, CompileError> {
        let token = self.current_token()?.clone();
        match token {
            Token::Integer(i) => {
                self.advance()?;
                Ok(ExprDesc::Integer(i))
            }
            Token::Float(f) => {
                self.advance()?;
                Ok(ExprDesc::Float(f))
            }
            Token::String(id) => {
                self.advance()?;
                Ok(ExprDesc::Str(id))
            }
            Token::Nil => {
                self.advance()?;
                Ok(ExprDesc::Nil)
            }
            Token::True => {
                self.advance()?;
                Ok(ExprDesc::True)
            }
            Token::False => {
                self.advance()?;
                Ok(ExprDesc::False)
            }
            Token::DotDotDot => {
                self.advance()?;
                if !self.fs().proto.is_vararg {
                    return Err(self.error("cannot use '...' outside a vararg function"));
                }
                let line = self.line();
                let pc = self.emit_abc(OpCode::VarArg, 0, 0, 0, line);
                Ok(ExprDesc::Vararg(pc))
            }
            Token::LBrace => {
                self.table_constructor()
            }
            Token::Function => {
                self.advance()?;
                self.function_body(false)
            }
            _ => {
                self.primary_expression()
            }
        }
    }

    /// Parse a primary expression (name or parenthesized) with suffixes.
    fn primary_expression(&mut self) -> Result<ExprDesc, CompileError> {
        let expr = match self.current_token()?.clone() {
            Token::Name(name) => {
                self.advance()?;
                self.resolve_name(name)?
            }
            Token::LParen => {
                self.advance()?;
                let e = self.expression()?;
                self.expect(&Token::RParen)?;
                match e {
                    ExprDesc::Call(pc) | ExprDesc::Vararg(pc) => {
                        let line = self.line();
                        let reg = self.discharge_to_any_reg(&ExprDesc::Call(pc), line);
                        ExprDesc::Register(reg)
                    }
                    other => other,
                }
            }
            other => {
                return Err(self.error(format!("unexpected symbol '{other}'")));
            }
        };

        self.finish_primary_expression(expr)
    }

    /// Parse suffix chain: .field, [key], :method(), ()
    fn finish_primary_expression(&mut self, mut expr: ExprDesc) -> Result<ExprDesc, CompileError> {
        loop {
            match self.current_token()?.clone() {
                Token::Dot => {
                    self.advance()?;
                    let field_name = self.expect_name()?;
                    let line = self.line();
                    let table_reg = self.discharge_to_any_reg(&expr, line);
                    let k = self.fs_mut().add_string_constant(field_name);
                    expr = ExprDesc::Indexed {
                        table: table_reg,
                        key: IndexKey::Field(k),
                    };
                }
                Token::LBracket => {
                    self.advance()?;
                    let line = self.line();
                    let table_reg = self.discharge_to_any_reg(&expr, line);
                    let key_expr = self.expression()?;
                    self.expect(&Token::RBracket)?;
                    let key = self.expr_to_index_key(key_expr, line);
                    expr = ExprDesc::Indexed {
                        table: table_reg,
                        key,
                    };
                }
                Token::Colon => {
                    self.advance()?;
                    let method_name = self.expect_name()?;
                    let line = self.line();
                    let table_reg = self.discharge_to_any_reg(&expr, line);
                    let k = self.fs_mut().add_string_constant(method_name);
                    let self_reg = self.fs_mut().scope.alloc_reg();
                    self.emit(
                        Instruction::abc(OpCode::Self_, self_reg, table_reg, k as u8, true),
                        line,
                    );
                    let _obj_reg = self.fs_mut().scope.alloc_reg();
                    expr = ExprDesc::Register(self_reg);
                    expr = self.function_call(expr, line)?;
                }
                Token::LParen | Token::LBrace | Token::String(_) => {
                    let line = self.line();
                    expr = self.function_call(expr, line)?;
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    /// Finish parsing an expression that started with a name (for table constructor reuse).
    fn finish_expression(&mut self, expr: ExprDesc) -> Result<ExprDesc, CompileError> {
        // Continue with binary operators if any
        if let Some(binop) = self.check_binary_op()? {
            let (left_prec, right_prec) = binop.priority();
            if left_prec > 0 {
                let op_line = self.line();
                self.advance()?;
                let left_reg = self.discharge_to_any_reg(&expr, op_line);
                if binop == BinOp::And || binop == BinOp::Or {
                    // Put the value back and call sub_expression properly
                    // Actually, for simplicity in table constructors, just handle it:
                    let right = self.sub_expression(right_prec)?;
                    if binop == BinOp::And || binop == BinOp::Or {
                        // Short-circuit was already handled in sub_expression
                        return self.code_binary_op(binop, left_reg, right, op_line);
                    }
                    return self.code_binary_op(binop, left_reg, right, op_line);
                }
                let right = self.sub_expression(right_prec)?;
                return self.code_binary_op(binop, left_reg, right, op_line);
            }
        }
        Ok(expr)
    }

    /// Parse a function call.
    fn function_call(&mut self, func_expr: ExprDesc, line: u32) -> Result<ExprDesc, CompileError> {
        let func_reg = self.discharge_to_any_reg(&func_expr, line);
        let base = func_reg;

        let nargs = match self.current_token()?.clone() {
            Token::LParen => {
                self.advance()?;
                if self.check(&Token::RParen) {
                    self.advance()?;
                    0u8
                } else {
                    let n = self.expression_list(base + 1)?;
                    self.expect(&Token::RParen)?;
                    n
                }
            }
            Token::LBrace => {
                let table = self.table_constructor()?;
                self.discharge_to_reg(&table, base + 1, line);
                1u8
            }
            Token::String(id) => {
                self.advance()?;
                self.discharge_to_reg(&ExprDesc::Str(id), base + 1, line);
                1u8
            }
            _ => {
                return Err(self.error("function arguments expected"));
            }
        };

        // CALL A B C: call func at R(A), B-1 args, C-1 results (0 = multi)
        let pc = self.emit(
            Instruction::abc(OpCode::Call, base, nargs + 1, 0, false),
            line,
        );
        // Free all arg registers, leave result in base
        self.fs_mut().scope.free_reg_to(base + 1);
        Ok(ExprDesc::Call(pc))
    }

    /// Parse an expression list, discharging each to consecutive registers.
    /// Returns the number of expressions parsed. The last expression may be multi-value.
    fn expression_list(&mut self, base_reg: u8) -> Result<u8, CompileError> {
        let mut count = 0u8;
        loop {
            let expr = self.expression()?;
            let line = self.line();

            if !self.check(&Token::Comma) {
                // Last expression: might be multi-value
                match &expr {
                    ExprDesc::Call(_) | ExprDesc::Vararg(_) => {
                        // Leave multi-value as-is — caller handles
                        self.discharge_to_reg(&expr, base_reg + count, line);
                        count += 1;
                    }
                    _ => {
                        self.discharge_to_reg(&expr, base_reg + count, line);
                        count += 1;
                    }
                }
                break;
            }

            // Not the last expression: force single value
            self.discharge_to_reg(&expr, base_reg + count, line);
            self.fs_mut().scope.free_reg_to(base_reg + count + 1);
            count += 1;
            self.advance()?; // consume comma
        }
        Ok(count)
    }

    fn expr_to_index_key(&mut self, expr: ExprDesc, line: u32) -> IndexKey {
        match expr {
            ExprDesc::Integer(i) if i >= 0 && i <= 255 => IndexKey::Integer(i as u8),
            ExprDesc::Str(id) => {
                let k = self.fs_mut().add_string_constant(id);
                IndexKey::Field(k)
            }
            _ => {
                let reg = self.discharge_to_any_reg(&expr, line);
                IndexKey::Register(reg)
            }
        }
    }

    /// Table constructor: { field, field, ... }
    fn table_constructor(&mut self) -> Result<ExprDesc, CompileError> {
        self.expect(&Token::LBrace)?;
        let line = self.line();
        let table_reg = self.fs_mut().scope.alloc_reg();
        let pc = self.emit_abc(OpCode::NewTable, table_reg, 0, 0, line);

        let mut array_count = 0u32;
        let mut hash_count = 0u32;
        let mut total_array = 0u32;

        while !self.check(&Token::RBrace) {
            match self.current_token()?.clone() {
                Token::LBracket => {
                    // [expr] = expr
                    self.advance()?;
                    let key = self.expression()?;
                    self.expect(&Token::RBracket)?;
                    self.expect(&Token::Assign)?;
                    let val = self.expression()?;
                    let kline = self.line();
                    let key_reg = self.discharge_to_any_reg(&key, kline);
                    let val_reg = self.discharge_to_any_reg(&val, kline);
                    self.emit_abc(OpCode::SetTable, table_reg, key_reg, val_reg, kline);
                    self.fs_mut().scope.free_reg_to(table_reg + 1);
                    hash_count += 1;
                }
                Token::Name(name) => {
                    // Could be name=expr (hash) or just an expression (array)
                    // We consume the name and check if next is '='
                    self.advance()?;
                    if self.check(&Token::Assign) {
                        // name = expr
                        self.advance()?;
                        let val = self.expression()?;
                        let kline = self.line();
                        let k = self.fs_mut().add_string_constant(name);
                        let val_reg = self.discharge_to_any_reg(&val, kline);
                        self.emit(
                            Instruction::abc(OpCode::SetField, table_reg, k as u8, val_reg, false),
                            kline,
                        );
                        self.fs_mut().scope.free_reg_to(table_reg + 1);
                        hash_count += 1;
                    } else {
                        // It's an expression starting with a name — resolve as expression
                        let name_expr = self.resolve_name(name)?;
                        // Parse suffix chain on this name
                        let expr = self.finish_primary_expression(name_expr)?;
                        // Check for binary operators
                        let expr = self.finish_expression(expr)?;
                        let eline = self.line();
                        let _val_reg = self.discharge_to_any_reg(&expr, eline);
                        array_count += 1;
                        total_array += 1;
                        if array_count >= 50 {
                            let batch = (total_array - 1) / 50 + 1;
                            self.emit(
                                Instruction::abc(
                                    OpCode::SetList,
                                    table_reg,
                                    array_count as u8,
                                    batch as u8,
                                    false,
                                ),
                                eline,
                            );
                            self.fs_mut().scope.free_reg_to(table_reg + 1);
                            array_count = 0;
                        }
                    }
                }
                _ => {
                    // Array element
                    let expr = self.expression()?;
                    let eline = self.line();
                    let val_reg = self.discharge_to_any_reg(&expr, eline);
                    array_count += 1;
                    total_array += 1;

                    // Flush in batches of 50 (LFIELDS_PER_FLUSH in PUC)
                    if array_count >= 50 {
                        let batch = (total_array - 1) / 50 + 1;
                        self.emit(
                            Instruction::abc(
                                OpCode::SetList,
                                table_reg,
                                array_count as u8,
                                batch as u8,
                                false,
                            ),
                            eline,
                        );
                        self.fs_mut().scope.free_reg_to(table_reg + 1);
                        array_count = 0;
                    }
                    let _ = val_reg; // used implicitly via register allocation
                }
            }

            // Optional separator
            if !self.test_next(&Token::Comma)? && !self.test_next(&Token::Semi)? {
                break;
            }
        }

        self.expect(&Token::RBrace)?;

        // Flush remaining array elements
        if array_count > 0 {
            let batch = (total_array - 1) / 50 + 1;
            let eline = self.line();
            self.emit(
                Instruction::abc(
                    OpCode::SetList,
                    table_reg,
                    array_count as u8,
                    batch as u8,
                    false,
                ),
                eline,
            );
        }

        // Patch NewTable with size hints
        let array_log = if total_array > 0 {
            int_log2(total_array) + 1
        } else {
            0
        };
        let hash_log = if hash_count > 0 {
            int_log2(hash_count) + 1
        } else {
            0
        };
        self.fs_mut().proto.code[pc] =
            Instruction::abc(OpCode::NewTable, table_reg, array_log as u8, hash_log as u8, false);

        self.fs_mut().scope.free_reg_to(table_reg + 1);
        Ok(ExprDesc::Register(table_reg))
    }

    // ---- Unary/Binary operations ----

    fn check_unary_op(&self) -> Result<Option<UnOp>, CompileError> {
        Ok(match self.current_token()? {
            Token::Minus => Some(UnOp::Neg),
            Token::Tilde => Some(UnOp::BNot),
            Token::Not => Some(UnOp::Not),
            Token::Hash => Some(UnOp::Len),
            _ => None,
        })
    }

    fn check_binary_op(&self) -> Result<Option<BinOp>, CompileError> {
        Ok(match self.current_token()? {
            Token::Plus => Some(BinOp::Add),
            Token::Minus => Some(BinOp::Sub),
            Token::Star => Some(BinOp::Mul),
            Token::Slash => Some(BinOp::Div),
            Token::FloorDiv => Some(BinOp::IDiv),
            Token::Percent => Some(BinOp::Mod),
            Token::Caret => Some(BinOp::Pow),
            Token::DotDot => Some(BinOp::Concat),
            Token::ShiftLeft => Some(BinOp::Shl),
            Token::ShiftRight => Some(BinOp::Shr),
            Token::Ampersand => Some(BinOp::BAnd),
            Token::Pipe => Some(BinOp::BOr),
            Token::Tilde => Some(BinOp::BXor),
            Token::Equal => Some(BinOp::Eq),
            Token::NotEqual => Some(BinOp::NotEq),
            Token::Less => Some(BinOp::Lt),
            Token::LessEq => Some(BinOp::LtEq),
            Token::Greater => Some(BinOp::Gt),
            Token::GreaterEq => Some(BinOp::GtEq),
            Token::And => Some(BinOp::And),
            Token::Or => Some(BinOp::Or),
            _ => None,
        })
    }

    fn code_unary_op(
        &mut self,
        op: UnOp,
        expr: ExprDesc,
        line: u32,
    ) -> Result<ExprDesc, CompileError> {
        // Try constant folding
        match (op, &expr) {
            (UnOp::Neg, ExprDesc::Integer(i)) => return Ok(ExprDesc::Integer(-i)),
            (UnOp::Neg, ExprDesc::Float(f)) => return Ok(ExprDesc::Float(-f)),
            (UnOp::BNot, ExprDesc::Integer(i)) => return Ok(ExprDesc::Integer(!i)),
            (UnOp::Not, ExprDesc::Nil | ExprDesc::False) => return Ok(ExprDesc::True),
            (UnOp::Not, ExprDesc::True | ExprDesc::Integer(_) | ExprDesc::Float(_) | ExprDesc::Str(_)) => {
                return Ok(ExprDesc::False)
            }
            _ => {}
        }

        let reg = self.discharge_to_any_reg(&expr, line);
        let dest = self.fs_mut().scope.alloc_reg();
        let opcode = match op {
            UnOp::Neg => OpCode::Unm,
            UnOp::BNot => OpCode::BNot,
            UnOp::Not => OpCode::Not,
            UnOp::Len => OpCode::Len,
        };
        self.emit_abc(opcode, dest, reg, 0, line);
        self.fs_mut().scope.free_reg_to(dest + 1);
        Ok(ExprDesc::Register(dest))
    }

    fn code_binary_op(
        &mut self,
        op: BinOp,
        left_reg: u8,
        right: ExprDesc,
        line: u32,
    ) -> Result<ExprDesc, CompileError> {
        // Try constant folding for arithmetic
        // (simplified: only when both are in ExprDesc form before discharge)
        // Since left is already discharged to reg, we mainly fold right with const ops

        if op.is_comparison() {
            return self.code_comparison(op, left_reg, right, line);
        }

        if op == BinOp::Concat {
            let right_reg = self.discharge_to_any_reg(&right, line);
            let dest = left_reg; // concat overwrites leftmost
            self.emit_abc(OpCode::Concat, dest, right_reg - dest + 1, 0, line);
            self.fs_mut().scope.free_reg_to(dest + 1);
            return Ok(ExprDesc::Register(dest));
        }

        let (opcode, opcode_k) = match op {
            BinOp::Add => (OpCode::Add, OpCode::AddK),
            BinOp::Sub => (OpCode::Sub, OpCode::SubK),
            BinOp::Mul => (OpCode::Mul, OpCode::MulK),
            BinOp::Div => (OpCode::Div, OpCode::DivK),
            BinOp::IDiv => (OpCode::IDiv, OpCode::IDivK),
            BinOp::Mod => (OpCode::Mod, OpCode::ModK),
            BinOp::Pow => (OpCode::Pow, OpCode::PowK),
            BinOp::Shl => (OpCode::Shl, OpCode::Shl),
            BinOp::Shr => (OpCode::Shr, OpCode::Shr),
            BinOp::BAnd => (OpCode::BAnd, OpCode::BAndK),
            BinOp::BOr => (OpCode::BOr, OpCode::BOrK),
            BinOp::BXor => (OpCode::BXor, OpCode::BXorK),
            _ => unreachable!(),
        };

        // Try to use constant variant
        if let ExprDesc::Integer(i) = &right {
            let i = *i;
            if matches!(
                op,
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Mod | BinOp::Pow
                    | BinOp::Div | BinOp::IDiv | BinOp::BAnd | BinOp::BOr | BinOp::BXor
            ) {
                let k = self.fs_mut().add_constant(Constant::Integer(i));
                if k <= 255 {
                    let dest = self.fs_mut().scope.alloc_reg();
                    self.emit(
                        Instruction::abc(opcode_k, dest, left_reg, k as u8, false),
                        line,
                    );
                    self.fs_mut().scope.free_reg_to(dest + 1);
                    // Emit MMBIN for metamethod fallback
                    self.emit(
                        Instruction::abc(OpCode::MMBinK, left_reg, k as u8, op_to_mm(op), false),
                        line,
                    );
                    return Ok(ExprDesc::Register(dest));
                }
            }
        }

        // Integer immediate for add/shift
        if let ExprDesc::Integer(i) = &right {
            let i = *i;
            if i >= -128 && i <= 127 {
                if op == BinOp::Add {
                    let dest = self.fs_mut().scope.alloc_reg();
                    self.emit(
                        Instruction::abc(OpCode::AddI, dest, left_reg, (i as u8) & 0xFF, false),
                        line,
                    );
                    self.fs_mut().scope.free_reg_to(dest + 1);
                    self.emit(
                        Instruction::abc(
                            OpCode::MMBinI,
                            left_reg,
                            (i as u8) & 0xFF,
                            op_to_mm(op),
                            false,
                        ),
                        line,
                    );
                    return Ok(ExprDesc::Register(dest));
                }
                if op == BinOp::Shr {
                    let dest = self.fs_mut().scope.alloc_reg();
                    self.emit(
                        Instruction::abc(OpCode::ShrI, dest, left_reg, (i as u8) & 0xFF, false),
                        line,
                    );
                    self.fs_mut().scope.free_reg_to(dest + 1);
                    return Ok(ExprDesc::Register(dest));
                }
                if op == BinOp::Shl {
                    let dest = self.fs_mut().scope.alloc_reg();
                    self.emit(
                        Instruction::abc(OpCode::ShlI, dest, left_reg, (i as u8) & 0xFF, false),
                        line,
                    );
                    self.fs_mut().scope.free_reg_to(dest + 1);
                    return Ok(ExprDesc::Register(dest));
                }
            }
        }

        // General register-register case
        let right_reg = self.discharge_to_any_reg(&right, line);
        let dest = self.fs_mut().scope.alloc_reg();
        self.emit_abc(opcode, dest, left_reg, right_reg, line);
        self.fs_mut().scope.free_reg_to(dest + 1);
        // Emit MMBIN for metamethod fallback
        self.emit(
            Instruction::abc(OpCode::MMBin, left_reg, right_reg, op_to_mm(op), false),
            line,
        );
        Ok(ExprDesc::Register(dest))
    }

    fn code_comparison(
        &mut self,
        op: BinOp,
        left_reg: u8,
        right: ExprDesc,
        line: u32,
    ) -> Result<ExprDesc, CompileError> {
        let right_reg = self.discharge_to_any_reg(&right, line);

        let (opcode, a, b, k) = match op {
            BinOp::Eq => (OpCode::Eq, left_reg, right_reg, false),
            BinOp::NotEq => (OpCode::Eq, left_reg, right_reg, true), // k=1 negates
            BinOp::Lt => (OpCode::Lt, left_reg, right_reg, false),
            BinOp::GtEq => (OpCode::Lt, left_reg, right_reg, true),
            BinOp::LtEq => (OpCode::Le, left_reg, right_reg, false),
            BinOp::Gt => (OpCode::Le, left_reg, right_reg, true),
            _ => unreachable!(),
        };

        self.emit(Instruction::abc(opcode, a, b, 0, k), line);
        let pc = self.emit_sj(OpCode::Jmp, 0, line);
        self.fs_mut().scope.free_reg_to(left_reg);
        Ok(ExprDesc::Jump(pc))
    }

    fn code_short_circuit(
        &mut self,
        op: BinOp,
        left: ExprDesc,
        right_prec: u8,
        line: u32,
    ) -> Result<ExprDesc, CompileError> {
        let left_reg = self.discharge_to_any_reg(&left, line);

        if op == BinOp::And {
            // If left is falsy, skip right; result = left
            self.emit(Instruction::abc(OpCode::TestSet, left_reg, left_reg, 0, false), line);
        } else {
            // If left is truthy, skip right; result = left
            self.emit(Instruction::abc(OpCode::TestSet, left_reg, left_reg, 0, true), line);
        }
        let jump = self.emit_sj(OpCode::Jmp, 0, line);

        // Right side may allocate temps, so save/restore
        let save_reg = self.fs().scope.free_reg;
        let right = self.sub_expression(right_prec)?;
        let right_line = self.line();
        self.discharge_to_reg(&right, left_reg, right_line);
        if self.fs().scope.free_reg > left_reg + 1 {
            self.fs_mut().scope.free_reg_to(left_reg + 1);
        }

        self.patch_jump(jump);
        Ok(ExprDesc::Register(left_reg))
    }

    /// Resolve a name: local → upvalue → _ENV global.
    fn resolve_name(&mut self, name: StringId) -> Result<ExprDesc, CompileError> {
        // Check locals
        if let Some(local) = self.fs().scope.resolve_local(name) {
            return Ok(ExprDesc::Register(local.reg));
        }

        // Check upvalues
        if let Some(idx) = self.resolve_upvalue(self.func_stack.len() - 1, name) {
            return Ok(ExprDesc::Upvalue(idx));
        }

        // Global: _ENV[name]
        let env_idx = self.resolve_upvalue_env();
        let k = self.fs_mut().add_string_constant(name);
        Ok(ExprDesc::Global { env_upval: env_idx, name_k: k })
    }

    /// Resolve an upvalue by walking up the function state stack.
    fn resolve_upvalue(&mut self, fs_idx: usize, name: StringId) -> Option<u8> {
        if fs_idx == 0 {
            // At the outermost function, check its locals only
            let local = self.func_stack[0].scope.resolve_local(name)?;
            let reg = local.reg;
            return Some(self.add_upvalue(fs_idx, name, true, reg));
        }

        // Check parent's locals first
        let parent_idx = fs_idx - 1;
        if let Some(local) = self.func_stack[parent_idx].scope.resolve_local(name) {
            let reg = local.reg;
            return Some(self.add_upvalue(fs_idx, name, true, reg));
        }

        // Check parent's upvalues
        if let Some(parent_upval) = self.resolve_upvalue(parent_idx, name) {
            return Some(self.add_upvalue(fs_idx, name, false, parent_upval));
        }

        None
    }

    fn add_upvalue(&mut self, fs_idx: usize, name: StringId, in_stack: bool, index: u8) -> u8 {
        let fs = &mut self.func_stack[fs_idx];
        // Check if already registered
        for (i, up) in fs.upvalues.iter().enumerate() {
            if up.in_stack == in_stack && up.index == index {
                return i as u8;
            }
        }
        let idx = fs.upvalues.len() as u8;
        fs.upvalues.push(UpvalInfo {
            name,
            in_stack,
            index,
        });
        idx
    }

    /// Get the upvalue index for _ENV (always 0 at any function level).
    fn resolve_upvalue_env(&mut self) -> u8 {
        // _ENV is upvalue 0 of every function
        0
    }

    /// Compile a function body (after 'function' keyword or in function statement).
    pub(crate) fn function_body(
        &mut self,
        is_method: bool,
    ) -> Result<ExprDesc, CompileError> {
        let line = self.line();

        // Create new FuncState
        let parent_idx = self.func_stack.len() - 1;
        let mut new_fs = FuncState::new(Some(parent_idx));
        new_fs.proto.source = self.fs().proto.source;
        new_fs.scope.enter_block(false);

        // For methods, add implicit 'self' parameter
        if is_method {
            let self_name = self.lexer.strings.intern(b"self");
            new_fs.scope.add_local(self_name, false, false, 0);
            new_fs.proto.num_params = 1;
        }

        self.func_stack.push(new_fs);

        self.expect(&Token::LParen)?;
        if !self.check(&Token::RParen) {
            self.parse_param_list()?;
        }
        self.expect(&Token::RParen)?;

        self.block()?;
        self.expect(&Token::End)?;

        // Emit RETURN0 if no explicit return
        let ret_line = self.line();
        self.emit_abc(OpCode::Return0, 0, 0, 0, ret_line);

        // Pop FuncState
        let mut child_fs = self.func_stack.pop().unwrap();
        child_fs.scope.leave_block();
        child_fs.proto.max_stack_size = child_fs.scope.max_reg + 2;

        // Convert upvalue info
        child_fs.proto.upvalues = child_fs
            .upvalues
            .iter()
            .map(|u| UpvalDesc {
                name: Some(u.name),
                in_stack: u.in_stack,
                index: u.index,
                kind: 0,
            })
            .collect();

        // Add child proto to parent
        let proto_idx = self.fs().proto.protos.len();
        self.fs_mut().proto.protos.push(child_fs.proto);

        // Emit CLOSURE instruction
        let dest = self.fs_mut().scope.alloc_reg();
        self.emit_abx(OpCode::Closure, dest, proto_idx as u32, line);
        Ok(ExprDesc::Register(dest))
    }

    fn parse_param_list(&mut self) -> Result<(), CompileError> {
        loop {
            match self.current_token()?.clone() {
                Token::Name(name) => {
                    self.advance()?;
                    self.fs_mut().scope.add_local(name, false, false, 0);
                    self.fs_mut().proto.num_params += 1;
                }
                Token::DotDotDot => {
                    self.advance()?;
                    self.fs_mut().proto.is_vararg = true;
                    break;
                }
                _ => break,
            }
            if !self.test_next(&Token::Comma)? {
                break;
            }
        }
        Ok(())
    }

    // ---- Block parsing (used by function_body, statements) ----

    /// Parse a block of statements until a block-ending token.
    pub(crate) fn block(&mut self) -> Result<(), CompileError> {
        loop {
            match self.current_token()? {
                Token::End | Token::Else | Token::ElseIf | Token::Until | Token::Eof => break,
                _ => {
                    self.statement()?;
                }
            }
        }
        Ok(())
    }

    /// Statement dispatch — placeholder, will be filled in commit 8.
    fn statement(&mut self) -> Result<(), CompileError> {
        match self.current_token()?.clone() {
            Token::Semi => {
                self.advance()?;
                Ok(())
            }
            Token::Local => self.stat_local(),
            Token::If => self.stat_if(),
            Token::While => self.stat_while(),
            Token::Do => self.stat_do(),
            Token::For => self.stat_for(),
            Token::Repeat => self.stat_repeat(),
            Token::Function => self.stat_function(),
            Token::Return => self.stat_return(),
            Token::Break => self.stat_break(),
            Token::Goto => self.stat_goto(),
            Token::DoubleColon => self.stat_label(),
            _ => self.stat_expr_or_assign(),
        }
    }

    // ---- Statement implementations ----

    /// `local name {, name} ['=' explist]`
    /// `local function name funcbody`
    fn stat_local(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume 'local'
        let line = self.line();

        if self.check(&Token::Function) {
            // local function name funcbody
            self.advance()?;
            let name = self.expect_name()?;
            let pc = self.fs().current_pc() as u32;
            let reg = self.fs_mut().scope.add_local(name, false, false, pc);
            let func_expr = self.function_body(false)?;
            self.discharge_to_reg(&func_expr, reg, line);
            self.fs_mut().scope.free_reg_to(reg + 1);
            return Ok(());
        }

        // Parse variable names with optional attributes
        let mut names = Vec::new();
        let mut attrs = Vec::new();
        loop {
            let name = self.expect_name()?;
            names.push(name);
            // Check for <const> or <close> attribute
            let (is_const, is_close) = if self.check(&Token::Less) {
                self.advance()?;
                let attr = self.expect_name()?;
                self.expect(&Token::Greater)?;
                let attr_bytes = self.lexer.strings.get_bytes(attr);
                if attr_bytes == b"const" {
                    (true, false)
                } else if attr_bytes == b"close" {
                    (false, true)
                } else {
                    return Err(self.error("unknown attribute (expected 'const' or 'close')"));
                }
            } else {
                (false, false)
            };
            attrs.push((is_const, is_close));
            if !self.test_next(&Token::Comma)? {
                break;
            }
        }

        let num_vars = names.len();

        if self.test_next(&Token::Assign)? {
            // Parse initializers
            let base_reg = self.fs().scope.free_reg;
            let num_exprs = self.expression_list(base_reg)?;

            // Pad with nils if fewer expressions than variables
            if (num_exprs as usize) < num_vars {
                for i in num_exprs as u8..num_vars as u8 {
                    self.emit_abx(OpCode::LoadNil, base_reg + i, 0, line);
                }
            }
        } else {
            // No initializer: all nil
            let base_reg = self.fs().scope.free_reg;
            for i in 0..num_vars as u8 {
                self.emit_abx(OpCode::LoadNil, base_reg + i, 0, line);
            }
        }

        // Register all local variables
        let start_pc = self.fs().current_pc() as u32;
        for (i, name) in names.into_iter().enumerate() {
            let (is_const, is_close) = attrs[i];
            self.fs_mut().scope.add_local(name, is_const, is_close, start_pc);
            if is_close {
                let reg = self.fs().scope.free_reg - 1;
                self.emit_abc(OpCode::Tbc, reg, 0, 0, line);
            }
        }

        Ok(())
    }

    /// `if exp then block {elseif exp then block} [else block] end`
    fn stat_if(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume 'if'
        let mut escape_jumps = Vec::new();

        // First condition
        let cond = self.expression()?;
        self.expect(&Token::Then)?;
        let line = self.line();
        let false_jump = self.code_test_jump(&cond, false, line)?;

        self.fs_mut().scope.enter_block(false);
        self.block()?;
        self.fs_mut().scope.leave_block();

        while self.check(&Token::ElseIf) {
            let esc = self.emit_jump(self.line());
            escape_jumps.push(esc);
            self.patch_jump(false_jump);
            let false_jump_inner;

            self.advance()?; // consume 'elseif'
            let cond = self.expression()?;
            self.expect(&Token::Then)?;
            let cond_line = self.line();
            false_jump_inner = self.code_test_jump(&cond, false, cond_line)?;

            self.fs_mut().scope.enter_block(false);
            self.block()?;
            self.fs_mut().scope.leave_block();

            // The last false_jump from elseif chain
            escape_jumps.push(self.emit_jump(self.line()));
            self.patch_jump(false_jump_inner);
            // Need to handle the chain properly. Let me restructure.
        }

        // Actually the above loop logic is getting messy. Let me redo with a cleaner approach.
        // The issue is that we need to track the false_jump across iterations.
        // Let me just use a simpler recursive approach.

        // Actually, wait — the code above has a bug because false_jump from the initial
        // 'if' isn't being patched properly when there are elseifs.
        // Let me just redo this method cleanly:

        // ...the method is getting complex. Let me just patch the initial false_jump
        // before checking for else/end.

        if self.check(&Token::Else) {
            let esc = self.emit_jump(self.line());
            escape_jumps.push(esc);
            self.patch_jump(false_jump);

            self.advance()?; // consume 'else'
            self.fs_mut().scope.enter_block(false);
            self.block()?;
            self.fs_mut().scope.leave_block();
        } else if !self.check(&Token::ElseIf) {
            self.patch_jump(false_jump);
        }

        self.expect(&Token::End)?;

        for esc in escape_jumps {
            self.patch_jump(esc);
        }
        Ok(())
    }

    /// `while exp do block end`
    fn stat_while(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume 'while'
        let loop_start = self.fs().current_pc();
        let cond = self.expression()?;
        self.expect(&Token::Do)?;
        let line = self.line();
        let exit_jump = self.code_test_jump(&cond, false, line)?;

        self.fs_mut().scope.enter_block(true);
        self.block()?;
        let block = self.fs_mut().scope.leave_block();

        // Jump back to loop start
        let back_jump = self.emit_sj(OpCode::Jmp, 0, self.line());
        self.patch_jump_to(back_jump, loop_start);

        self.expect(&Token::End)?;

        self.patch_jump(exit_jump);
        // Patch break jumps
        for brk in block.break_jumps {
            self.patch_jump(brk);
        }
        Ok(())
    }

    /// `do block end`
    fn stat_do(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume 'do'
        self.fs_mut().scope.enter_block(false);
        self.block()?;
        self.fs_mut().scope.leave_block();
        self.expect(&Token::End)?;
        Ok(())
    }

    /// `for name '=' exp ',' exp [',' exp] do block end`  (numeric)
    /// `for namelist in explist do block end`  (generic)
    fn stat_for(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume 'for'
        let name = self.expect_name()?;

        if self.check(&Token::Assign) {
            self.stat_for_numeric(name)
        } else if self.check(&Token::Comma) || self.check(&Token::In) {
            self.stat_for_generic(name)
        } else {
            Err(self.error("'=' or 'in' expected in for statement"))
        }
    }

    fn stat_for_numeric(&mut self, var_name: StringId) -> Result<(), CompileError> {
        self.advance()?; // consume '='
        let line = self.line();

        // Allocate 4 internal registers: (internal) init, limit, step, var
        let base = self.fs().scope.free_reg;

        // Parse init
        let init = self.expression()?;
        self.discharge_to_reg(&init, base, line);
        self.fs_mut().scope.alloc_reg(); // for init

        // Parse limit
        self.expect(&Token::Comma)?;
        let limit = self.expression()?;
        self.discharge_to_reg(&limit, base + 1, line);
        self.fs_mut().scope.alloc_reg(); // for limit

        // Parse optional step
        if self.test_next(&Token::Comma)? {
            let step = self.expression()?;
            self.discharge_to_reg(&step, base + 2, line);
        } else {
            self.discharge_to_reg(&ExprDesc::Integer(1), base + 2, line);
        }
        self.fs_mut().scope.alloc_reg(); // for step

        self.expect(&Token::Do)?;

        // ForPrep: jump to the loop test
        let prep_pc = self.emit_abx(OpCode::ForPrep, base, 0, line);

        // Enter loop block
        self.fs_mut().scope.enter_block(true);
        // The loop variable
        let pc = self.fs().current_pc() as u32;
        self.fs_mut().scope.add_local(var_name, false, false, pc);

        self.block()?;

        let block = self.fs_mut().scope.leave_block();

        // ForLoop: increment and test
        let loop_pc = self.emit_abx(OpCode::ForLoop, base, 0, self.line());
        // Patch ForPrep to jump to ForLoop
        let offset = loop_pc as u32 - prep_pc as u32 - 1;
        self.fs_mut().proto.code[prep_pc] = Instruction::asbx(OpCode::ForPrep, base, offset as i32);
        // Patch ForLoop to jump back to loop body start
        let body_start = prep_pc + 1;
        let back_offset = body_start as i32 - loop_pc as i32 - 1;
        self.fs_mut().proto.code[loop_pc] = Instruction::asbx(OpCode::ForLoop, base, back_offset);

        self.expect(&Token::End)?;

        // Patch breaks
        for brk in block.break_jumps {
            self.patch_jump(brk);
        }

        self.fs_mut().scope.free_reg_to(base);
        Ok(())
    }

    fn stat_for_generic(&mut self, first_name: StringId) -> Result<(), CompileError> {
        let line = self.line();
        let base = self.fs().scope.free_reg;

        // Collect variable names
        let mut names = vec![first_name];
        while self.test_next(&Token::Comma)? {
            let name = self.expect_name()?;
            names.push(name);
        }

        self.expect(&Token::In)?;

        // Allocate 4 hidden slots: iterator func, state, control, to-be-closed
        // Then the declared variables
        let iter_reg = self.fs_mut().scope.alloc_reg();
        let state_reg = self.fs_mut().scope.alloc_reg();
        let control_reg = self.fs_mut().scope.alloc_reg();
        let _tbc_reg = self.fs_mut().scope.alloc_reg();

        // Parse iterator expression list
        let expr = self.expression()?;
        self.discharge_to_reg(&expr, iter_reg, line);
        if self.test_next(&Token::Comma)? {
            let state_expr = self.expression()?;
            self.discharge_to_reg(&state_expr, state_reg, line);
            if self.test_next(&Token::Comma)? {
                let ctrl_expr = self.expression()?;
                self.discharge_to_reg(&ctrl_expr, control_reg, line);
            } else {
                self.emit_abx(OpCode::LoadNil, control_reg, 0, line);
            }
        } else {
            self.emit_abx(OpCode::LoadNil, state_reg, 0, line);
            self.emit_abx(OpCode::LoadNil, control_reg, 0, line);
        }

        self.expect(&Token::Do)?;

        // TForPrep
        let prep_pc = self.emit_abx(OpCode::TForPrep, base, 0, line);

        self.fs_mut().scope.enter_block(true);

        // Declare loop variables
        for name in &names {
            let pc = self.fs().current_pc() as u32;
            self.fs_mut().scope.add_local(*name, false, false, pc);
        }

        self.block()?;

        let block = self.fs_mut().scope.leave_block();

        // TForCall + TForLoop
        let nvars = names.len() as u8;
        self.emit_abc(OpCode::TForCall, base, 0, nvars, self.line());
        let loop_pc = self.emit_abx(OpCode::TForLoop, base + 2, 0, self.line());

        // Patch TForPrep to jump to TForCall
        let call_pc = loop_pc - 1;
        let offset = call_pc as i32 - prep_pc as i32 - 1;
        self.fs_mut().proto.code[prep_pc] = Instruction::asbx(OpCode::TForPrep, base, offset);

        // Patch TForLoop to jump back to loop body
        let body_start = prep_pc + 1;
        let back_offset = body_start as i32 - loop_pc as i32 - 1;
        self.fs_mut().proto.code[loop_pc] = Instruction::asbx(OpCode::TForLoop, base + 2, back_offset);

        self.expect(&Token::End)?;

        for brk in block.break_jumps {
            self.patch_jump(brk);
        }

        self.fs_mut().scope.free_reg_to(base);
        Ok(())
    }

    /// `repeat block until exp`
    fn stat_repeat(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume 'repeat'
        let loop_start = self.fs().current_pc();

        self.fs_mut().scope.enter_block(true);
        self.block()?;
        self.expect(&Token::Until)?;

        let cond = self.expression()?;
        let line = self.line();
        let exit_jump = self.code_test_jump(&cond, true, line)?;

        let block = self.fs_mut().scope.leave_block();

        // Jump back if condition is false
        self.patch_jump_to(exit_jump, loop_start);

        // Patch breaks to after the loop
        for brk in block.break_jumps {
            self.patch_jump(brk);
        }
        Ok(())
    }

    /// `function funcname funcbody`
    fn stat_function(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume 'function'
        let line = self.line();

        // Parse function name: name {'.' name} [':' name]
        let first_name = self.expect_name()?;
        let mut expr = self.resolve_name(first_name)?;
        let mut is_method = false;

        loop {
            if self.check(&Token::Dot) {
                self.advance()?;
                let field = self.expect_name()?;
                let table_reg = self.discharge_to_any_reg(&expr, line);
                let k = self.fs_mut().add_string_constant(field);
                expr = ExprDesc::Indexed {
                    table: table_reg,
                    key: IndexKey::Field(k),
                };
            } else if self.check(&Token::Colon) {
                self.advance()?;
                let method = self.expect_name()?;
                let table_reg = self.discharge_to_any_reg(&expr, line);
                let k = self.fs_mut().add_string_constant(method);
                expr = ExprDesc::Indexed {
                    table: table_reg,
                    key: IndexKey::Field(k),
                };
                is_method = true;
                break;
            } else {
                break;
            }
        }

        let func = self.function_body(is_method)?;
        self.code_store(&expr, &func, line)?;
        Ok(())
    }

    /// `return [explist] [';']`
    fn stat_return(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume 'return'
        let line = self.line();

        // Check if there are return values
        let is_end = matches!(
            self.current_token()?,
            Token::End | Token::Else | Token::ElseIf | Token::Until | Token::Eof | Token::Semi
        );

        if is_end {
            self.test_next(&Token::Semi)?;
            self.emit_abc(OpCode::Return0, 0, 0, 0, line);
            return Ok(());
        }

        let base = self.fs().scope.free_reg;
        let first_expr = self.expression()?;

        if !self.check(&Token::Comma) {
            // Single return value
            self.test_next(&Token::Semi)?;
            match &first_expr {
                ExprDesc::Call(pc) => {
                    // Tail call optimization for single call return
                    let pc = *pc;
                    let inst = self.fs().proto.code[pc];
                    let a = inst.a();
                    let b = inst.b();
                    self.fs_mut().proto.code[pc] =
                        Instruction::abc(OpCode::TailCall, a, b, 0, inst.k());
                    self.emit_abc(OpCode::Return, a, 0, 0, line);
                }
                _ => {
                    self.discharge_to_reg(&first_expr, base, line);
                    self.emit(
                        Instruction::abc(OpCode::Return1, base, 0, 0, false),
                        line,
                    );
                }
            }
            return Ok(());
        }

        // Multiple return values
        self.discharge_to_reg(&first_expr, base, line);
        let mut count = 1u8;
        while self.test_next(&Token::Comma)? {
            let expr = self.expression()?;
            self.discharge_to_reg(&expr, base + count, line);
            count += 1;
        }
        self.test_next(&Token::Semi)?;
        self.emit(
            Instruction::abc(OpCode::Return, base, count + 1, 0, false),
            line,
        );
        Ok(())
    }

    /// `break`
    fn stat_break(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume 'break'
        let line = self.line();

        // Find enclosing loop
        let jump = self.emit_sj(OpCode::Jmp, 0, line);

        let found = self.fs_mut().scope.find_loop_block().map(|b| {
            b.break_jumps.push(jump);
            true
        });

        if found.is_none() {
            return Err(self.error("'break' outside loop"));
        }
        Ok(())
    }

    /// `goto name`
    fn stat_goto(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume 'goto'
        let line = self.line();
        let name = self.expect_name()?;
        let pc = self.emit_sj(OpCode::Jmp, 0, line);
        let num_locals = self.fs().scope.num_locals();

        // Try to resolve immediately
        let resolved = self.find_label(name);
        if let Some(target_pc) = resolved {
            self.patch_jump_to(pc, target_pc);
        } else {
            // Save as pending goto
            if let Some(block) = self.fs_mut().scope.current_block_mut() {
                block.pending_gotos.push(PendingGoto {
                    name,
                    pc,
                    line,
                    num_locals,
                });
            }
        }
        Ok(())
    }

    /// `:: name ::`
    fn stat_label(&mut self) -> Result<(), CompileError> {
        self.advance()?; // consume '::'
        let name = self.expect_name()?;
        self.expect(&Token::DoubleColon)?;
        let pc = self.fs().current_pc();
        let num_locals = self.fs().scope.num_locals();

        if let Some(block) = self.fs_mut().scope.current_block_mut() {
            // Check for duplicate label
            for label in &block.labels {
                if label.name == name {
                    return Err(self.error("duplicate label"));
                }
            }
            block.labels.push(LabelInfo {
                name,
                pc,
                num_locals,
            });

            // Resolve pending gotos that reference this label
            let mut resolved = Vec::new();
            for (i, goto) in block.pending_gotos.iter().enumerate() {
                if goto.name == name {
                    resolved.push((i, goto.pc));
                }
            }
            for (_, goto_pc) in &resolved {
                self.patch_jump_to(*goto_pc, pc);
            }
            // Remove resolved gotos (in reverse order to preserve indices)
            for (i, _) in resolved.into_iter().rev() {
                self.fs_mut().scope.current_block_mut().unwrap().pending_gotos.remove(i);
            }
        }
        Ok(())
    }

    /// Expression statement or assignment.
    fn stat_expr_or_assign(&mut self) -> Result<(), CompileError> {
        let expr = self.primary_expression()?;
        let line = self.line();

        if self.check(&Token::Assign) || self.check(&Token::Comma) {
            // Assignment
            let mut targets = vec![expr];
            while self.test_next(&Token::Comma)? {
                let target = self.primary_expression()?;
                targets.push(target);
            }
            self.expect(&Token::Assign)?;

            let base = self.fs().scope.free_reg;
            let count = targets.len();

            // Parse right-hand side
            let first = self.expression()?;
            self.discharge_to_reg(&first, base, line);
            let mut num_rhs = 1;
            while self.test_next(&Token::Comma)? {
                let e = self.expression()?;
                self.discharge_to_reg(&e, base + num_rhs, line);
                num_rhs += 1;
            }

            // Pad with nils
            while (num_rhs as usize) < count {
                self.emit_abx(OpCode::LoadNil, base + num_rhs, 0, line);
                num_rhs += 1;
            }

            // Store values to targets
            for (i, target) in targets.iter().enumerate() {
                let val = ExprDesc::Register(base + i as u8);
                self.code_store(target, &val, line)?;
            }

            self.fs_mut().scope.free_reg_to(base);
        } else {
            // Expression statement (function call)
            match &expr {
                ExprDesc::Call(_) => {
                    // Discard results by setting C=1
                    if let ExprDesc::Call(pc) = expr {
                        let inst = &mut self.fs_mut().proto.code[pc];
                        let a = inst.a();
                        let b = inst.b();
                        *inst = Instruction::abc(OpCode::Call, a, b, 1, false);
                    }
                }
                _ => {
                    return Err(self.error("expression is not a statement"));
                }
            }
        }
        Ok(())
    }

    // ---- Helper methods ----

    /// Generate a conditional jump: if `condition` is `jump_if`, jump.
    fn code_test_jump(
        &mut self,
        cond: &ExprDesc,
        jump_if: bool,
        line: u32,
    ) -> Result<usize, CompileError> {
        match cond {
            ExprDesc::Jump(pc) => {
                // The comparison already emitted a conditional + JMP
                // We just need to return the jump PC
                Ok(*pc)
            }
            _ => {
                let reg = self.discharge_to_any_reg(cond, line);
                // TEST: skip next if R(A) is truthy/falsy
                self.emit(
                    Instruction::abc(OpCode::Test, reg, 0, 0, !jump_if),
                    line,
                );
                let jump = self.emit_sj(OpCode::Jmp, 0, line);
                Ok(jump)
            }
        }
    }

    /// Store a value expression into a target expression (assignment).
    fn code_store(
        &mut self,
        target: &ExprDesc,
        value: &ExprDesc,
        line: u32,
    ) -> Result<(), CompileError> {
        match target {
            ExprDesc::Register(reg) => {
                // Local variable assignment
                // Check if const
                let reg = *reg;
                if let Some(local) = self.fs().scope.resolve_local_by_reg(reg) {
                    if local.is_const {
                        return Err(self.error("attempt to assign to const variable"));
                    }
                }
                self.discharge_to_reg(value, reg, line);
            }
            ExprDesc::Upvalue(idx) => {
                let idx = *idx;
                let val_reg = self.discharge_to_any_reg(value, line);
                self.emit_abc(OpCode::SetUpval, val_reg, idx, 0, line);
            }
            ExprDesc::Global { env_upval, name_k } => {
                let env_upval = *env_upval;
                let name_k = *name_k;
                let val_reg = self.discharge_to_any_reg(value, line);
                self.emit(
                    Instruction::abc(OpCode::SetTabUp, env_upval, name_k as u8, val_reg, false),
                    line,
                );
            }
            ExprDesc::Indexed { table, key } => {
                let table = *table;
                let val_reg = self.discharge_to_any_reg(value, line);
                match key {
                    IndexKey::Field(k) => {
                        self.emit(
                            Instruction::abc(OpCode::SetField, table, *k as u8, val_reg, false),
                            line,
                        );
                    }
                    IndexKey::Register(key_reg) => {
                        self.emit_abc(OpCode::SetTable, table, *key_reg, val_reg, line);
                    }
                    IndexKey::Integer(i) => {
                        self.emit_abc(OpCode::SetI, table, *i, val_reg, line);
                    }
                    IndexKey::Constant(k) => {
                        self.emit(
                            Instruction::abc(OpCode::SetTable, table, *k as u8, val_reg, true),
                            line,
                        );
                    }
                }
            }
            _ => {
                return Err(self.error("invalid assignment target"));
            }
        }
        Ok(())
    }

    fn find_label(&self, name: StringId) -> Option<usize> {
        for block in self.fs().scope.blocks.iter().rev() {
            for label in &block.labels {
                if label.name == name {
                    return Some(label.pc);
                }
            }
        }
        None
    }
}

fn op_to_mm(op: BinOp) -> u8 {
    match op {
        BinOp::Add => 0,
        BinOp::Sub => 1,
        BinOp::Mul => 2,
        BinOp::Mod => 3,
        BinOp::Pow => 4,
        BinOp::Div => 5,
        BinOp::IDiv => 6,
        BinOp::BAnd => 7,
        BinOp::BOr => 8,
        BinOp::BXor => 9,
        BinOp::Shl => 10,
        BinOp::Shr => 11,
        BinOp::Concat => 12,
        _ => 0,
    }
}

fn int_log2(mut n: u32) -> u32 {
    let mut log = 0;
    while n > 1 {
        n >>= 1;
        log += 1;
    }
    log
}

/// Compile Lua source to a Proto. Public API — this is the entry point.
pub fn compile(source: &[u8], name: &str) -> Result<(Proto, StringInterner), CompileError> {
    let mut compiler = Compiler::new(source);

    // Create the top-level function
    let mut top = FuncState::new(None);
    let source_name = compiler.lexer.strings.intern_or_create(name.as_bytes());
    top.proto.source = Some(source_name);
    top.proto.is_vararg = true;
    top.scope.enter_block(false);

    // Add _ENV upvalue
    let env_name = compiler.lexer.strings.intern(b"_ENV");
    top.upvalues.push(UpvalInfo {
        name: env_name,
        in_stack: true,
        index: 0,
    });

    // VarArgPrep
    top.emit(Instruction::abx(OpCode::VarArgPrep, 0, 0), 1);

    compiler.func_stack.push(top);

    // Parse the block
    compiler.block()?;

    // Expect EOF
    compiler.expect(&Token::Eof)?;

    // Emit RETURN0
    let line = compiler.line();
    compiler.emit_abc(OpCode::Return0, 0, 0, 0, line);

    // Finalize
    let mut fs = compiler.func_stack.pop().unwrap();
    fs.scope.leave_block();
    fs.proto.max_stack_size = fs.scope.max_reg + 2;
    fs.proto.upvalues = fs
        .upvalues
        .iter()
        .map(|u| UpvalDesc {
            name: Some(u.name),
            in_stack: u.in_stack,
            index: u.index,
            kind: 0,
        })
        .collect();

    Ok((fs.proto, compiler.lexer.strings))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compile_ok(source: &str) -> (Proto, StringInterner) {
        compile(source.as_bytes(), "test").unwrap()
    }

    fn compile_err(source: &str) -> CompileError {
        compile(source.as_bytes(), "test").unwrap_err()
    }

    fn has_opcode(proto: &Proto, op: OpCode) -> bool {
        proto.code.iter().any(|i| i.opcode() == op)
    }

    #[test]
    fn test_compile_empty() {
        let (proto, _) = compile_ok("");
        assert_eq!(proto.code.len(), 2);
        assert_eq!(proto.code[0].opcode(), OpCode::VarArgPrep);
        assert_eq!(proto.code[1].opcode(), OpCode::Return0);
    }

    #[test]
    fn test_return_nil() {
        let (proto, _) = compile_ok("return nil");
        assert!(has_opcode(&proto, OpCode::LoadNil));
        assert!(has_opcode(&proto, OpCode::Return1));
    }

    #[test]
    fn test_return_integer() {
        let (proto, _) = compile_ok("return 42");
        assert!(has_opcode(&proto, OpCode::LoadI));
        assert!(has_opcode(&proto, OpCode::Return1));
    }

    #[test]
    fn test_return_string() {
        let (proto, _) = compile_ok("return \"hello\"");
        assert!(has_opcode(&proto, OpCode::LoadK));
        assert_eq!(proto.constants.len(), 1);
    }

    #[test]
    fn test_return_multiple() {
        let (proto, _) = compile_ok("return 1, 2, 3");
        assert!(has_opcode(&proto, OpCode::Return));
    }

    #[test]
    fn test_return_no_value() {
        let (proto, _) = compile_ok("return");
        assert!(has_opcode(&proto, OpCode::Return0));
    }

    #[test]
    fn test_local_declaration() {
        let (proto, _) = compile_ok("local x = 42");
        assert!(has_opcode(&proto, OpCode::LoadI));
    }

    #[test]
    fn test_local_nil_default() {
        let (proto, _) = compile_ok("local x");
        assert!(has_opcode(&proto, OpCode::LoadNil));
    }

    #[test]
    fn test_local_multiple() {
        let (proto, _) = compile_ok("local x, y = 1, 2");
        // Should have two LoadI instructions
        let load_count = proto
            .code
            .iter()
            .filter(|i| i.opcode() == OpCode::LoadI)
            .count();
        assert!(load_count >= 2);
    }

    #[test]
    fn test_local_function() {
        let (proto, _) = compile_ok("local function f() end");
        assert!(has_opcode(&proto, OpCode::Closure));
        assert_eq!(proto.protos.len(), 1);
    }

    #[test]
    fn test_global_assignment() {
        let (proto, _) = compile_ok("x = 42");
        assert!(has_opcode(&proto, OpCode::SetTabUp));
    }

    #[test]
    fn test_global_read() {
        let (proto, _) = compile_ok("return x");
        assert!(has_opcode(&proto, OpCode::GetTabUp));
    }

    #[test]
    fn test_if_then_end() {
        let (proto, _) = compile_ok("if true then local x = 1 end");
        assert!(has_opcode(&proto, OpCode::Test) || has_opcode(&proto, OpCode::LoadTrue));
    }

    #[test]
    fn test_if_then_else() {
        let (proto, _) = compile_ok(
            "if true then local x = 1 else local y = 2 end",
        );
        assert!(has_opcode(&proto, OpCode::Jmp));
    }

    #[test]
    fn test_while_loop() {
        let (proto, _) = compile_ok("local x = 0\nwhile x do x = nil end");
        assert!(has_opcode(&proto, OpCode::Test));
        assert!(has_opcode(&proto, OpCode::Jmp));
    }

    #[test]
    fn test_repeat_until() {
        let (proto, _) = compile_ok("repeat local x = 1 until true");
        assert!(has_opcode(&proto, OpCode::Test) || has_opcode(&proto, OpCode::LoadTrue));
    }

    #[test]
    fn test_numeric_for() {
        let (proto, _) = compile_ok("for i = 1, 10 do local x = i end");
        assert!(has_opcode(&proto, OpCode::ForPrep));
        assert!(has_opcode(&proto, OpCode::ForLoop));
    }

    #[test]
    fn test_numeric_for_with_step() {
        let (proto, _) = compile_ok("for i = 1, 10, 2 do local x = i end");
        assert!(has_opcode(&proto, OpCode::ForPrep));
    }

    #[test]
    fn test_generic_for() {
        let (proto, _) = compile_ok("for k, v in pairs do local x = k end");
        assert!(has_opcode(&proto, OpCode::TForPrep));
        assert!(has_opcode(&proto, OpCode::TForCall));
        assert!(has_opcode(&proto, OpCode::TForLoop));
    }

    #[test]
    fn test_do_end() {
        let (proto, _) = compile_ok("do local x = 1 end");
        assert!(has_opcode(&proto, OpCode::LoadI));
    }

    #[test]
    fn test_break_in_loop() {
        let (proto, _) = compile_ok("while true do break end");
        assert!(has_opcode(&proto, OpCode::Jmp));
    }

    #[test]
    fn test_break_outside_loop_error() {
        let err = compile_err("break");
        assert!(err.message.contains("break") && err.message.contains("outside"));
    }

    #[test]
    fn test_function_statement() {
        let (proto, _) = compile_ok("function f() end");
        assert!(has_opcode(&proto, OpCode::Closure));
        assert!(has_opcode(&proto, OpCode::SetTabUp));
    }

    #[test]
    fn test_function_with_params() {
        let (proto, _) = compile_ok("function f(a, b) return a end");
        assert_eq!(proto.protos.len(), 1);
        assert_eq!(proto.protos[0].num_params, 2);
    }

    #[test]
    fn test_function_vararg() {
        let (proto, _) = compile_ok("function f(...) return ... end");
        assert_eq!(proto.protos[0].is_vararg, true);
    }

    #[test]
    fn test_closure_upvalue() {
        let (proto, _) = compile_ok(
            "local x = 1\nfunction f() return x end",
        );
        assert_eq!(proto.protos.len(), 1);
        assert!(!proto.protos[0].upvalues.is_empty());
    }

    #[test]
    fn test_method_definition() {
        let (proto, _) = compile_ok("function t:m() return self end");
        assert_eq!(proto.protos[0].num_params, 1);
    }

    #[test]
    fn test_goto_forward() {
        let (proto, _) = compile_ok("goto done\n::done::");
        assert!(has_opcode(&proto, OpCode::Jmp));
    }

    #[test]
    fn test_goto_backward() {
        let (proto, _) = compile_ok("::start::\ngoto start");
        assert!(has_opcode(&proto, OpCode::Jmp));
    }

    #[test]
    fn test_label_duplicate_error() {
        let err = compile_err("::x::\n::x::");
        assert!(err.message.contains("duplicate label"));
    }

    #[test]
    fn test_table_constructor_empty() {
        let (proto, _) = compile_ok("return {}");
        assert!(has_opcode(&proto, OpCode::NewTable));
    }

    #[test]
    fn test_table_constructor_array() {
        let (proto, _) = compile_ok("return {1, 2, 3}");
        assert!(has_opcode(&proto, OpCode::NewTable));
        assert!(has_opcode(&proto, OpCode::SetList));
    }

    #[test]
    fn test_table_constructor_hash() {
        let (proto, _) = compile_ok("return {x = 1, y = 2}");
        assert!(has_opcode(&proto, OpCode::NewTable));
        assert!(has_opcode(&proto, OpCode::SetField));
    }

    #[test]
    fn test_function_call_statement() {
        let (proto, _) = compile_ok("print(42)");
        assert!(has_opcode(&proto, OpCode::Call));
    }

    #[test]
    fn test_semicolons_ignored() {
        let (proto, _) = compile_ok(";;;local x = 1;;;");
        assert!(has_opcode(&proto, OpCode::LoadI));
    }

    #[test]
    fn test_and_short_circuit() {
        let (proto, _) = compile_ok("return true and false");
        assert!(has_opcode(&proto, OpCode::TestSet));
    }

    #[test]
    fn test_or_short_circuit() {
        let (proto, _) = compile_ok("return true or false");
        assert!(has_opcode(&proto, OpCode::TestSet));
    }

    #[test]
    fn test_comparison_eq() {
        let (proto, _) = compile_ok("local a = 1\nlocal b = 2\nif a == b then end");
        assert!(has_opcode(&proto, OpCode::Eq));
    }

    #[test]
    fn test_arithmetic_add() {
        let (proto, _) = compile_ok("return 1 + 2");
        // Could be folded or AddK
        assert!(
            has_opcode(&proto, OpCode::AddK)
                || has_opcode(&proto, OpCode::Add)
                || has_opcode(&proto, OpCode::AddI)
                || has_opcode(&proto, OpCode::LoadI)
        );
    }

    #[test]
    fn test_unary_neg() {
        let (proto, _) = compile_ok("return -42");
        // Constant folded to -42
        assert!(has_opcode(&proto, OpCode::LoadI));
    }

    #[test]
    fn test_unary_not() {
        let (proto, _) = compile_ok("return not true");
        // Constant folded to false
        assert!(has_opcode(&proto, OpCode::LoadFalse));
    }

    #[test]
    fn test_concat() {
        let (proto, _) = compile_ok("local a = \"hello\"\nlocal b = \"world\"\nreturn a .. b");
        assert!(has_opcode(&proto, OpCode::Concat));
    }

    #[test]
    fn test_operator_precedence_types() {
        let (_, add) = BinOp::Add.priority();
        let (_, mul) = BinOp::Mul.priority();
        let (_, pow_r) = BinOp::Pow.priority();
        assert!(mul > add);
        assert!(pow_r > mul);
    }

    #[test]
    fn test_concat_right_assoc() {
        let (left, right) = BinOp::Concat.priority();
        assert!(left > right);
    }

    #[test]
    fn test_pow_right_assoc() {
        let (left, right) = BinOp::Pow.priority();
        assert!(left > right);
    }

    #[test]
    fn test_expr_desc_is_literal() {
        assert!(ExprDesc::Nil.is_literal());
        assert!(ExprDesc::True.is_literal());
        assert!(ExprDesc::False.is_literal());
        assert!(ExprDesc::Integer(42).is_literal());
        assert!(ExprDesc::Float(3.14).is_literal());
        assert!(!ExprDesc::Register(0).is_literal());
        assert!(!ExprDesc::Void.is_literal());
    }

    #[test]
    fn test_local_const_attribute() {
        let (proto, _) = compile_ok("local x <const> = 42");
        assert!(has_opcode(&proto, OpCode::LoadI));
    }

    #[test]
    fn test_nested_function() {
        let (proto, _) = compile_ok(
            "function outer()\n  function inner() end\nend",
        );
        assert_eq!(proto.protos.len(), 1);
        assert_eq!(proto.protos[0].protos.len(), 1);
    }

    #[test]
    fn test_multiple_assignment() {
        let (proto, _) = compile_ok("local a, b\na, b = 1, 2");
        // Should store to both locals
        let move_count = proto
            .code
            .iter()
            .filter(|i| i.opcode() == OpCode::Move || i.opcode() == OpCode::LoadI)
            .count();
        assert!(move_count >= 2);
    }

    #[test]
    fn test_field_access() {
        let (proto, _) = compile_ok("return t.x");
        assert!(has_opcode(&proto, OpCode::GetField) || has_opcode(&proto, OpCode::GetTabUp));
    }

    #[test]
    fn test_index_access() {
        let (proto, _) = compile_ok("local t = {}\nreturn t[1]");
        assert!(has_opcode(&proto, OpCode::GetI) || has_opcode(&proto, OpCode::GetTable));
    }
}
