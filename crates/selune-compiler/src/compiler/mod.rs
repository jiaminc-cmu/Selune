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
        let mut expr = match self.current_token()?.clone() {
            Token::Name(name) => {
                self.advance()?;
                self.resolve_name(name)?
            }
            Token::LParen => {
                self.advance()?;
                let e = self.expression()?;
                self.expect(&Token::RParen)?;
                // Parenthesized expression: limit to single value
                match e {
                    ExprDesc::Call(pc) | ExprDesc::Vararg(pc) => {
                        // Force single result
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

        // Parse suffix chain: .field, [key], :method(), ()
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
                    // SELF instruction
                    let self_reg = self.fs_mut().scope.alloc_reg();
                    self.emit(
                        Instruction::abc(OpCode::Self_, self_reg, table_reg, k as u8, true),
                        line,
                    );
                    let _obj_reg = self.fs_mut().scope.alloc_reg(); // slot for self
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
                Token::Name(name) if self.peek_is_assign() => {
                    // name = expr
                    self.advance()?;
                    self.expect(&Token::Assign)?;
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

    /// Peek ahead to check if the next token after current Name is '='.
    fn peek_is_assign(&self) -> bool {
        // We need to check if after the current Name token, there's an '='
        // Since we're single-token lookahead, check the next token
        // The lexer keeps current, so we check what follows
        // Actually for table constructors, after Name we check if next is '='
        // Since we have 1-token lookahead, we need to peek through the lexer
        // For simplicity, look at position after current name
        if let Ok(st) = self.lexer.current() {
            matches!(st.token, Token::Assign)
        } else {
            false
        }
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

        self.fs_mut().scope.free_reg_to(left_reg);
        let right = self.sub_expression(right_prec)?;
        let right_line = self.line();
        self.discharge_to_reg(&right, left_reg, right_line);
        self.fs_mut().scope.free_reg_to(left_reg + 1);

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
        // _ENV is always upvalue 0 of the top-level function
        let env_idx = self.resolve_upvalue_env();
        let line = self.line();
        let k = self.fs_mut().add_string_constant(name);
        let reg = self.fs_mut().scope.alloc_reg();
        self.emit(
            Instruction::abc(OpCode::GetTabUp, reg, env_idx, k as u8, false),
            line,
        );
        Ok(ExprDesc::Register(reg))
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

    // Stub statements — to be filled in commit 8.
    fn stat_local(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_if(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_while(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_do(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_for(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_repeat(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_function(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_return(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_break(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_goto(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_label(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
    }
    fn stat_expr_or_assign(&mut self) -> Result<(), CompileError> {
        Err(self.error("statements not yet implemented"))
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
    let source_name = compiler.lexer.strings.intern(name.as_bytes());
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

    fn compile_expr(source: &str) -> Result<(Proto, StringInterner), CompileError> {
        // Wrap expression in a minimal statement: `return <expr>`
        let wrapped = format!("return {source}");
        compile(wrapped.as_bytes(), "test")
    }

    #[test]
    fn test_compile_empty() {
        let (proto, _) = compile(b"", "test").unwrap();
        // Should have VarArgPrep + Return0
        assert_eq!(proto.code.len(), 2);
        assert_eq!(proto.code[0].opcode(), OpCode::VarArgPrep);
        assert_eq!(proto.code[1].opcode(), OpCode::Return0);
    }

    #[test]
    fn test_compile_nil_literal() {
        // Can't test expressions directly without statements yet,
        // so just verify the compiler doesn't crash on empty input
        let result = compile(b"", "test");
        assert!(result.is_ok());
    }

    #[test]
    fn test_operator_precedence_types() {
        // Verify precedence ordering
        let (_, add) = BinOp::Add.priority();
        let (_, mul) = BinOp::Mul.priority();
        let (_, pow_r) = BinOp::Pow.priority();
        assert!(mul > add);
        assert!(pow_r > mul);
    }

    #[test]
    fn test_concat_right_assoc() {
        let (left, right) = BinOp::Concat.priority();
        assert!(left > right, "concat should be right-associative (left > right)");
    }

    #[test]
    fn test_pow_right_assoc() {
        let (left, right) = BinOp::Pow.priority();
        assert!(left > right, "pow should be right-associative (left > right)");
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
}
