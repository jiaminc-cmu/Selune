/// Bytecode disassembler (luac -l style output).
use crate::opcode::{Instruction, InstructionFormat};
use crate::proto::{Constant, Proto};
use selune_core::string::StringInterner;
use std::fmt::Write;

/// Disassemble a complete Proto into a human-readable string.
pub fn disassemble(proto: &Proto, strings: &StringInterner) -> String {
    let mut out = String::new();
    disassemble_proto(&mut out, proto, strings, 0);
    out
}

fn disassemble_proto(out: &mut String, proto: &Proto, strings: &StringInterner, level: usize) {
    let indent = "  ".repeat(level);

    // Header
    let vararg = if proto.is_vararg { "+" } else { "" };
    writeln!(
        out,
        "{indent}function ({}{vararg} params, {} slots, {} upvalues, {} constants, {} functions)",
        proto.num_params,
        proto.max_stack_size,
        proto.upvalues.len(),
        proto.constants.len(),
        proto.protos.len(),
    )
    .unwrap();

    // Instructions
    for (pc, inst) in proto.code.iter().enumerate() {
        let line = proto.get_line(pc);
        let line_str = if line > 0 {
            format!("[{line}]")
        } else {
            "[-]".to_string()
        };
        write!(out, "{indent}\t{}\t{:>5}\t", pc + 1, line_str).unwrap();
        disasm_instruction(out, inst, proto, strings);
        writeln!(out).unwrap();
    }

    // Constants
    if !proto.constants.is_empty() {
        writeln!(out, "{indent}constants ({}):", proto.constants.len()).unwrap();
        for (i, k) in proto.constants.iter().enumerate() {
            write!(out, "{indent}\t{}\t", i).unwrap();
            match k {
                Constant::Nil => writeln!(out, "nil").unwrap(),
                Constant::Boolean(b) => writeln!(out, "{b}").unwrap(),
                Constant::Integer(i) => writeln!(out, "{i}").unwrap(),
                Constant::Float(f) => writeln!(out, "{f}").unwrap(),
                Constant::String(id) => {
                    let bytes = strings.get_bytes(*id);
                    if let Ok(s) = std::str::from_utf8(bytes) {
                        writeln!(out, "\"{s}\"").unwrap();
                    } else {
                        writeln!(out, "<binary string>").unwrap();
                    }
                }
            }
        }
    }

    // Upvalues
    if !proto.upvalues.is_empty() {
        writeln!(out, "{indent}upvalues ({}):", proto.upvalues.len()).unwrap();
        for (i, up) in proto.upvalues.iter().enumerate() {
            let name = up
                .name
                .map(|id| {
                    std::str::from_utf8(strings.get_bytes(id))
                        .unwrap_or("?")
                        .to_string()
                })
                .unwrap_or_else(|| "-".to_string());
            writeln!(
                out,
                "{indent}\t{}\t{}\t{}\t{}",
                i,
                name,
                if up.in_stack { 1 } else { 0 },
                up.index
            )
            .unwrap();
        }
    }

    // Nested protos
    for (i, p) in proto.protos.iter().enumerate() {
        writeln!(out, "{indent}function [{i}]:").unwrap();
        disassemble_proto(out, p, strings, level + 1);
    }
}

/// Disassemble a single instruction into the output string.
pub fn disasm_instruction(
    out: &mut String,
    inst: &Instruction,
    proto: &Proto,
    strings: &StringInterner,
) {
    let op = inst.opcode();
    write!(out, "{:<12}", op.name()).unwrap();

    match op.format() {
        InstructionFormat::IABC => {
            write!(out, "{} {} {}", inst.a(), inst.b(), inst.c()).unwrap();
            if inst.k() {
                write!(out, " ; k").unwrap();
            }
        }
        InstructionFormat::IABx => {
            write!(out, "{} {}", inst.a(), inst.bx()).unwrap();
            // If it's a LoadK, show the constant
            if op == crate::opcode::OpCode::LoadK {
                let idx = inst.bx() as usize;
                if idx < proto.constants.len() {
                    write!(out, "\t; ").unwrap();
                    format_constant(out, &proto.constants[idx], strings);
                }
            } else if op == crate::opcode::OpCode::Closure {
                write!(out, "\t; function [{}]", inst.bx()).unwrap();
            }
        }
        InstructionFormat::IAsBx => {
            write!(out, "{} {}", inst.a(), inst.sbx()).unwrap();
        }
        InstructionFormat::IAx => {
            write!(out, "{}", inst.ax_field()).unwrap();
        }
        InstructionFormat::IsJ => {
            write!(out, "{}", inst.get_sj()).unwrap();
            let target = inst.get_sj();
            write!(out, "\t; to ?+{target}").unwrap();
        }
    }
}

fn format_constant(out: &mut String, k: &Constant, strings: &StringInterner) {
    match k {
        Constant::Nil => write!(out, "nil").unwrap(),
        Constant::Boolean(b) => write!(out, "{b}").unwrap(),
        Constant::Integer(i) => write!(out, "{i}").unwrap(),
        Constant::Float(f) => write!(out, "{f}").unwrap(),
        Constant::String(id) => {
            let bytes = strings.get_bytes(*id);
            if let Ok(s) = std::str::from_utf8(bytes) {
                write!(out, "\"{s}\"").unwrap();
            } else {
                write!(out, "<binary>").unwrap();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::opcode::OpCode;

    #[test]
    fn test_disassemble_empty() {
        let p = Proto::new();
        let s = StringInterner::new();
        let out = disassemble(&p, &s);
        assert!(out.contains("function"));
        assert!(out.contains("0 params"));
    }

    #[test]
    fn test_disassemble_with_instructions() {
        let mut p = Proto::new();
        let mut s = StringInterner::new();
        let hello_id = s.intern(b"hello");

        p.emit(Instruction::abc(OpCode::Move, 0, 1, 0, false), 1);
        p.add_constant(Constant::String(hello_id));
        p.emit(Instruction::abx(OpCode::LoadK, 0, 0), 2);

        let out = disassemble(&p, &s);
        assert!(out.contains("MOVE"));
        assert!(out.contains("LOADK"));
        assert!(out.contains("\"hello\""));
    }

    #[test]
    fn test_disasm_jmp() {
        let mut p = Proto::new();
        let s = StringInterner::new();
        p.emit(Instruction::sj(OpCode::Jmp, 5), 1);
        let out = disassemble(&p, &s);
        assert!(out.contains("JMP"));
        assert!(out.contains("5"));
    }

    #[test]
    fn test_disassemble_format() {
        let mut p = Proto::new();
        let s = StringInterner::new();
        p.num_params = 2;
        p.is_vararg = true;
        p.max_stack_size = 10;
        let out = disassemble(&p, &s);
        assert!(out.contains("2+ params"));
        assert!(out.contains("10 slots"));
    }
}
