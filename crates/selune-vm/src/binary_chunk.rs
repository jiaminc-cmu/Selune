//! Lua 5.4 binary chunk serialization (dump) and deserialization (undump).
//!
//! Format follows PUC Lua 5.4 exactly so that chunks produced by string.dump
//! can be loaded back, and chunks from PUC luac can be loaded too.

use selune_compiler::opcode::Instruction;
use selune_compiler::proto::{AbsLineInfo, Constant, LocalVar, Proto, UpvalDesc};
use selune_core::string::{StringId, StringInterner};

// Lua 5.4 binary header constants
const LUA_SIGNATURE: &[u8; 4] = b"\x1bLua";
const LUAC_VERSION: u8 = 0x54; // Lua 5.4
const LUAC_FORMAT: u8 = 0;
const LUAC_DATA: &[u8; 6] = b"\x19\x93\r\n\x1a\n";
const INSTRUCTION_SIZE: u8 = 4;
const LUA_INTEGER_SIZE: u8 = 8;
const LUA_NUMBER_SIZE: u8 = 8;
const LUAC_INT: i64 = 0x5678;
const LUAC_NUM: f64 = 370.5;

// Lua constant type tags
const LUA_TNIL: u8 = 0;
const LUA_TBOOLEAN: u8 = 1;
const LUA_TNUMBER: u8 = 3;
const LUA_TSTRING: u8 = 4;
const LUA_VFALSE: u8 = LUA_TBOOLEAN; // 1
const LUA_VTRUE: u8 = LUA_TBOOLEAN | (1 << 4); // 0x11
const LUA_VNUMINT: u8 = LUA_TNUMBER; // 3
const LUA_VNUMFLT: u8 = LUA_TNUMBER | (1 << 4); // 0x13
const LUA_VSHRSTR: u8 = LUA_TSTRING; // 4
const LUA_VLNGSTR: u8 = LUA_TSTRING | (1 << 4); // 0x14

// ─── Dumper ─────────────────────────────────────────────────────────────

/// Serialize a Proto and all its children into Lua 5.4 binary format.
pub fn dump(proto: &Proto, strings: &StringInterner, strip: bool) -> Vec<u8> {
    let mut out = Vec::new();
    write_header(&mut out);
    // Number of upvalues for the main chunk
    out.push(proto.upvalues.len() as u8);
    write_function(&mut out, proto, strings, strip, None);
    out
}

fn write_header(out: &mut Vec<u8>) {
    out.extend_from_slice(LUA_SIGNATURE);
    out.push(LUAC_VERSION);
    out.push(LUAC_FORMAT);
    out.extend_from_slice(LUAC_DATA);
    out.push(INSTRUCTION_SIZE);
    out.push(LUA_INTEGER_SIZE);
    out.push(LUA_NUMBER_SIZE);
    out.extend_from_slice(&LUAC_INT.to_le_bytes());
    out.extend_from_slice(&LUAC_NUM.to_le_bytes());
}

fn write_size(out: &mut Vec<u8>, mut n: usize) {
    // Lua 5.4 uses a variable-length size encoding:
    // Each byte holds 7 bits of the number. The high bit is set on the LAST byte.
    n += 1; // Lua adds 1 to the size
    let mut buf = [0u8; 10];
    let mut i = 0;
    loop {
        buf[i] = (n & 0x7f) as u8;
        n >>= 7;
        i += 1;
        if n == 0 {
            break;
        }
    }
    // Write bytes in reverse order, with high bit on last byte written
    for j in (1..i).rev() {
        out.push(buf[j]);
    }
    out.push(buf[0] | 0x80);
}

fn write_string(out: &mut Vec<u8>, s: Option<&[u8]>) {
    match s {
        None => write_size(out, 0),
        Some(bytes) => {
            write_size(out, bytes.len() + 1);
            out.extend_from_slice(bytes);
        }
    }
}

fn write_int(out: &mut Vec<u8>, n: i32) {
    write_size(out, n as usize);
}

fn write_function(
    out: &mut Vec<u8>,
    proto: &Proto,
    strings: &StringInterner,
    strip: bool,
    parent_source: Option<&[u8]>,
) {
    // Source name
    let source_bytes = proto.source.map(|sid| strings.get_bytes(sid));
    if strip {
        write_string(out, None);
    } else if source_bytes == parent_source.map(Some).unwrap_or(None) {
        // Same source as parent: write empty to save space
        write_string(out, None);
    } else {
        write_string(out, source_bytes);
    }

    // linedefined, lastlinedefined
    write_int(out, proto.linedefined as i32);
    write_int(out, proto.lastlinedefined as i32);

    // numparams, is_vararg, maxstacksize
    out.push(proto.num_params);
    out.push(if proto.is_vararg { 1 } else { 0 });
    out.push(proto.max_stack_size);

    // Code
    write_int(out, proto.code.len() as i32);
    for inst in &proto.code {
        out.extend_from_slice(&inst.0.to_le_bytes());
    }

    // Constants
    write_int(out, proto.constants.len() as i32);
    for k in &proto.constants {
        match k {
            Constant::Nil => out.push(LUA_TNIL),
            Constant::Boolean(false) => out.push(LUA_VFALSE),
            Constant::Boolean(true) => out.push(LUA_VTRUE),
            Constant::Integer(i) => {
                out.push(LUA_VNUMINT);
                out.extend_from_slice(&i.to_le_bytes());
            }
            Constant::Float(f) => {
                out.push(LUA_VNUMFLT);
                out.extend_from_slice(&f.to_le_bytes());
            }
            Constant::String(sid) => {
                let bytes = strings.get_bytes(*sid);
                if bytes.len() <= 40 {
                    out.push(LUA_VSHRSTR);
                } else {
                    out.push(LUA_VLNGSTR);
                }
                write_string(out, Some(bytes));
            }
        }
    }

    // Upvalues
    write_int(out, proto.upvalues.len() as i32);
    for uv in &proto.upvalues {
        out.push(if uv.in_stack { 1 } else { 0 });
        out.push(uv.index);
        out.push(uv.kind);
    }

    // Protos (child functions)
    write_int(out, proto.protos.len() as i32);
    for child in &proto.protos {
        write_function(out, child, strings, strip, source_bytes);
    }

    // Debug info
    if strip {
        // Line info
        write_int(out, 0);
        // Abs line info
        write_int(out, 0);
        // Local vars
        write_int(out, 0);
        // Upvalue names
        write_int(out, 0);
    } else {
        // Line info
        write_int(out, proto.line_info.len() as i32);
        for &li in &proto.line_info {
            out.push(li as u8);
        }

        // Abs line info
        write_int(out, proto.abs_line_info.len() as i32);
        for abs in &proto.abs_line_info {
            write_int(out, abs.pc as i32);
            write_int(out, abs.line as i32);
        }

        // Local vars
        write_int(out, proto.local_vars.len() as i32);
        for lv in &proto.local_vars {
            let name_bytes = strings.get_bytes(lv.name);
            write_string(out, Some(name_bytes));
            write_int(out, lv.start_pc as i32);
            write_int(out, lv.end_pc as i32);
        }

        // Upvalue names
        write_int(out, proto.upvalues.len() as i32);
        for uv in &proto.upvalues {
            match uv.name {
                Some(sid) => write_string(out, Some(strings.get_bytes(sid))),
                None => write_string(out, None),
            }
        }
    }
}

// ─── Undumper ───────────────────────────────────────────────────────────

/// Error type for undump failures.
#[derive(Debug)]
pub struct UndumpError {
    pub message: String,
}

impl std::fmt::Display for UndumpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

struct Reader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(data: &'a [u8]) -> Self {
        Reader { data, pos: 0 }
    }

    fn remaining(&self) -> usize {
        self.data.len() - self.pos
    }

    fn read_byte(&mut self) -> Result<u8, UndumpError> {
        if self.pos >= self.data.len() {
            return Err(UndumpError {
                message: "truncated binary chunk".to_string(),
            });
        }
        let b = self.data[self.pos];
        self.pos += 1;
        Ok(b)
    }

    fn read_bytes(&mut self, n: usize) -> Result<&'a [u8], UndumpError> {
        if self.pos + n > self.data.len() {
            return Err(UndumpError {
                message: "truncated binary chunk".to_string(),
            });
        }
        let slice = &self.data[self.pos..self.pos + n];
        self.pos += n;
        Ok(slice)
    }

    fn read_u32_le(&mut self) -> Result<u32, UndumpError> {
        let bytes = self.read_bytes(4)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    fn read_i64_le(&mut self) -> Result<i64, UndumpError> {
        let bytes = self.read_bytes(8)?;
        Ok(i64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    fn read_f64_le(&mut self) -> Result<f64, UndumpError> {
        let bytes = self.read_bytes(8)?;
        Ok(f64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    fn read_size(&mut self) -> Result<usize, UndumpError> {
        // Variable-length size: read bytes until high bit is set
        let mut n: usize = 0;
        loop {
            let b = self.read_byte()?;
            n = (n << 7) | (b & 0x7f) as usize;
            if b & 0x80 != 0 {
                break;
            }
        }
        // Lua adds 1 during write, subtract 1 here
        Ok(n.wrapping_sub(1))
    }

    fn read_int(&mut self) -> Result<i32, UndumpError> {
        self.read_size().map(|n| n as i32)
    }

    fn read_lua_string(&mut self, strings: &mut StringInterner) -> Result<Option<StringId>, UndumpError> {
        let size = self.read_size()?;
        if size == 0 {
            return Ok(None);
        }
        let len = size - 1; // actual string length
        let bytes = self.read_bytes(len)?;
        Ok(Some(strings.intern(bytes)))
    }
}

/// Deserialize a Lua 5.4 binary chunk into a Proto.
pub fn undump(data: &[u8], name: &str, strings: &mut StringInterner) -> Result<Proto, UndumpError> {
    let mut reader = Reader::new(data);

    // Verify header
    verify_header(&mut reader, name)?;

    // Number of upvalues
    let _num_upvalues = reader.read_byte()?;

    // Read the main function
    let proto = read_function(&mut reader, strings, None)?;

    Ok(proto)
}

fn verify_header(reader: &mut Reader, name: &str) -> Result<(), UndumpError> {
    // Signature
    let sig = reader.read_bytes(4)?;
    if sig != LUA_SIGNATURE {
        return Err(UndumpError {
            message: format!("{}: not a binary chunk", name),
        });
    }

    // Version
    let version = reader.read_byte()?;
    if version != LUAC_VERSION {
        return Err(UndumpError {
            message: format!("{}: version mismatch", name),
        });
    }

    // Format
    let format = reader.read_byte()?;
    if format != LUAC_FORMAT {
        return Err(UndumpError {
            message: format!("{}: format mismatch", name),
        });
    }

    // LUAC_DATA
    let luac_data = reader.read_bytes(6)?;
    if luac_data != LUAC_DATA {
        return Err(UndumpError {
            message: format!("{}: corrupted chunk", name),
        });
    }

    // Sizes
    let inst_size = reader.read_byte()?;
    if inst_size != INSTRUCTION_SIZE {
        return Err(UndumpError {
            message: format!("{}: int size mismatch", name),
        });
    }
    let int_size = reader.read_byte()?;
    if int_size != LUA_INTEGER_SIZE {
        return Err(UndumpError {
            message: format!("{}: integer size mismatch", name),
        });
    }
    let num_size = reader.read_byte()?;
    if num_size != LUA_NUMBER_SIZE {
        return Err(UndumpError {
            message: format!("{}: number size mismatch", name),
        });
    }

    // LUAC_INT
    let luac_int = reader.read_i64_le()?;
    if luac_int != LUAC_INT {
        return Err(UndumpError {
            message: format!("{}: endianness mismatch", name),
        });
    }

    // LUAC_NUM
    let luac_num = reader.read_f64_le()?;
    if luac_num != LUAC_NUM {
        return Err(UndumpError {
            message: format!("{}: float format mismatch", name),
        });
    }

    Ok(())
}

fn read_function(
    reader: &mut Reader,
    strings: &mut StringInterner,
    parent_source: Option<StringId>,
) -> Result<Proto, UndumpError> {
    let mut proto = Proto::new();

    // Source name
    let source = reader.read_lua_string(strings)?;
    proto.source = source.or(parent_source);
    let effective_source = proto.source;

    // linedefined, lastlinedefined
    proto.linedefined = reader.read_int()? as u32;
    proto.lastlinedefined = reader.read_int()? as u32;

    // numparams, is_vararg, maxstacksize
    proto.num_params = reader.read_byte()?;
    proto.is_vararg = reader.read_byte()? != 0;
    proto.max_stack_size = reader.read_byte()?;

    // Code
    let code_size = reader.read_int()? as usize;
    proto.code = Vec::with_capacity(code_size);
    for _ in 0..code_size {
        let inst = reader.read_u32_le()?;
        proto.code.push(Instruction(inst));
    }

    // Constants
    let const_size = reader.read_int()? as usize;
    proto.constants = Vec::with_capacity(const_size);
    for _ in 0..const_size {
        let tag = reader.read_byte()?;
        let k = match tag {
            LUA_TNIL => Constant::Nil,
            LUA_VFALSE => Constant::Boolean(false),
            LUA_VTRUE => Constant::Boolean(true),
            LUA_VNUMINT => {
                let i = reader.read_i64_le()?;
                Constant::Integer(i)
            }
            LUA_VNUMFLT => {
                let f = reader.read_f64_le()?;
                Constant::Float(f)
            }
            LUA_VSHRSTR | LUA_VLNGSTR => {
                let sid = reader.read_lua_string(strings)?.ok_or_else(|| UndumpError {
                    message: "expected string constant".to_string(),
                })?;
                Constant::String(sid)
            }
            _ => {
                return Err(UndumpError {
                    message: format!("unknown constant type: {}", tag),
                })
            }
        };
        proto.constants.push(k);
    }

    // Upvalues
    let upval_size = reader.read_int()? as usize;
    proto.upvalues = Vec::with_capacity(upval_size);
    for _ in 0..upval_size {
        let in_stack = reader.read_byte()? != 0;
        let index = reader.read_byte()?;
        let kind = reader.read_byte()?;
        proto.upvalues.push(UpvalDesc {
            name: None, // filled in debug section
            in_stack,
            index,
            kind,
        });
    }

    // Protos (child functions)
    let proto_size = reader.read_int()? as usize;
    proto.protos = Vec::with_capacity(proto_size);
    for _ in 0..proto_size {
        let child = read_function(reader, strings, effective_source)?;
        proto.protos.push(child);
    }

    // Debug info - line info
    let line_info_size = reader.read_int()? as usize;
    proto.line_info = Vec::with_capacity(line_info_size);
    for _ in 0..line_info_size {
        proto.line_info.push(reader.read_byte()? as i8);
    }

    // Debug info - abs line info
    let abs_line_size = reader.read_int()? as usize;
    proto.abs_line_info = Vec::with_capacity(abs_line_size);
    for _ in 0..abs_line_size {
        let pc = reader.read_int()? as u32;
        let line = reader.read_int()? as u32;
        proto.abs_line_info.push(AbsLineInfo { pc, line });
    }

    // Debug info - local vars
    let local_size = reader.read_int()? as usize;
    proto.local_vars = Vec::with_capacity(local_size);
    for _ in 0..local_size {
        let name = reader.read_lua_string(strings)?.unwrap_or(StringId(0));
        let start_pc = reader.read_int()? as u32;
        let end_pc = reader.read_int()? as u32;
        proto.local_vars.push(LocalVar {
            name,
            reg: proto.local_vars.len() as u8,
            start_pc,
            end_pc,
        });
    }

    // Debug info - upvalue names
    let upval_name_size = reader.read_int()? as usize;
    for i in 0..upval_name_size {
        let name = reader.read_lua_string(strings)?;
        if i < proto.upvalues.len() {
            proto.upvalues[i].name = name;
        }
    }

    Ok(proto)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundtrip_simple() {
        let mut strings = StringInterner::new();
        let source_sid = strings.intern(b"=test");
        let const_str = strings.intern(b"hello");

        let mut proto = Proto::new();
        proto.source = Some(source_sid);
        proto.num_params = 0;
        proto.is_vararg = true;
        proto.max_stack_size = 2;
        proto.code.push(Instruction(0x00000046)); // Return0
        proto.line_info.push(1);
        proto.constants.push(Constant::Integer(42));
        proto.constants.push(Constant::Float(3.14));
        proto.constants.push(Constant::String(const_str));
        proto.constants.push(Constant::Boolean(true));
        proto.constants.push(Constant::Nil);
        proto.upvalues.push(UpvalDesc {
            name: Some(strings.intern(b"_ENV")),
            in_stack: true,
            index: 0,
            kind: 0,
        });

        let dumped = dump(&proto, &strings, false);
        assert_eq!(&dumped[0..4], LUA_SIGNATURE);

        let restored = undump(&dumped, "test", &mut strings).unwrap();
        assert_eq!(restored.code.len(), 1);
        assert_eq!(restored.constants.len(), 5);
        assert_eq!(restored.upvalues.len(), 1);
        assert_eq!(restored.num_params, 0);
        assert!(restored.is_vararg);
        assert_eq!(restored.max_stack_size, 2);
    }
}
