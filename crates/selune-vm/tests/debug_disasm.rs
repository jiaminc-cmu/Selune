#[test]
fn dump_bytecodes() {
    let tests = vec![(
        "nested_calls",
        "local function f(a, b) return a end
         return f(1, f(2, f(3, 4)))",
    )];

    for (label, source) in tests {
        eprintln!("=== {} ===", label);
        let (proto, strings) =
            selune_compiler::compiler::compile(source.as_bytes(), "=test").unwrap();
        eprintln!("{}", selune_compiler::disasm::disassemble(&proto, &strings));
        for (i, child) in proto.protos.iter().enumerate() {
            eprintln!("--- child proto {} ---", i);
            eprintln!("{}", selune_compiler::disasm::disassemble(child, &strings));
        }
    }
}
