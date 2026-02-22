#[test]
fn dump_bytecodes() {
    let tests = vec![
        (
            "nested_calls",
            "local function f(a, b) return a end
             return f(1, f(2, f(3, 4)))",
        ),
        (
            "handler_with_global",
            "local function handler(tbl, key)
                rawset(tbl, key, 42)
                return 42
            end
            return handler",
        ),
        (
            "multiple_metamethods",
            "local log = {}
            local mt = {
                __index = function(t, k) return 0 end,
                __len = function(t) return 99 end,
            }
            local t = setmetatable({}, mt)
            return t.x, #t",
        ),
        (
            "generic_for_pairs",
            "local t = {10, 20, 30}
            local sum = 0
            for k, v in pairs(t) do
                sum = sum + v
            end
            return sum",
        ),
        (
            "tbc_basic",
            "local closed = 0
            do
                local x <close> = setmetatable({}, {
                    __close = function(self, err) closed = closed + 1 end
                })
            end
            return closed",
        ),
    ];

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
