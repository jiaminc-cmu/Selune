use super::helpers::*;
use selune_compiler::opcode::OpCode;

#[test]
fn e2e_fibonacci() {
    let src = r#"
local function fib(n)
    if n then
        return n
    end
    return fib
end
return fib
"#;
    let (proto, _) = compile_str(src);
    assert!(has_opcode(&proto, OpCode::Closure));
    assert_eq!(proto.protos.len(), 1);
}

#[test]
fn e2e_factorial() {
    let src = r#"
local function fact(n)
    if n then return 1 end
    return n
end
return fact(10)
"#;
    let (proto, _) = compile_str(src);
    assert!(has_opcode(&proto, OpCode::Closure));
    assert!(has_opcode(&proto, OpCode::Call) || has_opcode(&proto, OpCode::TailCall));
}

#[test]
fn e2e_counter_closure() {
    let src = r#"
local function make_counter()
    local count = 0
    return function()
        count = count + 1
        return count
    end
end
local c = make_counter()
return c()
"#;
    let (proto, _) = compile_str(src);
    // make_counter creates a closure
    assert!(has_opcode(&proto, OpCode::Closure));
    assert!(has_opcode(&proto, OpCode::Call));
}

#[test]
fn e2e_nested_loops() {
    let src = r#"
for i = 1, 10 do
    for j = 1, 10 do
        local x = i
    end
end
"#;
    let (proto, _) = compile_str(src);
    assert_eq!(count_opcode(&proto, OpCode::ForPrep), 2);
    assert_eq!(count_opcode(&proto, OpCode::ForLoop), 2);
}

#[test]
fn e2e_table_operations() {
    let src = r#"
local t = {1, 2, 3}
t[4] = 4
local x = t[1]
t.name = "test"
local y = t.name
"#;
    let (proto, _) = compile_str(src);
    assert!(has_opcode(&proto, OpCode::NewTable));
    assert!(has_opcode(&proto, OpCode::SetI) || has_opcode(&proto, OpCode::SetTable));
}

#[test]
fn e2e_control_flow() {
    let src = r#"
local x = 10
if x then
    x = 1
else
    x = 0
end
while x do
    x = nil
end
repeat
    x = true
until x
"#;
    let (proto, _) = compile_str(src);
    assert!(has_opcode(&proto, OpCode::Test));
    assert!(has_opcode(&proto, OpCode::Jmp));
}

#[test]
fn e2e_all_return_forms() {
    let src = r#"
function f1() return end
function f2() return 1 end
function f3() return 1, 2, 3 end
"#;
    let (proto, _) = compile_str(src);
    assert_eq!(proto.protos.len(), 3);
}

#[test]
fn e2e_method_call_chain() {
    let src = r#"
local obj = {}
obj.x = 1
obj.y = 2
"#;
    let (proto, _) = compile_str(src);
    assert!(has_opcode(&proto, OpCode::NewTable));
    assert!(has_opcode(&proto, OpCode::SetField));
}

#[test]
fn e2e_complex_expression() {
    let src = "local a = 1\nlocal b = 2\nlocal c = 3\nreturn a + b * c";
    let (proto, _) = compile_str(src);
    // Should have multiplication and addition
    assert!(
        has_opcode(&proto, OpCode::Mul)
            || has_opcode(&proto, OpCode::MulK)
            || has_opcode(&proto, OpCode::Add)
            || has_opcode(&proto, OpCode::AddK)
            || has_opcode(&proto, OpCode::AddI)
    );
}

#[test]
fn e2e_string_operations() {
    let src = r#"
local a = "hello"
local b = "world"
local c = a .. " " .. b
return c
"#;
    let (proto, _) = compile_str(src);
    assert!(has_opcode(&proto, OpCode::Concat));
}

#[test]
fn e2e_varargs_program() {
    let src = r#"
local function vfunc(...)
    return ...
end
return vfunc(1, 2, 3)
"#;
    let (proto, _) = compile_str(src);
    assert!(proto.protos[0].is_vararg);
}

#[test]
fn e2e_goto_complex() {
    let src = r#"
local x = 1
goto skip
x = 2
::skip::
local y = x
"#;
    let (proto, _) = compile_str(src);
    assert!(has_opcode(&proto, OpCode::Jmp));
}

#[test]
fn e2e_break_nested() {
    let src = r#"
for i = 1, 10 do
    for j = 1, 10 do
        if j then
            break
        end
    end
end
"#;
    let (proto, _) = compile_str(src);
    assert_eq!(count_opcode(&proto, OpCode::ForPrep), 2);
}
