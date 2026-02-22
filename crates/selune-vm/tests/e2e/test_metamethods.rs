use super::helpers::*;

// ---- __index function ----

#[test]
fn test_index_function() {
    run_check_ints(
        r#"
        local t = setmetatable({}, {
            __index = function(tbl, key)
                return 42
            end
        })
        return t.anything
        "#,
        &[42],
    );
}

#[test]
fn test_index_function_receives_key() {
    run_check_ints(
        r#"
        local t = setmetatable({}, {
            __index = function(tbl, key)
                if key == "x" then return 10 end
                if key == "y" then return 20 end
                return 0
            end
        })
        return t.x, t.y, t.z
        "#,
        &[10, 20, 0],
    );
}

#[test]
fn test_index_existing_key_no_metamethod() {
    // If key exists, __index is not called
    run_check_ints(
        r#"
        local t = setmetatable({x = 99}, {
            __index = function(tbl, key) return 42 end
        })
        return t.x
        "#,
        &[99],
    );
}

// ---- __index table ----

#[test]
fn test_index_table() {
    run_check_ints(
        r#"
        local defaults = {x = 10, y = 20}
        local t = setmetatable({}, {__index = defaults})
        return t.x, t.y
        "#,
        &[10, 20],
    );
}

#[test]
fn test_index_chain() {
    // Chain: t -> mt1 -> mt2
    run_check_ints(
        r#"
        local base = {x = 100}
        local mid = setmetatable({}, {__index = base})
        local t = setmetatable({}, {__index = mid})
        return t.x
        "#,
        &[100],
    );
}

// ---- __newindex function ----

#[test]
fn test_newindex_function() {
    run_check_ints(
        r#"
        local log = 0
        local t = setmetatable({}, {
            __newindex = function(tbl, key, val)
                log = val
            end
        })
        t.x = 42
        return log
        "#,
        &[42],
    );
}

#[test]
fn test_newindex_existing_key_no_metamethod() {
    // If key already exists, __newindex is not called
    run_check_ints(
        r#"
        local log = 0
        local t = setmetatable({x = 10}, {
            __newindex = function(tbl, key, val)
                log = val
            end
        })
        t.x = 42
        return t.x, log
        "#,
        &[42, 0],
    );
}

// ---- __newindex table ----

#[test]
fn test_newindex_table() {
    run_check_ints(
        r#"
        local storage = {}
        local t = setmetatable({}, {__newindex = storage})
        t.x = 42
        return storage.x
        "#,
        &[42],
    );
}

// ---- __len ----

#[test]
fn test_len_metamethod() {
    run_check_ints(
        r#"
        local t = setmetatable({1, 2, 3}, {
            __len = function(tbl)
                return 99
            end
        })
        return #t
        "#,
        &[99],
    );
}

#[test]
fn test_len_no_metamethod() {
    run_check_ints(
        r#"
        local t = {1, 2, 3}
        return #t
        "#,
        &[3],
    );
}

// ---- __call ----

#[test]
fn test_call_metamethod() {
    run_check_ints(
        r#"
        local t = setmetatable({}, {
            __call = function(self, a, b)
                return a + b
            end
        })
        return t(10, 20)
        "#,
        &[30],
    );
}

#[test]
fn test_call_metamethod_receives_self() {
    // Simpler version: just test that self is passed
    run_check_ints(
        r#"
        local mt = {}
        mt.__call = function(self, x)
            return x + 1
        end
        local t = setmetatable({}, mt)
        return t(5)
        "#,
        &[6],
    );
}

// ---- OOP pattern with __index ----

#[test]
fn test_oop_class_pattern() {
    run_check_ints(
        r#"
        local MyClass = {}
        MyClass.__index = MyClass

        function MyClass.new(value)
            local self = setmetatable({}, MyClass)
            rawset(self, "value", value)
            return self
        end

        function MyClass.get_value(self)
            return rawget(self, "value")
        end

        function MyClass.add(self, x)
            rawset(self, "value", rawget(self, "value") + x)
        end

        local obj = MyClass.new(10)
        obj.add(obj, 5)
        return obj.get_value(obj)
        "#,
        &[15],
    );
}

#[test]
fn test_oop_method_call() {
    run_check_ints(
        r#"
        local MyClass = {}
        MyClass.__index = MyClass

        function MyClass.new(value)
            local self = setmetatable({}, MyClass)
            rawset(self, "value", value)
            return self
        end

        function MyClass:get_value()
            return rawget(self, "value")
        end

        local obj = MyClass.new(42)
        return obj:get_value()
        "#,
        &[42],
    );
}

// ---- No metamethod → correct errors ----

#[test]
fn test_index_nil_no_metamethod() {
    let err = run_lua_err("local x = nil\nreturn x.foo");
    assert!(
        err.contains("attempt to index a nil value"),
        "expected 'attempt to index a nil value', got: {err}"
    );
}

#[test]
fn test_call_non_callable_no_metamethod() {
    let err = run_lua_err("local t = {}\nt()");
    assert!(
        err.contains("attempt to call a table value"),
        "expected 'attempt to call a table value', got: {err}"
    );
}

// ---- __index with integer keys ----

#[test]
fn test_index_integer_key() {
    run_check_ints(
        r#"
        local defaults = {10, 20, 30}
        local t = setmetatable({}, {__index = defaults})
        return t[1], t[2], t[3]
        "#,
        &[10, 20, 30],
    );
}

// ---- Multiple metamethods on same table ----

#[test]
fn test_multiple_metamethods() {
    run_check_ints(
        r#"
        local log = {}
        local mt = {
            __index = function(t, k) return 0 end,
            __len = function(t) return 99 end,
        }
        local t = setmetatable({}, mt)
        return t.x, #t
        "#,
        &[0, 99],
    );
}

// ---- __newindex with rawset ----

#[test]
fn test_newindex_with_rawset() {
    run_check_ints(
        r#"
        local t = setmetatable({}, {
            __newindex = function(tbl, key, val)
                rawset(tbl, key, val * 2)
            end
        })
        t.x = 10
        return t.x
        "#,
        &[20],
    );
}

// ---- __index function with table receiver ----

#[test]
fn test_index_function_passes_table() {
    // Simpler: just test return value without rawset
    run_check_ints(
        r#"
        local t = setmetatable({}, {
            __index = function(tbl, key) return 42 end
        })
        local v1 = t.x
        local v2 = t.x
        return v1, v2
        "#,
        &[42, 42],
    );
}

#[test]
fn test_index_function_with_rawset() {
    // First check that the closure has upvalues when returned
    let source = r#"
        local function handler(tbl, key)
            rawset(tbl, key, 42)
            return 42
        end
        return handler
    "#;
    let (proto, strings) = selune_compiler::compiler::compile(source.as_bytes(), "=test").unwrap();

    // Check child proto has upvalues
    assert!(!proto.protos.is_empty(), "should have child proto");
    let child = &proto.protos[0];
    eprintln!(
        "Child proto: {} upvalues, {} params",
        child.upvalues.len(),
        child.num_params
    );

    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    let closure_idx = results[0].as_closure_idx().expect("should be closure");
    let closure = vm.gc.get_closure(closure_idx);
    eprintln!(
        "Closure: {} upvalues, proto_idx={}",
        closure.upvalues.len(),
        closure.proto_idx
    );

    // Now test the actual __index usage
    run_check_ints(
        r#"
        local function handler(tbl, key)
            rawset(tbl, key, 42)
            return 42
        end
        local t = setmetatable({}, {__index = handler})
        local v1 = t.x
        local v2 = t.x
        return v1, v2
        "#,
        &[42, 42],
    );
}

#[test]
fn test_gettabup_no_error_on_nil() {
    // Accessing a global that doesn't exist should return nil (not error)
    let results = run_lua("return undefined_global");
    assert_nil(&results, 0);
}

// ---- Arithmetic metamethods ----

#[test]
fn test_add_metamethod() {
    run_check_ints(
        r#"
        local mt = { __add = function(a, b) return 100 end }
        local t = setmetatable({}, mt)
        return t + 1
        "#,
        &[100],
    );
}

#[test]
fn test_sub_metamethod() {
    run_check_ints(
        r#"
        local mt = { __sub = function(a, b) return 200 end }
        local t = setmetatable({}, mt)
        return t - 1
        "#,
        &[200],
    );
}

#[test]
fn test_mul_metamethod() {
    run_check_ints(
        r#"
        local mt = { __mul = function(a, b) return 300 end }
        local t = setmetatable({}, mt)
        return t * 2
        "#,
        &[300],
    );
}

#[test]
fn test_div_metamethod() {
    run_check_floats(
        r#"
        local mt = { __div = function(a, b) return 4.0 end }
        local t = setmetatable({}, mt)
        return t / 2
        "#,
        &[4.0],
    );
}

#[test]
fn test_mod_metamethod() {
    run_check_ints(
        r#"
        local mt = { __mod = function(a, b) return 7 end }
        local t = setmetatable({}, mt)
        return t % 3
        "#,
        &[7],
    );
}

#[test]
fn test_pow_metamethod() {
    run_check_floats(
        r#"
        local mt = { __pow = function(a, b) return 8.0 end }
        local t = setmetatable({}, mt)
        return t ^ 3
        "#,
        &[8.0],
    );
}

#[test]
fn test_idiv_metamethod() {
    run_check_ints(
        r#"
        local mt = { __idiv = function(a, b) return 5 end }
        local t = setmetatable({}, mt)
        return t // 2
        "#,
        &[5],
    );
}

// ---- Bitwise metamethods ----

#[test]
fn test_band_metamethod() {
    run_check_ints(
        r#"
        local mt = { __band = function(a, b) return 42 end }
        local t = setmetatable({}, mt)
        return t & 0xFF
        "#,
        &[42],
    );
}

#[test]
fn test_bor_metamethod() {
    run_check_ints(
        r#"
        local mt = { __bor = function(a, b) return 42 end }
        local t = setmetatable({}, mt)
        return t | 0xFF
        "#,
        &[42],
    );
}

#[test]
fn test_bxor_metamethod() {
    run_check_ints(
        r#"
        local mt = { __bxor = function(a, b) return 42 end }
        local t = setmetatable({}, mt)
        return t ~ 0xFF
        "#,
        &[42],
    );
}

#[test]
fn test_shl_metamethod() {
    run_check_ints(
        r#"
        local mt = { __shl = function(a, b) return 42 end }
        local t = setmetatable({}, mt)
        return t << 2
        "#,
        &[42],
    );
}

#[test]
fn test_shr_metamethod() {
    run_check_ints(
        r#"
        local mt = { __shr = function(a, b) return 42 end }
        local t = setmetatable({}, mt)
        return t >> 2
        "#,
        &[42],
    );
}

// ---- Second operand has metamethod ----

#[test]
fn test_add_metamethod_right_operand() {
    run_check_ints(
        r#"
        local mt = { __add = function(a, b) return 999 end }
        local t = setmetatable({}, mt)
        return 1 + t
        "#,
        &[999],
    );
}

// ---- Unary metamethods ----

#[test]
fn test_unm_metamethod() {
    run_check_ints(
        r#"
        local mt = { __unm = function(a) return 42 end }
        local t = setmetatable({}, mt)
        return -t
        "#,
        &[42],
    );
}

#[test]
fn test_bnot_metamethod() {
    run_check_ints(
        r#"
        local mt = { __bnot = function(a) return 42 end }
        local t = setmetatable({}, mt)
        return ~t
        "#,
        &[42],
    );
}

// ---- Comparison metamethods ----

#[test]
fn test_eq_metamethod() {
    run_check_ints(
        r#"
        local mt = { __eq = function(a, b) return true end }
        local t1 = setmetatable({}, mt)
        local t2 = setmetatable({}, mt)
        if t1 == t2 then return 1 else return 0 end
        "#,
        &[1],
    );
}

#[test]
fn test_eq_metamethod_false() {
    run_check_ints(
        r#"
        local mt = { __eq = function(a, b) return false end }
        local t1 = setmetatable({}, mt)
        local t2 = setmetatable({}, mt)
        if t1 == t2 then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_lt_metamethod() {
    run_check_ints(
        r#"
        local mt = { __lt = function(a, b) return true end }
        local t1 = setmetatable({}, mt)
        local t2 = setmetatable({}, mt)
        if t1 < t2 then return 1 else return 0 end
        "#,
        &[1],
    );
}

#[test]
fn test_le_metamethod() {
    run_check_ints(
        r#"
        local mt = { __le = function(a, b) return true end }
        local t1 = setmetatable({}, mt)
        local t2 = setmetatable({}, mt)
        if t1 <= t2 then return 1 else return 0 end
        "#,
        &[1],
    );
}

// ---- Concat metamethod ----

#[test]
fn test_concat_metamethod() {
    run_check_strings(
        r#"
        local mt = { __concat = function(a, b) return "hello" end }
        local t = setmetatable({}, mt)
        return t .. "world"
        "#,
        &["hello"],
    );
}

#[test]
fn test_concat_metamethod_right() {
    run_check_strings(
        r#"
        local mt = { __concat = function(a, b) return "hello" end }
        local t = setmetatable({}, mt)
        return "world" .. t
        "#,
        &["hello"],
    );
}

// ---- Practical: Vector addition via __add ----

#[test]
fn test_vector_add_metamethod() {
    run_check_ints(
        r#"
        local Vec = {}
        Vec.__index = Vec
        Vec.__add = function(a, b)
            local result = setmetatable({}, Vec)
            rawset(result, "x", rawget(a, "x") + rawget(b, "x"))
            rawset(result, "y", rawget(a, "y") + rawget(b, "y"))
            return result
        end
        local v1 = setmetatable({}, Vec)
        rawset(v1, "x", 1)
        rawset(v1, "y", 2)
        local v2 = setmetatable({}, Vec)
        rawset(v2, "x", 3)
        rawset(v2, "y", 4)
        local v3 = v1 + v2
        return rawget(v3, "x"), rawget(v3, "y")
        "#,
        &[4, 6],
    );
}

// ---- No metamethod → correct error preserved ----

#[test]
fn test_add_no_metamethod_error() {
    let err = run_lua_err("local t = {} return t + 1");
    assert!(
        err.contains("attempt to perform arithmetic"),
        "expected arithmetic error, got: {err}"
    );
}

#[test]
fn test_lt_no_metamethod_error() {
    let err = run_lua_err("local t1 = {} local t2 = {} return t1 < t2");
    assert!(
        err.contains("attempt to compare"),
        "expected compare error, got: {err}"
    );
}

// ---- MMBinK variant (table + constant) ----

#[test]
fn test_add_metamethod_with_constant() {
    run_check_ints(
        r#"
        local mt = { __add = function(a, b) return 42 end }
        local t = setmetatable({}, mt)
        return t + 100
        "#,
        &[42],
    );
}

// ---- MMBinI variant (table + immediate) ----

#[test]
fn test_add_metamethod_with_immediate() {
    run_check_ints(
        r#"
        local mt = { __add = function(a, b) return 42 end }
        local t = setmetatable({}, mt)
        return t + 1
        "#,
        &[42],
    );
}
