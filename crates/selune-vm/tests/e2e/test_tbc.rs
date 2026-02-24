use super::helpers::*;

// ── Basic __close on scope exit ─────────────────────────────────

#[test]
fn test_tbc_basic_close() {
    run_check_ints(
        r#"
        local closed = 0
        do
            local x <close> = setmetatable({}, {
                __close = function(self, err)
                    closed = closed + 1
                end
            })
        end
        return closed
        "#,
        &[1],
    );
}

#[test]
fn test_tbc_close_receives_nil_on_normal_exit() {
    run_check_ints(
        r#"
        local got_nil = 0
        do
            local x <close> = setmetatable({}, {
                __close = function(self, err)
                    if err == nil then got_nil = 1 end
                end
            })
        end
        return got_nil
        "#,
        &[1],
    );
}

// ── Multiple TBC vars close in reverse order ────────────────────

#[test]
fn test_tbc_reverse_order() {
    run_check_ints(
        r#"
        local order = 0
        do
            local a <close> = setmetatable({id=1}, {
                __close = function(self, err)
                    order = order * 10 + self.id
                end
            })
            local b <close> = setmetatable({id=2}, {
                __close = function(self, err)
                    order = order * 10 + self.id
                end
            })
            local c <close> = setmetatable({id=3}, {
                __close = function(self, err)
                    order = order * 10 + self.id
                end
            })
        end
        -- Should close in reverse: c(3), b(2), a(1) → 321
        return order
        "#,
        &[321],
    );
}

// ── TBC on function return ──────────────────────────────────────

#[test]
fn test_tbc_on_function_return() {
    run_check_ints(
        r#"
        local closed = 0
        local function f()
            local x <close> = setmetatable({}, {
                __close = function(self, err)
                    closed = closed + 1
                end
            })
            return 42
        end
        local result = f()
        return closed, result
        "#,
        &[1, 42],
    );
}

// ── TBC with nil value (no crash) ───────────────────────────────

#[test]
fn test_tbc_nil_value() {
    run_check_ints(
        r#"
        local ok = 1
        do
            local x <close> = nil
        end
        return ok
        "#,
        &[1],
    );
}

// ── TBC on error (still closes) ─────────────────────────────────

#[test]
fn test_tbc_closes_on_error() {
    run_check_ints(
        r#"
        local closed = 0
        pcall(function()
            local x <close> = setmetatable({}, {
                __close = function(self, err)
                    closed = closed + 1
                end
            })
            error("boom")
        end)
        return closed
        "#,
        &[1],
    );
}

#[test]
fn test_tbc_receives_error_on_error_exit() {
    run_check_ints(
        r#"
        local got_error = 0
        pcall(function()
            local x <close> = setmetatable({}, {
                __close = function(self, err)
                    if err ~= nil then got_error = 1 end
                end
            })
            error("boom")
        end)
        return got_error
        "#,
        &[1],
    );
}

// ── TBC in nested scopes ────────────────────────────────────────

#[test]
fn test_tbc_nested_scopes() {
    run_check_ints(
        r#"
        local count = 0
        do
            local a <close> = setmetatable({}, {
                __close = function() count = count + 1 end
            })
            do
                local b <close> = setmetatable({}, {
                    __close = function() count = count + 1 end
                })
            end
            -- b should already be closed here
        end
        return count
        "#,
        &[2],
    );
}

// ── TBC in for loop ─────────────────────────────────────────────

#[test]
fn test_tbc_in_for_loop() {
    run_check_ints(
        r#"
        local count = 0
        for i = 1, 3 do
            local x <close> = setmetatable({}, {
                __close = function() count = count + 1 end
            })
        end
        return count
        "#,
        &[3],
    );
}

// ── Error in __close during normal exit propagates ──────────────

#[test]
fn test_tbc_close_error_propagates() {
    run_check_ints(
        r#"
        local ok = pcall(function()
            do
                local x <close> = setmetatable({}, {
                    __close = function(self, err)
                        error("close failed")
                    end
                })
            end
        end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

// ── Error in __close during error exit is suppressed ────────────

#[test]
fn test_tbc_close_error_suppressed_on_error() {
    run_check_ints(
        r#"
        local ok, msg = pcall(function()
            local x <close> = setmetatable({}, {
                __close = function(self, err)
                    error("close error")
                end
            })
            error("original error")
        end)
        -- The original error should be preserved, close error suppressed
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

// ── TBC with table that has no __close is a runtime error ─────────

#[test]
fn test_tbc_no_close_metamethod() {
    let err = run_lua_err(
        r#"
        local ok = 1
        do
            local x <close> = setmetatable({}, {})
        end
        return ok
        "#,
    );
    assert!(
        err.contains("non-closable value"),
        "expected non-closable error, got: {err}"
    );
}

// ── Multiple TBC in different functions ─────────────────────────

#[test]
fn test_tbc_across_function_calls() {
    run_check_ints(
        r#"
        local order = 0
        local function inner()
            local x <close> = setmetatable({id=1}, {
                __close = function(self) order = order * 10 + self.id end
            })
            return 42
        end
        do
            local y <close> = setmetatable({id=2}, {
                __close = function(self) order = order * 10 + self.id end
            })
            inner()
        end
        -- inner's x closes (1), then y closes (2) → 12
        return order
        "#,
        &[12],
    );
}
