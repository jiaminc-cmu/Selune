// Tests for userdata type infrastructure.
// These are Rust-level tests since Lua scripts can't create userdata directly
// (userdata is created by native code like io.open).
// The Lua-visible behavior is tested through type() and the io library later.

#[allow(unused_imports)]
use super::helpers::*;

// Test that type() returns "userdata" for unknown GC sub-tags
// (this exercises the object.rs type name path)

#[test]
fn test_userdata_type_name() {
    use selune_core::gc::GcHeap;
    use selune_core::value::TValue;

    let mut gc = GcHeap::new();
    let ud_idx = gc.alloc_userdata(Box::new(42i32), None);
    let val = TValue::from_userdata(ud_idx);

    assert!(val.is_userdata());
    assert!(val.as_userdata_idx().is_some());
    assert_eq!(val.as_userdata_idx().unwrap().0, ud_idx.0);
    assert_eq!(selune_core::object::lua_type_name(val, &gc), "userdata");
}

#[test]
fn test_userdata_with_metatable() {
    use selune_core::gc::GcHeap;

    let mut gc = GcHeap::new();
    let mt_idx = gc.alloc_table(0, 4);
    let ud_idx = gc.alloc_userdata(Box::new("hello".to_string()), Some(mt_idx));

    let ud = gc.get_userdata(ud_idx);
    assert!(ud.metatable.is_some());
    assert_eq!(ud.metatable.unwrap().0, mt_idx.0);
}

#[test]
fn test_userdata_data_access() {
    use selune_core::gc::GcHeap;

    let mut gc = GcHeap::new();
    let ud_idx = gc.alloc_userdata(Box::new(vec![1, 2, 3]), None);

    let ud = gc.get_userdata(ud_idx);
    let data = ud.data.downcast_ref::<Vec<i32>>().unwrap();
    assert_eq!(data, &vec![1, 2, 3]);
}

#[test]
fn test_userdata_gc_collection() {
    use selune_core::gc::GcHeap;

    let mut gc = GcHeap::new();
    let _ud_idx = gc.alloc_userdata(Box::new(100u64), None);

    // Prepare marks, don't mark the userdata, sweep
    gc.gc_prepare_marks();
    // Don't mark - it should be swept
    gc.gc_sweep();

    // The userdata slot should be freed (we can verify by allocating again and
    // getting the same index back)
    let ud_idx2 = gc.alloc_userdata(Box::new(200u64), None);
    assert_eq!(ud_idx2.0, 0); // reused slot 0
}

#[test]
fn test_userdata_gc_mark_preserves() {
    use selune_core::gc::GcHeap;
    use selune_core::value::TValue;

    let mut gc = GcHeap::new();
    let ud_idx = gc.alloc_userdata(Box::new(42i64), None);
    let val = TValue::from_userdata(ud_idx);

    // Prepare marks, mark the userdata, sweep
    gc.gc_prepare_marks();
    gc.gc_mark_value(val);
    loop {
        if gc.gc_propagate() == 0 {
            break;
        }
    }
    gc.gc_sweep();

    // Userdata should still be accessible
    let ud = gc.get_userdata(ud_idx);
    let data = ud.data.downcast_ref::<i64>().unwrap();
    assert_eq!(*data, 42);
}

#[test]
fn test_userdata_gc_marks_metatable() {
    use selune_core::gc::GcHeap;
    use selune_core::string::StringInterner;
    use selune_core::value::TValue;

    let mut gc = GcHeap::new();
    let mut strings = StringInterner::new();

    // Create a metatable with a field
    let mt_idx = gc.alloc_table(0, 4);
    let key = strings.intern(b"__name");
    let name_sid = strings.intern(b"MyType");
    gc.get_table_mut(mt_idx)
        .raw_set_str(key, TValue::from_string_id(name_sid));

    // Create userdata with this metatable
    let ud_idx = gc.alloc_userdata(Box::new(0u8), Some(mt_idx));
    let val = TValue::from_userdata(ud_idx);

    // GC cycle: mark userdata (which should transitively mark metatable)
    gc.gc_prepare_marks();
    gc.gc_mark_value(val);
    loop {
        if gc.gc_propagate() == 0 {
            break;
        }
    }
    gc.gc_sweep();

    // Both userdata and metatable should survive
    let ud = gc.get_userdata(ud_idx);
    assert!(ud.metatable.is_some());
    let mt = gc.get_table(mt_idx);
    let name_val = mt.raw_get_str(key);
    assert!(!name_val.is_nil());
}

#[test]
fn test_userdata_tvalue_debug() {
    use selune_core::gc::GcHeap;
    use selune_core::value::TValue;

    let mut gc = GcHeap::new();
    let ud_idx = gc.alloc_userdata(Box::new(()), None);
    let val = TValue::from_userdata(ud_idx);

    let debug_str = format!("{:?}", val);
    assert!(debug_str.contains("userdata"), "debug was: {debug_str}");
}

#[test]
fn test_userdata_equality() {
    use selune_core::gc::GcHeap;
    use selune_core::value::TValue;

    let mut gc = GcHeap::new();
    let ud1 = gc.alloc_userdata(Box::new(1u32), None);
    let ud2 = gc.alloc_userdata(Box::new(1u32), None);

    let val1 = TValue::from_userdata(ud1);
    let val2 = TValue::from_userdata(ud2);
    let val1_copy = TValue::from_userdata(ud1);

    // Same userdata = equal, different userdata = not equal (identity semantics)
    assert_eq!(val1, val1_copy);
    assert_ne!(val1, val2);
}
