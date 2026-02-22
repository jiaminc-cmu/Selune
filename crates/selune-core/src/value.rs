/// NaN-boxed Lua value representation.
///
/// Layout (64 bits):
/// - Pure f64: any non-NaN double (quiet NaN canonicalized to QNAN)
/// - Tagged values: QNAN prefix (0x7FF8) | tag (3 bits, 47-49) | payload (47 bits)
///
/// Tags (bits 49-47):
///   000 = canonical NaN (no payload)
///   001 = nil
///   010 = bool
///   011 = small integer (47-bit signed)
///   100 = GC pointer
///   101 = light userdata
use crate::gc::*;
use crate::string::StringId;
use std::fmt;
use std::marker::PhantomData;

/// Quiet NaN prefix: exponent all 1s + quiet bit set
const QNAN: u64 = 0x7FF8_0000_0000_0000;

/// Tag mask: 3 bits at positions 47-49
const TAG_MASK: u64 = 0x0007_0000_0000_0000;
/// Payload mask: lower 47 bits
const PAYLOAD_MASK: u64 = 0x0000_FFFF_FFFF_FFFF;

const TAG_NIL: u64 = 0x0001_0000_0000_0000;
const TAG_BOOL: u64 = 0x0002_0000_0000_0000;
const TAG_INT: u64 = 0x0003_0000_0000_0000;
const TAG_GC: u64 = 0x0004_0000_0000_0000;
const TAG_LIGHT: u64 = 0x0005_0000_0000_0000;

/// 47-bit signed integer max: 2^46 - 1
const SMALL_INT_MAX: i64 = (1i64 << 46) - 1;
/// 47-bit signed integer min: -2^46
const SMALL_INT_MIN: i64 = -(1i64 << 46);

/// A NaN-boxed Lua value packed into 8 bytes.
#[derive(Clone, Copy)]
pub struct TValue(u64);

impl TValue {
    // ---- Constructors ----

    /// Create a nil value.
    #[inline]
    pub fn nil() -> Self {
        TValue(QNAN | TAG_NIL)
    }

    /// Create a boolean value.
    #[inline]
    pub fn from_bool(b: bool) -> Self {
        TValue(QNAN | TAG_BOOL | (b as u64))
    }

    /// Create a float value. NaN inputs are canonicalized.
    #[inline]
    pub fn from_float(f: f64) -> Self {
        let bits = f.to_bits();
        // Check if it's any kind of NaN
        if f.is_nan() {
            // Canonical NaN: QNAN with tag 000
            TValue(QNAN)
        } else {
            TValue(bits)
        }
    }

    /// Create an integer value from a 47-bit signed integer.
    ///
    /// # Panics
    /// Panics if the value is outside the 47-bit range [-2^46, 2^46-1].
    /// GC-boxed big integers will be added in Phase 2.
    #[inline]
    pub fn from_integer(i: i64) -> Self {
        assert!(
            (SMALL_INT_MIN..=SMALL_INT_MAX).contains(&i),
            "integer {i} outside 47-bit range [{SMALL_INT_MIN}, {SMALL_INT_MAX}]"
        );
        // Store as 47-bit two's complement
        let payload = (i as u64) & PAYLOAD_MASK;
        TValue(QNAN | TAG_INT | payload)
    }

    /// Create a GC pointer value.
    ///
    /// # Panics
    /// Panics if the pointer uses more than 47 bits.
    #[inline]
    pub fn from_gc_ptr(ptr: usize) -> Self {
        let ptr64 = ptr as u64;
        assert!(
            ptr64 & !PAYLOAD_MASK == 0,
            "GC pointer exceeds 47-bit address space"
        );
        TValue(QNAN | TAG_GC | ptr64)
    }

    /// Create a light userdata value.
    ///
    /// # Panics
    /// Panics if the pointer uses more than 47 bits.
    #[inline]
    pub fn from_light_userdata(ptr: usize) -> Self {
        let ptr64 = ptr as u64;
        assert!(
            ptr64 & !PAYLOAD_MASK == 0,
            "light userdata pointer exceeds 47-bit address space"
        );
        TValue(QNAN | TAG_LIGHT | ptr64)
    }

    // ---- Type checks ----

    /// Returns true if this is a NaN-boxed tagged value (not a plain float).
    #[inline]
    fn is_tagged(&self) -> bool {
        // A tagged value has the QNAN prefix set
        (self.0 & QNAN) == QNAN
    }

    #[inline]
    fn tag(&self) -> u64 {
        self.0 & TAG_MASK
    }

    #[inline]
    pub fn is_nil(&self) -> bool {
        self.is_tagged() && self.tag() == TAG_NIL
    }

    #[inline]
    pub fn is_bool(&self) -> bool {
        self.is_tagged() && self.tag() == TAG_BOOL
    }

    #[inline]
    pub fn is_float(&self) -> bool {
        !self.is_tagged() || (self.is_tagged() && self.tag() == 0)
    }

    #[inline]
    pub fn is_integer(&self) -> bool {
        self.is_tagged() && self.tag() == TAG_INT
    }

    #[inline]
    pub fn is_gc(&self) -> bool {
        self.is_tagged() && self.tag() == TAG_GC
    }

    #[inline]
    pub fn is_light_userdata(&self) -> bool {
        self.is_tagged() && self.tag() == TAG_LIGHT
    }

    /// Returns true if this value is a number (integer or float).
    #[inline]
    pub fn is_number(&self) -> bool {
        self.is_float() || self.is_integer()
    }

    // ---- Extractors ----

    /// Extract float value. Returns None for non-float values.
    #[inline]
    pub fn as_float(&self) -> Option<f64> {
        if self.is_tagged() && self.tag() == 0 {
            // Canonical NaN
            Some(f64::from_bits(QNAN))
        } else if !self.is_tagged() {
            Some(f64::from_bits(self.0))
        } else {
            None
        }
    }

    /// Extract boolean value. Returns None for non-bool values.
    #[inline]
    pub fn as_bool(&self) -> Option<bool> {
        if self.is_bool() {
            Some((self.0 & 1) != 0)
        } else {
            None
        }
    }

    /// Extract integer value. Returns None for non-integer values.
    #[inline]
    pub fn as_integer(&self) -> Option<i64> {
        if self.is_integer() {
            let raw = self.0 & PAYLOAD_MASK;
            // Sign-extend from 47 bits
            let extended = ((raw << 17) as i64) >> 17;
            Some(extended)
        } else {
            None
        }
    }

    /// Extract GC pointer. Returns None for non-GC values.
    #[inline]
    pub fn as_gc_ptr(&self) -> Option<usize> {
        if self.is_gc() {
            Some((self.0 & PAYLOAD_MASK) as usize)
        } else {
            None
        }
    }

    /// Extract light userdata pointer. Returns None for non-light-userdata values.
    #[inline]
    pub fn as_light_userdata(&self) -> Option<usize> {
        if self.is_light_userdata() {
            Some((self.0 & PAYLOAD_MASK) as usize)
        } else {
            None
        }
    }

    // ---- GC sub-tag helpers ----

    /// Create a GC value with a sub-tag and index.
    #[inline]
    pub fn from_gc_sub(sub_tag: u64, index: u32) -> Self {
        let payload = (sub_tag << GC_SUB_SHIFT) | (index as u64);
        debug_assert!(payload & !PAYLOAD_MASK == 0);
        TValue(QNAN | TAG_GC | payload)
    }

    /// Extract the GC sub-tag (bits 44-46 of payload).
    #[inline]
    pub fn gc_sub_tag(&self) -> Option<u64> {
        if self.is_gc() {
            let payload = self.0 & PAYLOAD_MASK;
            Some((payload >> GC_SUB_SHIFT) & GC_SUB_MASK)
        } else {
            None
        }
    }

    /// Extract the GC index (bits 0-43 of payload).
    #[inline]
    pub fn gc_index(&self) -> Option<u32> {
        if self.is_gc() {
            let payload = self.0 & PAYLOAD_MASK;
            Some((payload & GC_INDEX_MASK) as u32)
        } else {
            None
        }
    }

    /// Create a TValue from a StringId (stores as GC with string sub-tag).
    #[inline]
    pub fn from_string_id(id: StringId) -> Self {
        Self::from_gc_sub(GC_SUB_STRING, id.0)
    }

    /// Extract StringId if this is a string.
    #[inline]
    pub fn as_string_id(&self) -> Option<StringId> {
        if self.gc_sub_tag() == Some(GC_SUB_STRING) {
            Some(StringId(self.gc_index().unwrap()))
        } else {
            None
        }
    }

    /// Returns true if this is a string value.
    #[inline]
    pub fn is_string(&self) -> bool {
        self.gc_sub_tag() == Some(GC_SUB_STRING)
    }

    /// Create a TValue from a table GC index.
    #[inline]
    pub fn from_table(idx: GcIdx<crate::table::Table>) -> Self {
        Self::from_gc_sub(GC_SUB_TABLE, idx.0)
    }

    /// Extract table index if this is a table.
    #[inline]
    pub fn as_table_idx(&self) -> Option<GcIdx<crate::table::Table>> {
        if self.gc_sub_tag() == Some(GC_SUB_TABLE) {
            Some(GcIdx(self.gc_index().unwrap(), PhantomData))
        } else {
            None
        }
    }

    /// Returns true if this is a table value.
    #[inline]
    pub fn is_table(&self) -> bool {
        self.gc_sub_tag() == Some(GC_SUB_TABLE)
    }

    /// Create a TValue from a closure GC index.
    #[inline]
    pub fn from_closure(idx: GcIdx<crate::gc::LuaClosure>) -> Self {
        Self::from_gc_sub(GC_SUB_CLOSURE, idx.0)
    }

    /// Extract closure index if this is a closure.
    #[inline]
    pub fn as_closure_idx(&self) -> Option<GcIdx<crate::gc::LuaClosure>> {
        if self.gc_sub_tag() == Some(GC_SUB_CLOSURE) {
            Some(GcIdx(self.gc_index().unwrap(), PhantomData))
        } else {
            None
        }
    }

    /// Create a TValue from a native function GC index.
    #[inline]
    pub fn from_native(idx: GcIdx<crate::gc::NativeFunction>) -> Self {
        Self::from_gc_sub(GC_SUB_NATIVE, idx.0)
    }

    /// Extract native function index if this is a native function.
    #[inline]
    pub fn as_native_idx(&self) -> Option<GcIdx<crate::gc::NativeFunction>> {
        if self.gc_sub_tag() == Some(GC_SUB_NATIVE) {
            Some(GcIdx(self.gc_index().unwrap(), PhantomData))
        } else {
            None
        }
    }

    /// Returns true if this is any kind of function (closure or native).
    #[inline]
    pub fn is_function(&self) -> bool {
        matches!(
            self.gc_sub_tag(),
            Some(GC_SUB_CLOSURE) | Some(GC_SUB_NATIVE)
        )
    }

    /// Create a TValue from a full i64, boxing if necessary.
    #[inline]
    pub fn from_full_integer(i: i64, gc: &mut GcHeap) -> Self {
        if (SMALL_INT_MIN..=SMALL_INT_MAX).contains(&i) {
            Self::from_integer(i)
        } else {
            let idx = gc.alloc_boxed_int(i);
            Self::from_gc_sub(GC_SUB_BOXED_INT, idx.0)
        }
    }

    /// Extract a full i64, checking both inline and boxed.
    #[inline]
    pub fn as_full_integer(&self, gc: &GcHeap) -> Option<i64> {
        if let Some(i) = self.as_integer() {
            Some(i)
        } else if self.gc_sub_tag() == Some(GC_SUB_BOXED_INT) {
            let idx = GcIdx::<i64>(self.gc_index().unwrap(), PhantomData);
            Some(gc.get_boxed_int(idx))
        } else {
            None
        }
    }

    /// Returns true if this is any kind of integer (inline or boxed).
    #[inline]
    pub fn is_any_integer(&self, gc: &GcHeap) -> bool {
        self.is_integer()
            || (self.gc_sub_tag() == Some(GC_SUB_BOXED_INT)
                && gc.get_boxed_int(GcIdx::<i64>(self.gc_index().unwrap(), PhantomData))
                    == gc.get_boxed_int(GcIdx::<i64>(self.gc_index().unwrap(), PhantomData)))
    }

    /// Attempt to extract as number (f64). Integers convert to float.
    #[inline]
    pub fn as_number(&self, gc: &GcHeap) -> Option<f64> {
        if let Some(f) = self.as_float() {
            Some(f)
        } else if let Some(i) = self.as_full_integer(gc) {
            Some(i as f64)
        } else {
            None
        }
    }

    // ---- Lua semantics ----

    /// Lua falsy: only nil and false are falsy.
    #[inline]
    pub fn is_falsy(&self) -> bool {
        self.is_nil() || (self.is_bool() && self.as_bool() == Some(false))
    }

    /// Lua truthy: everything except nil and false.
    #[inline]
    pub fn is_truthy(&self) -> bool {
        !self.is_falsy()
    }

    /// Get the raw bits for debugging/testing.
    #[inline]
    pub fn raw_bits(&self) -> u64 {
        self.0
    }

    /// Create a TValue from raw bits (for reconstructing from stored bits).
    #[inline]
    pub fn from_raw_bits(bits: u64) -> Self {
        TValue(bits)
    }
}

impl fmt::Debug for TValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_nil() {
            write!(f, "nil")
        } else if let Some(b) = self.as_bool() {
            write!(f, "{b}")
        } else if let Some(i) = self.as_integer() {
            write!(f, "{i}")
        } else if let Some(fl) = self.as_float() {
            write!(f, "{fl}")
        } else if self.is_gc() {
            match self.gc_sub_tag() {
                Some(GC_SUB_STRING) => write!(f, "string(#{})", self.gc_index().unwrap()),
                Some(GC_SUB_TABLE) => write!(f, "table(#{})", self.gc_index().unwrap()),
                Some(GC_SUB_CLOSURE) => write!(f, "closure(#{})", self.gc_index().unwrap()),
                Some(GC_SUB_NATIVE) => write!(f, "native(#{})", self.gc_index().unwrap()),
                Some(GC_SUB_UPVAL) => write!(f, "upval(#{})", self.gc_index().unwrap()),
                Some(GC_SUB_BOXED_INT) => write!(f, "boxedint(#{})", self.gc_index().unwrap()),
                _ => write!(f, "gc({:#x})", self.0 & PAYLOAD_MASK),
            }
        } else if self.is_light_userdata() {
            write!(f, "lightuserdata({:#x})", self.0 & PAYLOAD_MASK)
        } else {
            write!(f, "unknown({:#018x})", self.0)
        }
    }
}

impl PartialEq for TValue {
    fn eq(&self, other: &Self) -> bool {
        // For NaN-boxed values, bit equality works for all tagged types.
        // For floats, we need to handle NaN specially (Lua: NaN ~= NaN).
        if self.is_float() && other.is_float() {
            match (self.as_float(), other.as_float()) {
                (Some(a), Some(b)) => a == b,
                _ => false,
            }
        } else {
            self.0 == other.0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_size_of_tvalue() {
        assert_eq!(std::mem::size_of::<TValue>(), 8);
    }

    #[test]
    fn test_nil() {
        let v = TValue::nil();
        assert!(v.is_nil());
        assert!(!v.is_bool());
        assert!(!v.is_float());
        assert!(!v.is_integer());
        assert!(!v.is_gc());
        assert!(!v.is_light_userdata());
    }

    #[test]
    fn test_bool_true() {
        let v = TValue::from_bool(true);
        assert!(v.is_bool());
        assert_eq!(v.as_bool(), Some(true));
        assert!(!v.is_nil());
        assert!(!v.is_float());
        assert!(!v.is_integer());
    }

    #[test]
    fn test_bool_false() {
        let v = TValue::from_bool(false);
        assert!(v.is_bool());
        assert_eq!(v.as_bool(), Some(false));
    }

    #[test]
    fn test_float_zero() {
        let v = TValue::from_float(0.0);
        assert!(v.is_float());
        assert_eq!(v.as_float(), Some(0.0));
        assert!(!v.is_integer());
        assert!(!v.is_nil());
    }

    #[test]
    fn test_float_positive() {
        let v = TValue::from_float(1.5);
        assert!(v.is_float());
        assert_eq!(v.as_float(), Some(1.5));
    }

    #[test]
    fn test_float_negative() {
        let v = TValue::from_float(-7.25);
        assert!(v.is_float());
        assert_eq!(v.as_float(), Some(-7.25));
    }

    #[test]
    fn test_float_infinity() {
        let v = TValue::from_float(f64::INFINITY);
        assert!(v.is_float());
        assert_eq!(v.as_float(), Some(f64::INFINITY));
    }

    #[test]
    fn test_float_neg_infinity() {
        let v = TValue::from_float(f64::NEG_INFINITY);
        assert!(v.is_float());
        assert_eq!(v.as_float(), Some(f64::NEG_INFINITY));
    }

    #[test]
    fn test_float_min() {
        let v = TValue::from_float(f64::MIN);
        assert!(v.is_float());
        assert_eq!(v.as_float(), Some(f64::MIN));
    }

    #[test]
    fn test_float_max() {
        let v = TValue::from_float(f64::MAX);
        assert!(v.is_float());
        assert_eq!(v.as_float(), Some(f64::MAX));
    }

    #[test]
    fn test_float_min_positive() {
        let v = TValue::from_float(f64::MIN_POSITIVE);
        assert!(v.is_float());
        assert_eq!(v.as_float(), Some(f64::MIN_POSITIVE));
    }

    #[test]
    fn test_nan_canonicalization() {
        let nan1 = TValue::from_float(f64::NAN);
        let nan2 = TValue::from_float(-f64::NAN);
        // Both should be canonical NaN
        assert!(nan1.is_float());
        assert!(nan2.is_float());
        assert!(nan1.as_float().unwrap().is_nan());
        assert!(nan2.as_float().unwrap().is_nan());
        // Same bit pattern
        assert_eq!(nan1.raw_bits(), nan2.raw_bits());
        assert_eq!(nan1.raw_bits(), QNAN);
    }

    #[test]
    fn test_integer_zero() {
        let v = TValue::from_integer(0);
        assert!(v.is_integer());
        assert_eq!(v.as_integer(), Some(0));
        assert!(!v.is_float());
    }

    #[test]
    fn test_integer_positive() {
        let v = TValue::from_integer(42);
        assert!(v.is_integer());
        assert_eq!(v.as_integer(), Some(42));
    }

    #[test]
    fn test_integer_negative() {
        let v = TValue::from_integer(-100);
        assert!(v.is_integer());
        assert_eq!(v.as_integer(), Some(-100));
    }

    #[test]
    fn test_integer_max() {
        let v = TValue::from_integer(SMALL_INT_MAX);
        assert!(v.is_integer());
        assert_eq!(v.as_integer(), Some(SMALL_INT_MAX));
    }

    #[test]
    fn test_integer_min() {
        let v = TValue::from_integer(SMALL_INT_MIN);
        assert!(v.is_integer());
        assert_eq!(v.as_integer(), Some(SMALL_INT_MIN));
    }

    #[test]
    #[should_panic(expected = "outside 47-bit range")]
    fn test_integer_overflow() {
        TValue::from_integer(SMALL_INT_MAX + 1);
    }

    #[test]
    #[should_panic(expected = "outside 47-bit range")]
    fn test_integer_underflow() {
        TValue::from_integer(SMALL_INT_MIN - 1);
    }

    #[test]
    fn test_falsy_nil() {
        assert!(TValue::nil().is_falsy());
    }

    #[test]
    fn test_falsy_false() {
        assert!(TValue::from_bool(false).is_falsy());
    }

    #[test]
    fn test_truthy_true() {
        assert!(TValue::from_bool(true).is_truthy());
    }

    #[test]
    fn test_truthy_zero() {
        // In Lua, 0 is truthy!
        assert!(TValue::from_integer(0).is_truthy());
    }

    #[test]
    fn test_truthy_float_zero() {
        assert!(TValue::from_float(0.0).is_truthy());
    }

    #[test]
    fn test_type_exclusivity() {
        let values = [
            TValue::nil(),
            TValue::from_bool(true),
            TValue::from_float(1.0),
            TValue::from_integer(1),
        ];

        for v in &values {
            let type_count = v.is_nil() as u8 + v.is_bool() as u8 + v.is_integer() as u8;
            // Float detection is separate since canonical NaN is "float"
            if !v.is_nil() && !v.is_bool() && !v.is_integer() {
                assert!(v.is_float());
            }
            assert!(type_count <= 1, "value {v:?} has multiple types");
        }
    }

    #[test]
    fn test_debug_format() {
        assert_eq!(format!("{:?}", TValue::nil()), "nil");
        assert_eq!(format!("{:?}", TValue::from_bool(true)), "true");
        assert_eq!(format!("{:?}", TValue::from_bool(false)), "false");
        assert_eq!(format!("{:?}", TValue::from_integer(42)), "42");
    }

    // Property tests with proptest
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn prop_float_roundtrip(f in proptest::num::f64::ANY.prop_filter("non-NaN", |f| !f.is_nan())) {
            let v = TValue::from_float(f);
            assert!(v.is_float());
            assert_eq!(v.as_float(), Some(f));
        }

        #[test]
        fn prop_integer_roundtrip(i in SMALL_INT_MIN..=SMALL_INT_MAX) {
            let v = TValue::from_integer(i);
            assert!(v.is_integer());
            assert_eq!(v.as_integer(), Some(i));
        }

        #[test]
        fn prop_bool_roundtrip(b in proptest::bool::ANY) {
            let v = TValue::from_bool(b);
            assert!(v.is_bool());
            assert_eq!(v.as_bool(), Some(b));
        }

        #[test]
        fn prop_falsy_only_nil_and_false(i in SMALL_INT_MIN..=SMALL_INT_MAX) {
            // Integers are always truthy in Lua
            assert!(TValue::from_integer(i).is_truthy());
        }

        #[test]
        fn prop_float_truthy(f in proptest::num::f64::ANY) {
            // All floats (including NaN and 0.0) are truthy in Lua
            assert!(TValue::from_float(f).is_truthy());
        }

        #[test]
        fn prop_nan_always_canonical(bits in proptest::bits::u64::ANY) {
            let f = f64::from_bits(bits);
            if f.is_nan() {
                let v = TValue::from_float(f);
                assert_eq!(v.raw_bits(), QNAN);
            }
        }
    }
}
