/// Lua string type with SSO (Small String Optimization) and interning.
///
/// Short strings (<=40 bytes) are stored inline and interned (deduplicated).
/// Long strings (>40 bytes) are heap-allocated and NOT interned.
use std::collections::HashMap;
use std::fmt;

/// Maximum bytes for inline (short) string storage.
const SSO_MAX: usize = 40;

/// An opaque handle to a string in the interner.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct StringId(pub u32);

/// Internal storage for string data.
#[derive(Clone)]
enum StringData {
    Short { buf: [u8; SSO_MAX], len: u8 },
    Long(Vec<u8>),
}

/// A Lua string with precomputed hash.
#[derive(Clone)]
pub struct TString {
    data: StringData,
    hash: u32,
}

impl TString {
    /// Create a new TString from bytes.
    fn new(bytes: &[u8]) -> Self {
        let hash = lua_hash(bytes);
        if bytes.len() <= SSO_MAX {
            let mut buf = [0u8; SSO_MAX];
            buf[..bytes.len()].copy_from_slice(bytes);
            TString {
                data: StringData::Short {
                    buf,
                    len: bytes.len() as u8,
                },
                hash,
            }
        } else {
            TString {
                data: StringData::Long(bytes.to_vec()),
                hash,
            }
        }
    }

    /// Get the bytes of this string.
    pub fn as_bytes(&self) -> &[u8] {
        match &self.data {
            StringData::Short { buf, len } => &buf[..*len as usize],
            StringData::Long(v) => v,
        }
    }

    /// Get the length in bytes.
    pub fn len(&self) -> usize {
        match &self.data {
            StringData::Short { len, .. } => *len as usize,
            StringData::Long(v) => v.len(),
        }
    }

    /// Returns true if the string is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns true if this is a short (inline) string.
    pub fn is_short(&self) -> bool {
        matches!(&self.data, StringData::Short { .. })
    }

    /// Get the precomputed hash.
    pub fn hash(&self) -> u32 {
        self.hash
    }
}

impl fmt::Debug for TString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Ok(s) = std::str::from_utf8(self.as_bytes()) {
            write!(f, "\"{}\"", s)
        } else {
            write!(f, "<binary string len={}>", self.len())
        }
    }
}

/// PUC Lua compatible hash function (luaS_hash algorithm).
///
/// This matches the hash used in PUC Lua 5.4 for string hashing.
pub fn lua_hash(bytes: &[u8]) -> u32 {
    let len = bytes.len();
    let mut h = len as u32;
    // Hash step: skip some bytes for long strings
    let step = (len >> 5) + 1;
    let mut i = len;
    while i >= step {
        h = h ^ ((h << 5).wrapping_add(h >> 2).wrapping_add(bytes[i - 1] as u32));
        i -= step;
    }
    h
}

/// String interner: owns all strings and provides deduplication for short strings.
#[derive(Debug)]
pub struct StringInterner {
    /// All strings, indexed by StringId.
    strings: Vec<TString>,
    /// Lookup table for short string deduplication: hash → list of StringIds.
    short_lookup: HashMap<u32, Vec<u32>>,
}

impl StringInterner {
    /// Create a new empty interner.
    pub fn new() -> Self {
        StringInterner {
            strings: Vec::new(),
            short_lookup: HashMap::new(),
        }
    }

    /// Intern a short string (<=40 bytes). Returns existing StringId if already interned.
    pub fn intern(&mut self, bytes: &[u8]) -> StringId {
        debug_assert!(bytes.len() <= SSO_MAX, "use create_long for long strings");
        let hash = lua_hash(bytes);

        // Check for existing entry
        if let Some(ids) = self.short_lookup.get(&hash) {
            for &id in ids {
                if self.strings[id as usize].as_bytes() == bytes {
                    return StringId(id);
                }
            }
        }

        // Create new entry
        let id = self.strings.len() as u32;
        self.strings.push(TString::new(bytes));
        self.short_lookup.entry(hash).or_default().push(id);
        StringId(id)
    }

    /// Intern a string of any length. Short strings are deduplicated; long strings are not.
    pub fn intern_or_create(&mut self, bytes: &[u8]) -> StringId {
        if bytes.len() <= SSO_MAX {
            self.intern(bytes)
        } else {
            self.create_long(bytes)
        }
    }

    /// Create a long string (>40 bytes). NOT interned — each call returns a unique ID.
    pub fn create_long(&mut self, bytes: &[u8]) -> StringId {
        let id = self.strings.len() as u32;
        self.strings.push(TString::new(bytes));
        StringId(id)
    }

    /// Get a string by its ID.
    pub fn get(&self, id: StringId) -> &TString {
        &self.strings[id.0 as usize]
    }

    /// Get the raw bytes of a string by its ID.
    pub fn get_bytes(&self, id: StringId) -> &[u8] {
        self.strings[id.0 as usize].as_bytes()
    }

    /// Get the number of strings stored.
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Returns true if no strings are stored.
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

impl Default for StringInterner {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_short_string_dedup() {
        let mut interner = StringInterner::new();
        let id1 = interner.intern(b"hello");
        let id2 = interner.intern(b"hello");
        assert_eq!(id1, id2);
        assert_eq!(interner.len(), 1);
    }

    #[test]
    fn test_different_strings_different_ids() {
        let mut interner = StringInterner::new();
        let id1 = interner.intern(b"hello");
        let id2 = interner.intern(b"world");
        assert_ne!(id1, id2);
        assert_eq!(interner.len(), 2);
    }

    #[test]
    fn test_sso_boundary_short() {
        let bytes = vec![b'a'; SSO_MAX];
        let s = TString::new(&bytes);
        assert!(s.is_short());
        assert_eq!(s.len(), SSO_MAX);
    }

    #[test]
    fn test_sso_boundary_long() {
        let bytes = vec![b'a'; SSO_MAX + 1];
        let s = TString::new(&bytes);
        assert!(!s.is_short());
        assert_eq!(s.len(), SSO_MAX + 1);
    }

    #[test]
    fn test_roundtrip_short() {
        let mut interner = StringInterner::new();
        let id = interner.intern(b"test string");
        assert_eq!(interner.get_bytes(id), b"test string");
    }

    #[test]
    fn test_roundtrip_long() {
        let mut interner = StringInterner::new();
        let long = vec![b'x'; 100];
        let id = interner.create_long(&long);
        assert_eq!(interner.get_bytes(id), &long[..]);
    }

    #[test]
    fn test_empty_string() {
        let mut interner = StringInterner::new();
        let id = interner.intern(b"");
        let s = interner.get(id);
        assert!(s.is_empty());
        assert_eq!(s.as_bytes(), b"");
    }

    #[test]
    fn test_binary_string_with_null() {
        let mut interner = StringInterner::new();
        let bytes = b"hello\0world";
        let id = interner.intern(bytes);
        assert_eq!(interner.get_bytes(id), bytes);
    }

    #[test]
    fn test_unicode_bytes() {
        let mut interner = StringInterner::new();
        let s = "こんにちは";
        let id = interner.intern(s.as_bytes());
        assert_eq!(interner.get_bytes(id), s.as_bytes());
    }

    #[test]
    fn test_long_string_uniqueness() {
        let mut interner = StringInterner::new();
        let long = vec![b'a'; 100];
        let id1 = interner.create_long(&long);
        let id2 = interner.create_long(&long);
        // Long strings are NOT interned — different IDs even for same content
        assert_ne!(id1, id2);
    }

    #[test]
    fn test_stress_10k_strings() {
        let mut interner = StringInterner::new();
        let mut ids = Vec::new();
        for i in 0..10_000u32 {
            let s = format!("string_{i}");
            ids.push(interner.intern(s.as_bytes()));
        }
        // Verify all retrievable
        for (i, id) in ids.iter().enumerate() {
            let expected = format!("string_{i}");
            assert_eq!(interner.get_bytes(*id), expected.as_bytes());
        }
        // Verify dedup
        for i in 0..10_000u32 {
            let s = format!("string_{i}");
            let id2 = interner.intern(s.as_bytes());
            assert_eq!(id2, ids[i as usize]);
        }
        assert_eq!(interner.len(), 10_000);
    }

    #[test]
    fn test_hash_consistency() {
        let h1 = lua_hash(b"hello");
        let h2 = lua_hash(b"hello");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_hash_different_strings() {
        let h1 = lua_hash(b"hello");
        let h2 = lua_hash(b"world");
        // Different strings should (usually) have different hashes
        // This is probabilistic but these specific strings are known to differ
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_intern_or_create_short() {
        let mut interner = StringInterner::new();
        let id1 = interner.intern_or_create(b"short");
        let id2 = interner.intern_or_create(b"short");
        assert_eq!(id1, id2);
    }

    #[test]
    fn test_intern_or_create_long() {
        let mut interner = StringInterner::new();
        let long = vec![b'z'; 100];
        let id1 = interner.intern_or_create(&long);
        let id2 = interner.intern_or_create(&long);
        // Long strings not interned
        assert_ne!(id1, id2);
    }
}
