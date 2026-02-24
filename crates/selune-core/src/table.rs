//! Hybrid array+hash table for Lua.

use crate::gc::GcIdx;
use crate::string::StringId;
use crate::value::TValue;
use indexmap::IndexMap;

/// A key in the hash part of a table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TableKey {
    Integer(i64),
    String(StringId),
    /// Float key, stored as raw bits for hashing.
    Float(u64),
    /// GC object key (table, closure, etc.), stored as raw TValue bits.
    GcPtr(u64),
    /// Boolean key.
    Boolean(bool),
}

/// A Lua table: hybrid array + hash map.
pub struct Table {
    /// Array part (1-indexed: array[0] corresponds to key 1).
    array: Vec<TValue>,
    /// Hash part for non-sequential keys (insertion-order preserving).
    hash: IndexMap<TableKey, TValue>,
    /// Metatable (if any).
    pub metatable: Option<GcIdx<Table>>,
}

impl Table {
    /// Create a new empty table with size hints.
    pub fn new(array_hint: usize, hash_hint: usize) -> Self {
        Table {
            array: Vec::with_capacity(array_hint),
            hash: IndexMap::with_capacity(hash_hint),
            metatable: None,
        }
    }

    /// Raw get by TValue key.
    pub fn raw_get(&self, key: TValue) -> TValue {
        // Fast path: integer key in array range
        if let Some(i) = key.as_integer() {
            if i >= 1 && (i as usize) <= self.array.len() {
                return self.array[(i - 1) as usize];
            }
        }
        // Float that is a whole integer
        if let Some(f) = key.as_float() {
            if f.fract() == 0.0 && f >= 1.0 && f <= self.array.len() as f64 {
                let idx = f as usize;
                if idx >= 1 && idx <= self.array.len() {
                    return self.array[idx - 1];
                }
            }
        }
        // Hash lookup
        if let Some(tk) = tvalue_to_table_key(key) {
            self.hash.get(&tk).copied().unwrap_or(TValue::nil())
        } else {
            TValue::nil()
        }
    }

    /// Raw set by TValue key.
    pub fn raw_set(&mut self, key: TValue, value: TValue) -> Result<(), &'static str> {
        if key.is_nil() {
            return Err("table index is nil");
        }
        if let Some(f) = key.as_float() {
            if f.is_nan() {
                return Err("table index is NaN");
            }
        }

        // Fast path: integer key in or near array range
        if let Some(i) = key.as_integer() {
            if i >= 1 {
                let idx = (i - 1) as usize;
                if idx < self.array.len() {
                    self.array[idx] = value;
                    return Ok(());
                }
                // Extend array if appending
                if idx == self.array.len() {
                    if value.is_nil() {
                        return Ok(()); // Don't extend for nil
                    }
                    self.array.push(value);
                    // Move hash entries that are now in array range
                    self.rehash_from_hash_to_array();
                    return Ok(());
                }
            }
        }

        // Float that is a whole integer — treat like integer key for array
        if let Some(f) = key.as_float() {
            if f.fract() == 0.0 && f >= 1.0 && f <= i64::MAX as f64 {
                let i = f as i64;
                let idx = (i - 1) as usize;
                if idx < self.array.len() {
                    self.array[idx] = value;
                    return Ok(());
                }
                if idx == self.array.len() {
                    if value.is_nil() {
                        return Ok(());
                    }
                    self.array.push(value);
                    self.rehash_from_hash_to_array();
                    return Ok(());
                }
            }
        }

        let tk = tvalue_to_table_key(key).unwrap();
        if value.is_nil() {
            // Keep tombstone (nil value) for iteration safety — next() can find dead keys
            // Only insert tombstone if the key existed; don't pollute with never-existed keys
            if self.hash.contains_key(&tk) {
                self.hash.insert(tk, value);
            }
        } else {
            self.hash.insert(tk, value);
        }
        Ok(())
    }

    /// Fast integer get (1-indexed).
    pub fn raw_geti(&self, key: i64) -> TValue {
        if key >= 1 && (key as usize) <= self.array.len() {
            self.array[(key - 1) as usize]
        } else {
            self.hash
                .get(&TableKey::Integer(key))
                .copied()
                .unwrap_or(TValue::nil())
        }
    }

    /// Fast integer set (1-indexed).
    pub fn raw_seti(&mut self, key: i64, value: TValue) {
        if key >= 1 {
            let idx = (key - 1) as usize;
            if idx < self.array.len() {
                self.array[idx] = value;
                return;
            }
            if idx == self.array.len() && !value.is_nil() {
                self.array.push(value);
                self.rehash_from_hash_to_array();
                return;
            }
        }
        if value.is_nil() {
            self.hash.shift_remove(&TableKey::Integer(key));
        } else {
            self.hash.insert(TableKey::Integer(key), value);
        }
    }

    /// Fast string key get.
    pub fn raw_get_str(&self, key: StringId) -> TValue {
        self.hash
            .get(&TableKey::String(key))
            .copied()
            .unwrap_or(TValue::nil())
    }

    /// Fast string key set.
    pub fn raw_set_str(&mut self, key: StringId, value: TValue) {
        if value.is_nil() {
            self.hash.shift_remove(&TableKey::String(key));
        } else {
            self.hash.insert(TableKey::String(key), value);
        }
    }

    /// Get the "length" of a table (boundary for array part).
    /// Returns the largest n such that t[n] is non-nil and t[n+1] is nil.
    pub fn length(&self) -> i64 {
        if self.array.is_empty() {
            return 0;
        }
        // If last element is non-nil, length = array.len()
        if !self.array.last().unwrap().is_nil() {
            return self.array.len() as i64;
        }
        // Binary search for boundary
        let mut lo = 0usize;
        let mut hi = self.array.len();
        while lo < hi {
            let mid = (lo + hi) / 2;
            if self.array[mid].is_nil() {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        lo as i64
    }

    /// Get the next key-value pair after `key` (for iteration).
    /// Returns Ok(Some(k,v)) for next pair, Ok(None) for end of iteration,
    /// Err(()) for invalid key (key not found in table).
    #[allow(clippy::result_unit_err)]
    pub fn next(&self, key: TValue) -> Result<Option<(TValue, TValue)>, ()> {
        if key.is_nil() {
            // Start iteration: first non-nil array element
            for (i, v) in self.array.iter().enumerate() {
                if !v.is_nil() {
                    return Ok(Some((TValue::from_integer((i + 1) as i64), *v)));
                }
            }
            // Then non-nil hash elements (skip tombstones)
            for (&k, &v) in &self.hash {
                if !v.is_nil() {
                    return Ok(Some((table_key_to_tvalue(k), v)));
                }
            }
            return Ok(None);
        }
        // Find current position and return next
        // This is O(n) but sufficient for now
        if let Some(i) = key.as_integer() {
            if i >= 1 && (i as usize) <= self.array.len() {
                // Key is in array range — present or tombstoned (nil = deleted during iteration)
                // Look for next non-nil in array
                for j in (i as usize)..self.array.len() {
                    if !self.array[j].is_nil() {
                        return Ok(Some((TValue::from_integer((j + 1) as i64), self.array[j])));
                    }
                }
                // Then non-nil hash elements (skip tombstones)
                for (&k, &v) in &self.hash {
                    if !v.is_nil() {
                        return Ok(Some((table_key_to_tvalue(k), v)));
                    }
                }
                return Ok(None);
            }
        }
        // Key is in hash: find and return next non-nil
        let tk = match tvalue_to_table_key(key) {
            Some(tk) => tk,
            None => return Err(()), // NaN or nil — invalid key
        };
        let mut found = false;
        for (&k, &v) in &self.hash {
            if found {
                if !v.is_nil() {
                    return Ok(Some((table_key_to_tvalue(k), v)));
                }
                // Skip tombstoned entries
                continue;
            }
            if k == tk {
                found = true;
            }
        }
        if found {
            Ok(None) // was last element (or only tombstones remain)
        } else {
            Err(()) // key not in hash
        }
    }

    /// Remove tombstones (nil-valued entries) from the hash part.
    /// Called during GC or rehash to reclaim memory.
    pub fn compact_hash(&mut self) {
        self.hash.retain(|_, v| !v.is_nil());
    }

    /// Move consecutive integer entries from hash into array.
    fn rehash_from_hash_to_array(&mut self) {
        loop {
            let next_idx = self.array.len() as i64 + 1;
            if let Some(v) = self.hash.shift_remove(&TableKey::Integer(next_idx)) {
                self.array.push(v);
            } else {
                break;
            }
        }
    }

    /// Clear weak entries: remove entries with dead keys/values.
    /// `is_dead` returns true if the TValue is a collectable GC object that is unmarked.
    pub fn clear_weak_entries<F>(&mut self, weak_keys: bool, weak_values: bool, is_dead: &F)
    where
        F: Fn(TValue) -> bool,
    {
        if weak_values {
            // Clear dead values in array part (set to nil)
            for v in self.array.iter_mut() {
                if !v.is_nil() && is_dead(*v) {
                    *v = TValue::nil();
                }
            }
            // Trim trailing nils from array
            while self.array.last().is_some_and(|v| v.is_nil()) {
                self.array.pop();
            }
        }
        // Clear dead keys/values in hash part
        let mut to_remove = Vec::new();
        for (k, v) in self.hash.iter() {
            let key_dead = weak_keys
                && match k {
                    TableKey::GcPtr(bits) => is_dead(TValue::from_raw_bits(*bits)),
                    _ => false,
                };
            let val_dead = weak_values && !v.is_nil() && is_dead(*v);
            if key_dead || val_dead {
                to_remove.push(*k);
            }
        }
        for k in to_remove {
            self.hash.shift_remove(&k);
        }
    }

    /// Iterate over all values in the array part (for GC traversal).
    pub fn array_values(&self) -> &[TValue] {
        &self.array
    }

    /// Mutable access to array values (for GC weak table clearing).
    pub fn array_values_mut(&mut self) -> &mut [TValue] {
        &mut self.array
    }

    /// Remove a hash entry by key (for GC weak table clearing).
    pub fn remove_hash_entry(&mut self, key: &TableKey) {
        self.hash.shift_remove(key);
    }

    /// Trim trailing nil values from the array part.
    pub fn trim_array(&mut self) {
        while self.array.last().is_some_and(|v| v.is_nil()) {
            self.array.pop();
        }
    }

    /// Iterate over all key-value pairs in the hash part (for GC traversal).
    pub fn hash_entries(&self) -> impl Iterator<Item = (&TableKey, &TValue)> {
        self.hash.iter()
    }
}

/// Convert a TValue to a TableKey for hash lookup.
fn tvalue_to_table_key(v: TValue) -> Option<TableKey> {
    if v.is_nil() {
        return None;
    }
    if let Some(i) = v.as_integer() {
        return Some(TableKey::Integer(i));
    }
    if let Some(f) = v.as_float() {
        if f.is_nan() {
            return None;
        }
        // Check if it's a whole integer
        if f.fract() == 0.0 && f >= i64::MIN as f64 && f <= i64::MAX as f64 {
            return Some(TableKey::Integer(f as i64));
        }
        return Some(TableKey::Float(f.to_bits()));
    }
    if let Some(b) = v.as_bool() {
        return Some(TableKey::Boolean(b));
    }
    if let Some(sid) = v.as_string_id() {
        return Some(TableKey::String(sid));
    }
    // GC object: use raw bits as identity
    if v.is_gc() {
        return Some(TableKey::GcPtr(v.raw_bits()));
    }
    None
}

/// Convert a TableKey back to a TValue.
fn table_key_to_tvalue(k: TableKey) -> TValue {
    match k {
        TableKey::Integer(i) => {
            if (-70368744177664..=70368744177663).contains(&i) {
                TValue::from_integer(i)
            } else {
                // Would need boxed int, but for iteration keys this is fine
                TValue::from_float(i as f64)
            }
        }
        TableKey::String(sid) => TValue::from_string_id(sid),
        TableKey::Float(bits) => TValue::from_float(f64::from_bits(bits)),
        TableKey::Boolean(b) => TValue::from_bool(b),
        TableKey::GcPtr(bits) => {
            // Reconstruct TValue from raw bits
            TValue::from_raw_bits(bits)
        }
    }
}

impl std::fmt::Debug for Table {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "table(array={}, hash={})",
            self.array.len(),
            self.hash.len()
        )
    }
}
