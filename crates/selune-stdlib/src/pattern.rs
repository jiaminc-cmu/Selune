//! Lua 5.4 pattern matching engine.
//!
//! Implements Lua's pattern matching, which is a custom pattern language distinct
//! from regular expressions. Supports character classes, quantifiers, anchors,
//! captures, balanced matches (`%bxy`), and frontier patterns (`%f[set]`).

/// Maximum number of captures allowed (Lua 5.4 limit: 32).
const MAX_CAPTURES: usize = 32;

/// Maximum recursion depth for the backtracking matcher.
const MAX_MATCH_DEPTH: usize = 200;

/// Sentinel value for position captures (empty `()` captures).
pub const CAP_POSITION: usize = usize::MAX;

/// Result of a successful pattern match.
#[derive(Debug, Clone)]
pub struct MatchState {
    /// Capture pairs: `(start, end)` byte offsets into the subject string.
    ///
    /// - For normal `(...)` captures, `start..end` is the captured substring.
    /// - For position captures (empty `()`), `start` is the position and
    ///   `end` is `CAP_POSITION`.
    /// - Capture 0 is always the full match.
    pub captures: Vec<(usize, usize)>,
}

/// Internal capture tracking during matching.
#[derive(Debug, Clone, Copy)]
enum CapStatus {
    /// Capture opened at `pos` but not yet closed.
    Open(usize),
    /// Capture closed: `(start, end)`.
    Closed(usize, usize),
    /// Position capture closed at `pos`.
    Position(usize),
}

/// Internal matcher state. Holds references to subject and pattern along with
/// mutable capture state.
struct Matcher<'a> {
    subject: &'a [u8],
    pattern: &'a [u8],
    caps: Vec<CapStatus>,
    depth: usize,
    error: Option<String>,
}

/// Find the first match of `pattern` in `subject` starting at byte offset `init`.
///
/// Returns `None` if no match is found. On success, returns `Some(MatchState)`
/// where `captures[0]` is always the full match range, and `captures[1..]`
/// correspond to explicit `(...)` captures in the pattern.
/// Validate a Lua pattern, returning an error message if invalid.
pub fn validate_pattern(pattern: &[u8]) -> Result<(), String> {
    let mut i = 0;
    let pat = if !pattern.is_empty() && pattern[0] == b'^' { &pattern[1..] } else { pattern };
    let mut open_parens = 0i32;
    while i < pat.len() {
        match pat[i] {
            b'(' => {
                open_parens += 1;
                i += 1;
            }
            b')' => {
                if open_parens <= 0 {
                    return Err("invalid pattern capture".to_string());
                }
                open_parens -= 1;
                i += 1;
            }
            b'%' => {
                i += 1;
                if i >= pat.len() {
                    return Err("malformed pattern (ends with '%%')".to_string());
                }
                if pat[i] == b'b' {
                    // %bxy needs exactly 2 more bytes
                    if i + 2 >= pat.len() {
                        return Err("malformed pattern (missing arguments to '%%b')".to_string());
                    }
                    i += 3; // skip 'b', x, y
                } else if pat[i] == b'f' {
                    // %f must be followed by [
                    i += 1;
                    if i >= pat.len() || pat[i] != b'[' {
                        return Err("missing '[' after '%%f' in pattern".to_string());
                    }
                    // Skip the set
                    i += 1;
                    if i < pat.len() && pat[i] == b'^' {
                        i += 1;
                    }
                    if i < pat.len() && pat[i] == b']' {
                        i += 1;
                    }
                    let mut found_close = false;
                    while i < pat.len() {
                        if pat[i] == b']' {
                            found_close = true;
                            i += 1;
                            break;
                        } else if pat[i] == b'%' && i + 1 < pat.len() {
                            i += 2;
                        } else {
                            i += 1;
                        }
                    }
                    if !found_close {
                        return Err("malformed pattern (missing ']')".to_string());
                    }
                } else {
                    i += 1;
                }
            }
            b'[' => {
                i += 1;
                // skip optional '^'
                if i < pat.len() && pat[i] == b'^' {
                    i += 1;
                }
                // first ']' after '[' or '[^' is literal
                if i < pat.len() && pat[i] == b']' {
                    i += 1;
                }
                let mut found_close = false;
                while i < pat.len() {
                    if pat[i] == b']' {
                        found_close = true;
                        i += 1;
                        break;
                    } else if pat[i] == b'%' && i + 1 < pat.len() {
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                if !found_close {
                    return Err("malformed pattern (missing ']')".to_string());
                }
            }
            _ => i += 1,
        }
    }
    if open_parens > 0 {
        return Err("unfinished capture".to_string());
    }
    Ok(())
}

pub fn pattern_find(subject: &[u8], pattern: &[u8], init: usize) -> Result<Option<MatchState>, String> {
    let anchor = !pattern.is_empty() && pattern[0] == b'^';
    let pat = if anchor { &pattern[1..] } else { pattern };

    let mut m = Matcher {
        subject,
        pattern: pat,
        caps: Vec::new(),
        depth: 0,
        error: None,
    };

    // Try matching at each starting position.
    let mut si = init;
    loop {
        m.caps.clear();
        m.depth = 0;
        if let Some(end) = m.match_pattern(pat, si) {
            return Ok(Some(m.build_result(si, end)));
        }
        if let Some(err) = m.error.take() {
            return Err(err);
        }
        if anchor || si >= subject.len() {
            return Ok(None);
        }
        si += 1;
    }
}

/// A public matcher for gsub that tries matching at a specific position only.
pub struct PatternMatcher<'a> {
    subject: &'a [u8],
    pat: &'a [u8],
}

impl<'a> PatternMatcher<'a> {
    pub fn new(subject: &'a [u8], pat: &'a [u8]) -> Self {
        PatternMatcher { subject, pat }
    }

    /// Try to match the pattern at exactly position `si`. Does NOT search forward.
    pub fn try_match_at(&mut self, si: usize) -> Result<Option<MatchState>, String> {
        let mut m = Matcher {
            subject: self.subject,
            pattern: self.pat,
            caps: Vec::new(),
            depth: 0,
            error: None,
        };
        if let Some(end) = m.match_pattern(self.pat, si) {
            Ok(Some(m.build_result(si, end)))
        } else if let Some(err) = m.error.take() {
            Err(err)
        } else {
            Ok(None)
        }
    }
}

/// Find all non-overlapping matches in `subject` starting at `init`.
///
/// This is useful for implementing `string.gmatch`. Each call to the returned
/// iterator yields the next `MatchState`.
pub fn pattern_gmatch<'a>(subject: &'a [u8], pattern: &'a [u8], init: usize) -> GmatchIter<'a> {
    let anchor = !pattern.is_empty() && pattern[0] == b'^';
    let pat_start = if anchor { 1 } else { 0 };
    GmatchIter {
        subject,
        pattern,
        pat_start,
        pos: init,
        anchor,
        finished: false,
        lastmatch: None,
    }
}

/// Iterator for `gmatch`-style repeated matching.
pub struct GmatchIter<'a> {
    subject: &'a [u8],
    pattern: &'a [u8],
    pat_start: usize,
    pos: usize,
    anchor: bool,
    finished: bool,
    lastmatch: Option<usize>,
}

impl<'a> Iterator for GmatchIter<'a> {
    type Item = MatchState;

    fn next(&mut self) -> Option<MatchState> {
        if self.finished {
            return None;
        }

        let pat = &self.pattern[self.pat_start..];
        let mut m = Matcher {
            subject: self.subject,
            pattern: pat,
            caps: Vec::new(),
            depth: 0,
            error: None,
        };

        let mut si = self.pos;
        loop {
            if si > self.subject.len() {
                self.finished = true;
                return None;
            }
            m.caps.clear();
            m.depth = 0;
            if let Some(end) = m.match_pattern(pat, si) {
                // Guard against repeated empty match at same position (Lua 5.3.3+).
                if end != si || self.lastmatch != Some(end) {
                    let result = m.build_result(si, end);
                    self.pos = end;
                    self.lastmatch = Some(end);
                    if self.anchor {
                        self.finished = true;
                    }
                    return Some(result);
                }
                // Repeated empty match — fall through to advance.
            }
            if self.anchor || si >= self.subject.len() {
                self.finished = true;
                return None;
            }
            si += 1;
        }
    }
}

// ---------------------------------------------------------------------------
// Pattern element parsing helpers
// ---------------------------------------------------------------------------

/// Classifies a single character class like `%a`, `%d`, etc.
fn match_class(ch: u8, class: u8) -> bool {
    let lower = class.to_ascii_lowercase();
    let result = match lower {
        b'a' => ch.is_ascii_alphabetic(),
        b'c' => ch.is_ascii_control(),
        b'd' => ch.is_ascii_digit(),
        b'g' => ch.is_ascii_graphic(),
        b'l' => ch.is_ascii_lowercase(),
        b'p' => ch.is_ascii_punctuation(),
        b's' => ch.is_ascii_whitespace(),
        b'u' => ch.is_ascii_uppercase(),
        b'w' => ch.is_ascii_alphanumeric(),
        b'x' => ch.is_ascii_hexdigit(),
        b'z' => ch == 0,
        _ => return ch == class,
    };
    // If the class letter was uppercase, negate the result.
    if class.is_ascii_uppercase() {
        !result
    } else {
        result
    }
}

/// Check if `ch` matches a character set `[...]` starting at `pattern[pp]`.
/// `pp` should point to the first byte after the opening `[`.
/// Returns `(matched, end_of_set)` where `end_of_set` is the index after `]`.
fn match_set(pattern: &[u8], mut pp: usize, ch: u8) -> (bool, usize) {
    let complement = pp < pattern.len() && pattern[pp] == b'^';
    if complement {
        pp += 1;
    }

    let mut matched = false;

    // `]` as the very first character after `[` or `[^` is a literal, not end of set.
    if pp < pattern.len() && pattern[pp] == b']' {
        if ch == b']' {
            matched = true;
        }
        pp += 1;
    }

    while pp < pattern.len() {
        if pattern[pp] == b']' {
            // End of set.
            let result = if complement { !matched } else { matched };
            return (result, pp + 1);
        } else if pattern[pp] == b'%' && pp + 1 < pattern.len() {
            pp += 1;
            if match_class(ch, pattern[pp]) {
                matched = true;
            }
            pp += 1;
        } else if pp + 2 < pattern.len() && pattern[pp + 1] == b'-' && pattern[pp + 2] != b']' {
            // Range like `a-z`.
            let lo = pattern[pp];
            let hi = pattern[pp + 2];
            if ch >= lo && ch <= hi {
                matched = true;
            }
            pp += 3;
        } else {
            if ch == pattern[pp] {
                matched = true;
            }
            pp += 1;
        }
    }

    // Unterminated set -- treat as no match and consume to end.
    (false, pp)
}

/// Test if the character `ch` matches a single pattern element starting at
/// `pattern[pp]`. Returns true/false.
///
/// This does NOT handle sets `[...]` -- the caller must handle those separately
/// because they span variable lengths. For single-char elements like `.`, `%a`, or
/// literal bytes, this works.
fn match_single(pattern: &[u8], pp: usize, ch: u8) -> bool {
    match pattern[pp] {
        b'.' => true,
        b'%' => {
            if pp + 1 < pattern.len() {
                match_class(ch, pattern[pp + 1])
            } else {
                false
            }
        }
        c => c == ch,
    }
}

/// Return the number of bytes consumed by one pattern element starting at
/// `pattern[pp]`. For `%x` it's 2, for `[...]` it's the whole set including
/// brackets, for anything else it's 1.
fn element_len(pattern: &[u8], pp: usize) -> usize {
    if pp >= pattern.len() {
        return 0;
    }
    match pattern[pp] {
        b'%' => {
            if pp + 1 < pattern.len() {
                // %bxy consumes 4 bytes.
                if pattern[pp + 1] == b'b' {
                    4
                } else if pattern[pp + 1] == b'f' {
                    // %f[set] -- the %f itself is 2 bytes; the set is handled separately.
                    2
                } else {
                    2
                }
            } else {
                1
            }
        }
        b'[' => {
            let mut p = pp + 1;
            // Skip initial `^` and/or `]` which are part of the set, not closing.
            if p < pattern.len() && pattern[p] == b'^' {
                p += 1;
            }
            if p < pattern.len() && pattern[p] == b']' {
                p += 1;
            }
            while p < pattern.len() && pattern[p] != b']' {
                if pattern[p] == b'%' && p + 1 < pattern.len() {
                    p += 2;
                } else {
                    p += 1;
                }
            }
            if p < pattern.len() {
                p + 1 - pp
            } else {
                p - pp
            }
        }
        _ => 1,
    }
}

/// Test if subject byte `ch` matches the pattern element starting at
/// `pattern[pp]`, handling single chars, `%x` classes, and `[set]`.
fn singlematch(pattern: &[u8], pp: usize, ch: u8) -> bool {
    if pp >= pattern.len() {
        return false;
    }
    match pattern[pp] {
        b'[' => {
            let (matched, _) = match_set(pattern, pp + 1, ch);
            matched
        }
        _ => match_single(pattern, pp, ch),
    }
}

// ---------------------------------------------------------------------------
// Core recursive matcher
// ---------------------------------------------------------------------------

impl<'a> Matcher<'a> {
    /// Main recursive matching function.
    ///
    /// Tries to match `pattern[pp..]` against `subject[si..]`.
    /// Returns `Some(end)` on success where `end` is the byte offset in subject
    /// just past the matched portion, or `None` on failure.
    fn match_pattern(&mut self, pattern: &[u8], si: usize) -> Option<usize> {
        self.depth += 1;
        if self.depth > MAX_MATCH_DEPTH {
            self.depth -= 1;
            return None;
        }

        let result = self.match_inner(pattern, 0, si);
        self.depth -= 1;
        result
    }

    fn match_inner(&mut self, pattern: &[u8], mut pp: usize, mut si: usize) -> Option<usize> {
        loop {
            if pp >= pattern.len() {
                // Pattern exhausted -- match succeeds at current position.
                return Some(si);
            }

            // Handle anchors.
            if pattern[pp] == b'$' && pp + 1 == pattern.len() {
                return if si == self.subject.len() {
                    Some(si)
                } else {
                    None
                };
            }

            // Handle captures.
            if pattern[pp] == b'(' {
                if pp + 1 < pattern.len() && pattern[pp + 1] == b')' {
                    // Position capture.
                    return self.match_position_capture(pattern, pp + 2, si);
                } else {
                    return self.match_open_capture(pattern, pp + 1, si);
                }
            }
            if pattern[pp] == b')' {
                return self.match_close_capture(pattern, pp + 1, si);
            }

            // Handle %bxy balanced match.
            if pattern[pp] == b'%'
                && pp + 1 < pattern.len()
                && pattern[pp + 1] == b'b'
                && pp + 3 < pattern.len()
            {
                return self.match_balance(pattern, pp, si);
            }

            // Handle %f[set] frontier pattern.
            if pattern[pp] == b'%'
                && pp + 1 < pattern.len()
                && pattern[pp + 1] == b'f'
                && pp + 2 < pattern.len()
                && pattern[pp + 2] == b'['
            {
                return self.match_frontier(pattern, pp, si);
            }

            // Handle %0-%9 back-references.
            if pattern[pp] == b'%'
                && pp + 1 < pattern.len()
                && pattern[pp + 1] >= b'0'
                && pattern[pp + 1] <= b'9'
            {
                let n = (pattern[pp + 1] - b'0') as usize;
                // %0 is not valid as a back-reference in patterns
                if n == 0 {
                    self.error = Some("invalid capture index %0".to_string());
                    return None;
                }
                let cap_idx = n - 1; // %1 = index 0, etc.
                // Check if this capture exists and is closed
                if cap_idx >= self.caps.len() {
                    self.error = Some(format!("invalid capture index %{}", n));
                    return None;
                }
                match self.caps[cap_idx] {
                    CapStatus::Open(_) => {
                        self.error = Some(format!("invalid capture index %{}", n));
                        return None;
                    }
                    CapStatus::Closed(start, end) => {
                        let captured = &self.subject[start..end];
                        let cap_len = captured.len();
                        if si + cap_len <= self.subject.len()
                            && &self.subject[si..si + cap_len] == captured
                        {
                            pp += 2;
                            si += cap_len;
                            continue;
                        }
                        return None;
                    }
                    CapStatus::Position(_) => {
                        // Position captures can't be used as back-references
                        self.error = Some(format!("invalid capture index %{}", n));
                        return None;
                    }
                }
            }

            // Determine the current element length and check for quantifiers.
            let elen = element_len(pattern, pp);
            let after_elem = pp + elen;
            let has_quantifier = after_elem < pattern.len()
                && matches!(pattern[after_elem], b'*' | b'+' | b'-' | b'?');

            if has_quantifier {
                let quantifier = pattern[after_elem];
                let rest = after_elem + 1;
                match quantifier {
                    b'*' => return self.match_greedy(pattern, pp, elen, rest, si, 0),
                    b'+' => return self.match_greedy(pattern, pp, elen, rest, si, 1),
                    b'-' => return self.match_lazy(pattern, pp, elen, rest, si),
                    b'?' => return self.match_optional(pattern, pp, elen, rest, si),
                    _ => unreachable!(),
                }
            }

            // No quantifier -- match exactly one element.
            if si >= self.subject.len() {
                return None;
            }
            if !singlematch(pattern, pp, self.subject[si]) {
                return None;
            }
            si += 1;
            pp += elen;
        }
    }

    /// Greedy quantifier: `elem*` (min=0) or `elem+` (min=1).
    fn match_greedy(
        &mut self,
        pattern: &[u8],
        pp: usize,
        _elen: usize,
        rest_pp: usize,
        si: usize,
        min_count: usize,
    ) -> Option<usize> {
        // Count maximum matches.
        let mut count = 0usize;
        while si + count < self.subject.len()
            && singlematch(pattern, pp, self.subject[si + count])
        {
            count += 1;
        }

        // Try matching the rest from the longest match downward.
        while count >= min_count {
            let saved_caps = self.caps.clone();
            if let Some(end) = self.match_inner(pattern, rest_pp, si + count) {
                return Some(end);
            }
            self.caps = saved_caps;
            if count == 0 {
                break;
            }
            count -= 1;
        }
        None
    }

    /// Lazy quantifier: `elem-`.
    fn match_lazy(
        &mut self,
        pattern: &[u8],
        pp: usize,
        _elen: usize,
        rest_pp: usize,
        si: usize,
    ) -> Option<usize> {
        let mut pos = si;
        loop {
            let saved_caps = self.caps.clone();
            if let Some(end) = self.match_inner(pattern, rest_pp, pos) {
                return Some(end);
            }
            self.caps = saved_caps;
            if pos < self.subject.len() && singlematch(pattern, pp, self.subject[pos]) {
                pos += 1;
            } else {
                return None;
            }
        }
    }

    /// Optional quantifier: `elem?`.
    fn match_optional(
        &mut self,
        pattern: &[u8],
        pp: usize,
        _elen: usize,
        rest_pp: usize,
        si: usize,
    ) -> Option<usize> {
        // Try with the element first (greedy).
        if si < self.subject.len() && singlematch(pattern, pp, self.subject[si]) {
            let saved_caps = self.caps.clone();
            if let Some(end) = self.match_inner(pattern, rest_pp, si + 1) {
                return Some(end);
            }
            self.caps = saved_caps;
        }
        // Try without the element.
        self.match_inner(pattern, rest_pp, si)
    }

    /// `%bxy` balanced match.
    fn match_balance(
        &mut self,
        pattern: &[u8],
        pp: usize,
        si: usize,
    ) -> Option<usize> {
        let open = pattern[pp + 2];
        let close = pattern[pp + 3];
        let rest_pp = pp + 4;

        if si >= self.subject.len() || self.subject[si] != open {
            return None;
        }

        let mut count = 1i32;
        let mut pos = si + 1;
        while pos < self.subject.len() {
            // Check close FIRST (important when open == close, e.g., %b'')
            if self.subject[pos] == close {
                count -= 1;
                if count == 0 {
                    return self.match_inner(pattern, rest_pp, pos + 1);
                }
            } else if self.subject[pos] == open {
                count += 1;
            }
            pos += 1;
        }
        None
    }

    /// `%f[set]` frontier pattern: matches the transition where the previous
    /// character does not match `[set]` but the current character does.
    /// This is a zero-width assertion.
    fn match_frontier(
        &mut self,
        pattern: &[u8],
        pp: usize,
        si: usize,
    ) -> Option<usize> {
        // pp points to '%', pp+1 is 'f', pp+2 is '['
        let set_start = pp + 2; // points to '['
        let set_inner = set_start + 1; // points to first byte inside [...]

        // Calculate end of set.
        let set_elen = element_len(pattern, set_start);
        let rest_pp = set_start + set_elen;

        let prev_ch = if si > 0 { self.subject[si - 1] } else { b'\0' };
        let curr_ch = if si < self.subject.len() {
            self.subject[si]
        } else {
            b'\0'
        };

        let (prev_matches, _) = match_set(pattern, set_inner, prev_ch);
        let (curr_matches, _) = match_set(pattern, set_inner, curr_ch);

        if !prev_matches && curr_matches {
            self.match_inner(pattern, rest_pp, si)
        } else {
            None
        }
    }

    /// Get the byte slice for a closed capture by index (0-based among user captures).
    fn get_closed_capture(&self, idx: usize) -> Option<&[u8]> {
        // Find the idx-th capture (skipping open/position captures for counting purposes).
        // In Lua, captures are numbered in order of their opening parenthesis.
        if idx < self.caps.len() {
            match self.caps[idx] {
                CapStatus::Closed(start, end) => Some(&self.subject[start..end]),
                _ => None,
            }
        } else {
            None
        }
    }

    /// Open a capture group.
    fn match_open_capture(
        &mut self,
        pattern: &[u8],
        rest_pp: usize,
        si: usize,
    ) -> Option<usize> {
        if self.caps.len() >= MAX_CAPTURES {
            return None; // too many captures
        }
        let idx = self.caps.len();
        self.caps.push(CapStatus::Open(si));
        if let Some(end) = self.match_inner(pattern, rest_pp, si) {
            return Some(end);
        }
        // Backtrack: remove capture.
        self.caps.truncate(idx);
        None
    }

    /// Close the most recent open capture.
    fn match_close_capture(
        &mut self,
        pattern: &[u8],
        rest_pp: usize,
        si: usize,
    ) -> Option<usize> {
        // Find the last open capture.
        let mut idx = None;
        for i in (0..self.caps.len()).rev() {
            if matches!(self.caps[i], CapStatus::Open(_)) {
                idx = Some(i);
                break;
            }
        }
        let idx = match idx {
            Some(i) => i,
            None => return None, // unmatched close
        };
        let start = match self.caps[idx] {
            CapStatus::Open(s) => s,
            _ => unreachable!(),
        };
        let saved = self.caps[idx];
        self.caps[idx] = CapStatus::Closed(start, si);
        if let Some(end) = self.match_inner(pattern, rest_pp, si) {
            return Some(end);
        }
        // Backtrack.
        self.caps[idx] = saved;
        None
    }

    /// Position capture: `()`.
    fn match_position_capture(
        &mut self,
        pattern: &[u8],
        rest_pp: usize,
        si: usize,
    ) -> Option<usize> {
        if self.caps.len() >= MAX_CAPTURES {
            return None;
        }
        let idx = self.caps.len();
        self.caps.push(CapStatus::Position(si));
        if let Some(end) = self.match_inner(pattern, rest_pp, si) {
            return Some(end);
        }
        self.caps.truncate(idx);
        None
    }

    /// Build the final `MatchState` from the internal capture list.
    fn build_result(&self, match_start: usize, match_end: usize) -> MatchState {
        let mut captures = Vec::with_capacity(self.caps.len() + 1);
        // Capture 0 is always the full match.
        captures.push((match_start, match_end));
        for cap in &self.caps {
            match *cap {
                CapStatus::Closed(start, end) => captures.push((start, end)),
                CapStatus::Position(pos) => captures.push((pos, CAP_POSITION)),
                CapStatus::Open(start) => {
                    // Unclosed capture -- shouldn't happen in a successful match,
                    // but treat as extending to end of match.
                    captures.push((start, match_end));
                }
            }
        }
        MatchState { captures }
    }
}

// ---------------------------------------------------------------------------
// GSub helper
// ---------------------------------------------------------------------------

/// Apply a pattern-based replacement, expanding `%0`..`%9` backreferences
/// and `%%` escapes in the replacement string.
///
/// `replacement` is the replacement pattern (may contain `%n` references).
/// `ms` is the match state from a successful match.
/// `subject` is the original subject string.
/// Returns the expanded replacement string.
pub fn expand_replacement(replacement: &[u8], ms: &MatchState, subject: &[u8]) -> Result<Vec<u8>, String> {
    let mut result = Vec::new();
    let mut i = 0;
    // Number of user captures (excluding capture 0 = full match).
    let num_user_captures = ms.captures.len() - 1;
    while i < replacement.len() {
        if replacement[i] == b'%' && i + 1 < replacement.len() {
            let next = replacement[i + 1];
            if next >= b'0' && next <= b'9' {
                let n = (next - b'0') as usize;
                // PUC Lua: %0 = whole match. %1..%9 = explicit captures.
                // When no explicit captures, %1 = whole match (capture index 0).
                // But %2..%9 with no explicit captures should error.
                let idx = if n == 0 {
                    0 // %0 always = full match
                } else if num_user_captures == 0 {
                    // No explicit captures: %1 = whole match, %2+ = error
                    if n == 1 {
                        0
                    } else {
                        return Err(format!("invalid capture index %{}", n));
                    }
                } else {
                    if n > num_user_captures {
                        return Err(format!("invalid capture index %{}", n));
                    }
                    n
                };
                let (start, end) = ms.captures[idx];
                if end == CAP_POSITION {
                    let pos_str = (start + 1).to_string();
                    result.extend_from_slice(pos_str.as_bytes());
                } else {
                    result.extend_from_slice(&subject[start..end]);
                }
                i += 2;
            } else if next == b'%' {
                result.push(b'%');
                i += 2;
            } else {
                return Err("invalid use of '%' in replacement string".to_string());
            }
        } else {
            result.push(replacement[i]);
            i += 1;
        }
    }
    Ok(result)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn find(subject: &str, pattern: &str) -> Option<(usize, usize)> {
        pattern_find(subject.as_bytes(), pattern.as_bytes(), 0)
            .unwrap()
            .map(|ms| ms.captures[0])
    }

    fn find_at(subject: &str, pattern: &str, init: usize) -> Option<(usize, usize)> {
        pattern_find(subject.as_bytes(), pattern.as_bytes(), init)
            .unwrap()
            .map(|ms| ms.captures[0])
    }

    fn captures(subject: &str, pattern: &str) -> Option<Vec<(usize, usize)>> {
        pattern_find(subject.as_bytes(), pattern.as_bytes(), 0)
            .unwrap()
            .map(|ms| ms.captures)
    }

    #[test]
    fn test_literal_match() {
        assert_eq!(find("hello world", "world"), Some((6, 11)));
        assert_eq!(find("hello world", "xyz"), None);
        assert_eq!(find("hello", "hello"), Some((0, 5)));
    }

    #[test]
    fn test_dot() {
        assert_eq!(find("abc", "a.c"), Some((0, 3)));
        assert_eq!(find("aXc", "a.c"), Some((0, 3)));
        assert_eq!(find("ac", "a.c"), None);
    }

    #[test]
    fn test_character_classes() {
        assert_eq!(find("abc123", "%a+"), Some((0, 3)));
        assert_eq!(find("abc123", "%d+"), Some((3, 6)));
        assert_eq!(find("Hello", "%u%l+"), Some((0, 5)));
        assert_eq!(find("  \t\n", "%s+"), Some((0, 4)));
        assert_eq!(find("abc!def", "%p"), Some((3, 4)));
        assert_eq!(find("0aFF9", "%x+"), Some((0, 5)));
    }

    #[test]
    fn test_negated_classes() {
        assert_eq!(find("abc123", "%A+"), Some((3, 6))); // non-alpha
        assert_eq!(find("abc123", "%D+"), Some((0, 3))); // non-digit
    }

    #[test]
    fn test_character_set() {
        assert_eq!(find("hello", "[helo]+"), Some((0, 5)));
        assert_eq!(find("abc", "[a-c]+"), Some((0, 3)));
        assert_eq!(find("abc", "[^a-c]+"), None);
        assert_eq!(find("xyz", "[^a-c]+"), Some((0, 3)));
    }

    #[test]
    fn test_set_with_closing_bracket() {
        // `]` as first char in set is literal
        assert_eq!(find("]abc", "[]a]+"), Some((0, 2)));
    }

    #[test]
    fn test_quantifier_star() {
        assert_eq!(find("aaa", "a*"), Some((0, 3)));
        assert_eq!(find("bbb", "a*"), Some((0, 0))); // matches empty at start
        assert_eq!(find("aaabbb", "a*b+"), Some((0, 6)));
    }

    #[test]
    fn test_quantifier_plus() {
        assert_eq!(find("aaa", "a+"), Some((0, 3)));
        assert_eq!(find("bbb", "a+"), None);
    }

    #[test]
    fn test_quantifier_minus() {
        // Lazy: matches as few as possible.
        assert_eq!(find("aaa", "a-"), Some((0, 0)));
        // But with more pattern after, it expands as needed.
        assert_eq!(find("<tag>content</tag>", "<(.-)>"), Some((0, 5)));
    }

    #[test]
    fn test_quantifier_question() {
        assert_eq!(find("color", "colou?r"), Some((0, 5)));
        assert_eq!(find("colour", "colou?r"), Some((0, 6)));
    }

    #[test]
    fn test_anchor_caret() {
        assert_eq!(find("hello", "^hello"), Some((0, 5)));
        assert_eq!(find("say hello", "^hello"), None);
    }

    #[test]
    fn test_anchor_dollar() {
        assert_eq!(find("hello", "hello$"), Some((0, 5)));
        assert_eq!(find("hello world", "hello$"), None);
        assert_eq!(find("world", "world$"), Some((0, 5)));
    }

    #[test]
    fn test_both_anchors() {
        assert_eq!(find("hello", "^hello$"), Some((0, 5)));
        assert_eq!(find("hello!", "^hello$"), None);
    }

    #[test]
    fn test_captures_basic() {
        let caps = captures("hello world", "(hello) (world)").unwrap();
        assert_eq!(caps.len(), 3);
        assert_eq!(caps[0], (0, 11));   // full match
        assert_eq!(caps[1], (0, 5));    // first capture
        assert_eq!(caps[2], (6, 11));   // second capture
    }

    #[test]
    fn test_position_capture() {
        let caps = captures("hello", "()hello()").unwrap();
        assert_eq!(caps.len(), 3);
        assert_eq!(caps[0], (0, 5));
        assert_eq!(caps[1], (0, CAP_POSITION));
        assert_eq!(caps[2], (5, CAP_POSITION));
    }

    #[test]
    fn test_nested_captures() {
        let caps = captures("abcd", "((a)(b))").unwrap();
        assert_eq!(caps.len(), 4);
        assert_eq!(caps[0], (0, 2)); // full match
        assert_eq!(caps[1], (0, 2)); // outer capture
        assert_eq!(caps[2], (0, 1)); // 'a'
        assert_eq!(caps[3], (1, 2)); // 'b'
    }

    #[test]
    fn test_balanced_match() {
        assert_eq!(find("(inner)", "%b()"), Some((0, 7)));
        assert_eq!(find("((nested))", "%b()"), Some((0, 10)));
        assert_eq!(find("{a{b}c}", "%b{}"), Some((0, 7)));
        assert_eq!(find("(unbalanced", "%b()"), None);
    }

    #[test]
    fn test_frontier() {
        // Match transition from non-uppercase to uppercase.
        assert_eq!(find("helloWorld", "%f[%u]"), Some((5, 5)));
        // Frontier at start of string (previous char is \0).
        assert_eq!(find("Hello", "%f[%a]"), Some((0, 0)));
    }

    #[test]
    fn test_escaped_specials() {
        assert_eq!(find("a.b", "a%.b"), Some((0, 3)));
        assert_eq!(find("a*b", "a%*b"), Some((0, 3)));
        assert_eq!(find("50%", "%d+%%"), Some((0, 3)));
    }

    #[test]
    fn test_find_at_offset() {
        assert_eq!(find_at("abcabc", "abc", 0), Some((0, 3)));
        assert_eq!(find_at("abcabc", "abc", 1), Some((3, 6)));
        assert_eq!(find_at("abcabc", "abc", 4), None);
    }

    #[test]
    fn test_gmatch() {
        let subject = b"hello world foo";
        let pattern = b"%a+";
        let results: Vec<_> = pattern_gmatch(subject, pattern, 0).collect();
        assert_eq!(results.len(), 3);
        assert_eq!(results[0].captures[0], (0, 5));
        assert_eq!(results[1].captures[0], (6, 11));
        assert_eq!(results[2].captures[0], (12, 15));
    }

    #[test]
    fn test_gmatch_empty_match() {
        // Pattern that can match empty strings shouldn't loop forever.
        let subject = b"abc";
        let pattern = b"x*";
        let results: Vec<_> = pattern_gmatch(subject, pattern, 0).collect();
        // Should get matches at each position.
        assert!(results.len() >= 3);
    }

    #[test]
    fn test_expand_replacement() {
        let ms = MatchState {
            captures: vec![(0, 5), (0, 3), (3, 5)],
        };
        let subject = b"hello";
        let result = expand_replacement(b"%2-%1", &ms, subject).unwrap();
        assert_eq!(result, b"lo-hel");
    }

    #[test]
    fn test_expand_replacement_percent_escape() {
        let ms = MatchState {
            captures: vec![(0, 5)],
        };
        let subject = b"hello";
        let result = expand_replacement(b"100%%", &ms, subject).unwrap();
        assert_eq!(result, b"100%");
    }

    #[test]
    fn test_class_in_set() {
        // %d inside a set
        assert_eq!(find("abc123", "[%d]+"), Some((3, 6)));
        assert_eq!(find("abc123", "[%a%d]+"), Some((0, 6)));
    }

    #[test]
    fn test_empty_pattern() {
        // Empty pattern matches at position 0 with zero length.
        assert_eq!(find("hello", ""), Some((0, 0)));
    }

    #[test]
    fn test_complex_pattern() {
        // Match a simple email-like pattern.
        let caps = captures("user@host.com", "(%w+)@(%w+%.%w+)");
        let caps = caps.unwrap();
        assert_eq!(caps[0], (0, 13));
        assert_eq!(caps[1], (0, 4));   // "user"
        assert_eq!(caps[2], (5, 13));  // "host.com"
    }

    #[test]
    fn test_star_greedy() {
        // `.*` is greedy: matches as much as possible.
        let caps = captures("<a><b>", "<(.*)>");
        let caps = caps.unwrap();
        // Greedy: captures "a><b"
        assert_eq!(&b"<a><b>"[caps[1].0..caps[1].1], b"a><b");
    }

    #[test]
    fn test_minus_lazy() {
        // `.-` is lazy: matches as little as possible.
        let caps = captures("<a><b>", "<(.-)>");
        let caps = caps.unwrap();
        // Lazy: captures "a"
        assert_eq!(&b"<a><b>"[caps[1].0..caps[1].1], b"a");
    }

    #[test]
    fn test_control_class() {
        assert_eq!(find("\x01\x02abc", "%c+"), Some((0, 2)));
        assert_eq!(find("abc", "%c+"), None);
    }

    #[test]
    fn test_percent_zero_full_match() {
        // %0 in replacement refers to the full match.
        let ms = MatchState {
            captures: vec![(2, 5)],
        };
        let subject = b"xxhello";
        let result = expand_replacement(b"[%0]", &ms, subject).unwrap();
        assert_eq!(result, b"[hel]");
    }

    #[test]
    fn test_anchor_only_at_start() {
        // `^` in the middle of a pattern is literal.
        assert_eq!(find("a^b", "a%^b"), Some((0, 3)));
    }

    #[test]
    fn test_set_with_range_and_class() {
        // Mix ranges and classes in a set.
        assert_eq!(find("5", "[%a0-9]"), Some((0, 1)));
        assert_eq!(find("z", "[%d%a]"), Some((0, 1)));
    }

    #[test]
    fn test_balanced_different_chars() {
        assert_eq!(find("<inner>", "%b<>"), Some((0, 7)));
        assert_eq!(find("<a<b>c>", "%b<>"), Some((0, 7)));
    }

    #[test]
    fn test_frontier_at_boundary() {
        // Frontier between digit and non-digit.
        let subject = "abc123def";
        let ms = pattern_find(subject.as_bytes(), b"%f[%d]", 0).unwrap().unwrap();
        assert_eq!(ms.captures[0], (3, 3)); // zero-width at pos 3
    }

    #[test]
    fn test_frontier_at_end_boundary() {
        // Frontier from digit back to letter.
        let subject = "123abc";
        let ms = pattern_find(subject.as_bytes(), b"%f[%a]", 0).unwrap().unwrap();
        assert_eq!(ms.captures[0], (3, 3));
    }
}
