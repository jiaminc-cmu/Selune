#![no_main]

use libfuzzer_sys::fuzz_target;
use selune_compiler::compiler::compile;

fuzz_target!(|data: &[u8]| {
    // The compiler must never panic on any input — errors are fine, panics are bugs.
    let _ = compile(data, "fuzz");
});
