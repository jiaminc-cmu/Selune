# Sel-ne-A-modern-lua-JIT-in-rust-
Project: Selûne
A modern Lua JIT in Rust
🎯 Project Mission
Ranked by priority:
1. Lua 5.4 Compliance: Complete and accurate support for modern Lua 5.4 semantics, explicitly solving the dual integer/float number system challenge.
2. Extreme Performance: Achieving execution speeds that rival or surpass existing JIT implementations through aggressive, low-level engine optimizations.
3. Cross-Platform Compatibility: Seamless execution across major architectures, starting with robust support for x86_64 (Linux/Windows) and ARM64 (Apple Silicon).
🛠️ Tech Stack & Architecture
• Core Language: Rust (leveraging zero-cost abstractions, with targeted use of unsafe for performance-critical VM internals).
• Memory Model: Tagged Pointers (packing values and type information into a single 8-byte/64-bit word to maximize CPU L1/L2 cache locality).
• Frontend: No-AST / Single-Pass Compiler (parsing directly from lexical tokens to bytecode to ensure minimal heap allocation and lightning-fast load times).
• JIT Backend: Cranelift (utilizing its fast compilation times and robust Intermediate Representation to generate highly optimized machine code).
