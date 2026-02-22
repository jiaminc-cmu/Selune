use selune_compiler::compiler::compile;

fn compile_file(path: &str) {
    let content = std::fs::read(path).unwrap_or_else(|e| {
        panic!("failed to read {path}: {e}");
    });
    compile(&content, path).unwrap_or_else(|e| {
        panic!("failed to compile {path}: {e}");
    });
}

fn samples_dir() -> String {
    let manifest = env!("CARGO_MANIFEST_DIR");
    format!("{manifest}/../../tests/lua_samples")
}

#[test]
fn e2e_sample_fibonacci() {
    compile_file(&format!("{}/fibonacci.lua", samples_dir()));
}

#[test]
fn e2e_sample_factorial() {
    compile_file(&format!("{}/factorial.lua", samples_dir()));
}

#[test]
fn e2e_sample_closures() {
    compile_file(&format!("{}/closures.lua", samples_dir()));
}

#[test]
fn e2e_sample_tables() {
    compile_file(&format!("{}/tables.lua", samples_dir()));
}

#[test]
fn e2e_sample_control_flow() {
    compile_file(&format!("{}/control_flow.lua", samples_dir()));
}

#[test]
fn e2e_sample_sieve() {
    compile_file(&format!("{}/sieve.lua", samples_dir()));
}

#[test]
fn e2e_sample_varargs() {
    compile_file(&format!("{}/varargs.lua", samples_dir()));
}

#[test]
fn e2e_sample_goto() {
    compile_file(&format!("{}/goto.lua", samples_dir()));
}

#[test]
fn e2e_sample_attributes() {
    compile_file(&format!("{}/attributes.lua", samples_dir()));
}

#[test]
fn e2e_sample_comprehensive() {
    compile_file(&format!("{}/comprehensive.lua", samples_dir()));
}
