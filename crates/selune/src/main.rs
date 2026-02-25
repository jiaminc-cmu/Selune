use std::cell::RefCell;
use std::io::Read;

use selune_compiler::compiler;
use selune_jit::JitCompiler;
use selune_vm::vm::Vm;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let mut script_file: Option<String> = None;
    let mut exec_statements: Vec<String> = Vec::new();
    let mut load_modules: Vec<String> = Vec::new();
    let mut interactive = false;
    let mut show_version = false;
    let mut warn_on = false;
    let mut script_args: Vec<String> = Vec::new();
    let mut saw_dashdash = false;

    // Parse arguments
    let mut i = 1;
    while i < args.len() {
        if saw_dashdash {
            script_args.push(args[i].clone());
            i += 1;
            continue;
        }
        match args[i].as_str() {
            "--" => {
                saw_dashdash = true;
                i += 1;
            }
            "-v" => {
                show_version = true;
                i += 1;
            }
            "-i" => {
                interactive = true;
                i += 1;
            }
            "-W" => {
                warn_on = true;
                i += 1;
            }
            "-e" => {
                if i + 1 >= args.len() {
                    eprintln!("selune: '-e' needs argument");
                    std::process::exit(1);
                }
                exec_statements.push(args[i + 1].clone());
                i += 2;
            }
            "-l" => {
                if i + 1 >= args.len() {
                    eprintln!("selune: '-l' needs argument");
                    std::process::exit(1);
                }
                load_modules.push(args[i + 1].clone());
                i += 2;
            }
            _ => {
                if args[i].starts_with('-') && args[i] != "-" {
                    // Check for combined forms like -e"code"
                    if args[i].starts_with("-e") && args[i].len() > 2 {
                        exec_statements.push(args[i][2..].to_string());
                        i += 1;
                    } else if args[i].starts_with("-l") && args[i].len() > 2 {
                        load_modules.push(args[i][2..].to_string());
                        i += 1;
                    } else {
                        eprintln!("selune: unrecognized option '{}'", args[i]);
                        std::process::exit(1);
                    }
                } else {
                    // Script file
                    script_file = Some(args[i].clone());
                    // Everything after script file is script args
                    script_args = args[i + 1..].to_vec();
                    break;
                }
            }
        }
    }

    if show_version {
        println!("Selune 0.1.0 -- Lua 5.4 (compatible)");
    }

    // If no script and no -e, and stdin is a terminal, go interactive
    let stdin_is_tty = atty_check();
    let go_interactive = interactive
        || (script_file.is_none() && exec_statements.is_empty() && stdin_is_tty && !show_version);

    // Execute -l modules and -e statements
    if !load_modules.is_empty() || !exec_statements.is_empty() || script_file.is_some() {
        let mut vm = create_vm(warn_on, &script_file, &script_args);

        // -l modules
        for modname in &load_modules {
            let code = format!("require(\"{}\")", modname);
            let chunk_name = format!("=(require '{}')", modname);
            if let Err(e) = run_string(&mut vm, &code, &chunk_name, modname) {
                eprintln!("selune: {}", e);
                std::process::exit(1);
            }
        }

        // -e statements
        for stat in &exec_statements {
            if let Err(e) = run_string(&mut vm, stat, "=(command line)", "") {
                eprintln!("selune: {}", e);
                std::process::exit(1);
            }
        }

        // Script file
        if let Some(ref path) = script_file {
            if path == "-" {
                // Read from stdin
                let mut buf = Vec::new();
                if let Err(e) = std::io::stdin().read_to_end(&mut buf) {
                    eprintln!("selune: cannot read stdin: {}", e);
                    std::process::exit(1);
                }
                if let Err(e) = run_bytes(&mut vm, &buf, "=stdin") {
                    eprintln!("selune: {}", e);
                    std::process::exit(1);
                }
            } else {
                let source = match std::fs::read(path) {
                    Ok(data) => data,
                    Err(e) => {
                        eprintln!("selune: cannot open {}: {}", path, e);
                        std::process::exit(1);
                    }
                };
                // Strip shebang line if present
                let source = strip_shebang(&source);
                if let Err(e) = run_bytes(&mut vm, source, &format!("@{}", path)) {
                    eprintln!("selune: {}", e);
                    std::process::exit(1);
                }
            }
        }

        // If -i was given, enter interactive mode after running script
        if go_interactive && (script_file.is_some() || !exec_statements.is_empty()) {
            run_repl(vm);
        }
    } else if !stdin_is_tty && !show_version {
        // Read from stdin (piped input)
        let mut vm = create_vm(warn_on, &None, &[]);
        let mut buf = Vec::new();
        if let Err(e) = std::io::stdin().read_to_end(&mut buf) {
            eprintln!("selune: cannot read stdin: {}", e);
            std::process::exit(1);
        }
        if let Err(e) = run_bytes(&mut vm, &buf, "=stdin") {
            eprintln!("selune: {}", e);
            std::process::exit(1);
        }
    } else if go_interactive {
        // Interactive REPL
        if !show_version {
            println!("Selune 0.1.0 -- Lua 5.4 (compatible)");
        }
        let vm = create_vm(warn_on, &None, &[]);
        run_repl(vm);
    }
}

thread_local! {
    static JIT_COMPILER: RefCell<Option<JitCompiler>> = RefCell::new(None);
}

fn jit_compile_hook(vm: &mut Vm, proto_idx: usize) {
    JIT_COMPILER.with(|cell| {
        let mut opt = cell.borrow_mut();
        if opt.is_none() {
            *opt = JitCompiler::new().ok();
        }
        if let Some(jit) = opt.as_mut() {
            match jit.compile_proto(&vm.protos[proto_idx], &mut vm.gc, proto_idx) {
                Ok(jit_fn) => {
                    vm.jit_functions.insert(proto_idx, jit_fn);
                }
                Err(_e) => {}
            }
        }
    });
}

fn create_vm(warn_on: bool, script_file: &Option<String>, script_args: &[String]) -> Vm {
    // We need to use the VM's execute method which initializes everything.
    // Create a dummy proto to initialize the VM, then we can use load_chunk for subsequent code.
    let source = b"";
    let (proto, strings) = compiler::compile(source, "=(init)").unwrap();
    let mut vm = Vm::new();
    // Execute the empty proto to initialize stdlib
    let _ = vm.execute(&proto, strings);

    // Enable JIT compilation
    vm.jit_enabled = true;
    vm.jit_threshold = 1000;
    vm.jit_compile_callback = Some(jit_compile_hook);

    if warn_on {
        vm.warn_enabled = true;
    }

    // Set up `arg` table
    if let Some(env_idx) = vm.env_idx {
        let arg_table = vm.gc.alloc_table(8, 4);

        // arg[0] = script name (or empty)
        if let Some(ref path) = script_file {
            let sid = vm.strings.intern_or_create(path.as_bytes());
            vm.gc
                .get_table_mut(arg_table)
                .raw_seti(0, selune_core::value::TValue::from_string_id(sid));
        }

        // arg[1..] = script arguments
        for (j, a) in script_args.iter().enumerate() {
            let sid = vm.strings.intern_or_create(a.as_bytes());
            vm.gc.get_table_mut(arg_table).raw_seti(
                (j + 1) as i64,
                selune_core::value::TValue::from_string_id(sid),
            );
        }

        // arg[-1] = program name
        let prog_sid = vm.strings.intern_or_create(b"selune");
        vm.gc
            .get_table_mut(arg_table)
            .raw_seti(-1, selune_core::value::TValue::from_string_id(prog_sid));

        let arg_key = vm.strings.intern(b"arg");
        vm.gc
            .get_table_mut(env_idx)
            .raw_set_str(arg_key, selune_core::value::TValue::from_table(arg_table));
    }

    vm
}

fn run_string(vm: &mut Vm, source: &str, name: &str, _modname: &str) -> Result<(), String> {
    run_bytes(vm, source.as_bytes(), name)
}

fn run_bytes(vm: &mut Vm, source: &[u8], name: &str) -> Result<(), String> {
    let closure_val = vm.load_chunk(source, name, None)?;
    match selune_vm::dispatch::call_function(vm, closure_val, &[]) {
        Ok(_results) => Ok(()),
        Err(e) => Err(format!("{}", e)),
    }
}

fn strip_shebang(source: &[u8]) -> &[u8] {
    if source.starts_with(b"#") {
        // Skip to end of first line
        if let Some(pos) = source.iter().position(|&b| b == b'\n') {
            &source[pos + 1..]
        } else {
            b""
        }
    } else {
        source
    }
}

fn run_repl(mut vm: Vm) {
    let config = rustyline::config::Config::builder()
        .auto_add_history(true)
        .build();

    let mut rl = match rustyline::DefaultEditor::with_config(config) {
        Ok(rl) => rl,
        Err(e) => {
            eprintln!("selune: cannot initialize REPL: {}", e);
            return;
        }
    };

    loop {
        let readline = rl.readline("> ");
        match readline {
            Ok(line) => {
                let line = line.trim().to_string();
                if line.is_empty() {
                    continue;
                }

                // Try as expression first (prepend "return ")
                let try_expr = format!("return {}", line);
                let result = try_compile_and_run(&mut vm, &try_expr, "=stdin");

                match result {
                    Ok(Some(output)) => {
                        if !output.is_empty() {
                            println!("{}", output);
                        }
                    }
                    Ok(None) => {}
                    Err(_) => {
                        // Try as statement
                        let mut full_line = line.clone();
                        loop {
                            match try_compile_and_run(&mut vm, &full_line, "=stdin") {
                                Ok(Some(output)) => {
                                    if !output.is_empty() {
                                        println!("{}", output);
                                    }
                                    break;
                                }
                                Ok(None) => break,
                                Err(e) => {
                                    // Check if this is a "near <eof>" error (incomplete input)
                                    if e.contains("<eof>") || e.contains("unexpected end") {
                                        // Read continuation line
                                        match rl.readline(">> ") {
                                            Ok(cont) => {
                                                full_line.push('\n');
                                                full_line.push_str(&cont);
                                            }
                                            Err(_) => {
                                                eprintln!("{}", e);
                                                break;
                                            }
                                        }
                                    } else {
                                        eprintln!("{}", e);
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Err(rustyline::error::ReadlineError::Interrupted) => {
                // Ctrl-C
                continue;
            }
            Err(rustyline::error::ReadlineError::Eof) => {
                // Ctrl-D
                break;
            }
            Err(e) => {
                eprintln!("selune: readline error: {}", e);
                break;
            }
        }
    }
}

/// Try to compile and run code. Returns Ok(Some(output)) if it produced output,
/// Ok(None) if it ran without output, or Err if it failed to compile/run.
fn try_compile_and_run(vm: &mut Vm, source: &str, name: &str) -> Result<Option<String>, String> {
    let closure_val = vm.load_chunk(source.as_bytes(), name, None)?;

    match selune_vm::dispatch::call_function(vm, closure_val, &[]) {
        Ok(results) => {
            if results.is_empty() {
                Ok(None)
            } else {
                let parts: Vec<String> = results
                    .iter()
                    .map(|v| format_value(*v, &vm.gc, &vm.strings))
                    .collect();
                Ok(Some(parts.join("\t")))
            }
        }
        Err(e) => Err(format!("{}", e)),
    }
}

fn format_value(
    val: selune_core::value::TValue,
    gc: &selune_core::gc::GcHeap,
    strings: &selune_core::string::StringInterner,
) -> String {
    if val.is_nil() {
        "nil".to_string()
    } else if let Some(b) = val.as_bool() {
        if b {
            "true".to_string()
        } else {
            "false".to_string()
        }
    } else if let Some(i) = val.as_integer() {
        format!("{}", i)
    } else if let Some(i) = val.as_full_integer(gc) {
        format!("{}", i)
    } else if let Some(f) = val.as_float() {
        if f == f.floor() && f.is_finite() && f.abs() < 1e15 {
            format!("{:.1}", f)
        } else {
            format!("{:.14e}", f)
        }
    } else if let Some(sid) = val.as_string_id() {
        String::from_utf8_lossy(strings.get_bytes(sid)).into_owned()
    } else if let Some(idx) = val.as_table_idx() {
        format!("table: 0x{:x}", idx.index())
    } else if let Some(idx) = val.as_closure_idx() {
        format!("function: 0x{:x}", idx.index())
    } else if let Some(idx) = val.as_native_idx() {
        format!("function: 0x{:x}", idx.index())
    } else if let Some(idx) = val.as_userdata_idx() {
        format!("userdata: 0x{:x}", idx.index())
    } else {
        "unknown".to_string()
    }
}

/// Check if stdin is connected to a terminal.
fn atty_check() -> bool {
    #[cfg(unix)]
    {
        extern "C" {
            fn isatty(fd: i32) -> i32;
        }
        unsafe { isatty(0) != 0 }
    }
    #[cfg(not(unix))]
    {
        true
    }
}
