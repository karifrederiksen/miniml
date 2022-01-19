#![allow(dead_code)]
#![allow(unused_imports)]

use ast::{print_module, print_type};
use io::prelude::*;
use prelude::{sym, Symbol};
use std::collections::HashMap;
use std::fs;
use std::io;
use std::process::{Command, ExitStatus};
use type_recon as trc;

fn main() {
    let mut module: ast::Module = {
        let prelude: &str = include_str!("./prelude");
        let src: &str = include_str!("./program");
        parser::parse_module(&format!("{}\n{}", prelude, src)).unwrap()
    };
    println!("===== FULL PROGRAM =====:\n{}\n", print_module(&module));
    {
        use trc::Error;
        let mut ctx = trc::SymbolTypeContext::new();
        ctx.add_prelude();
        match ctx.annotate(&mut module) {
            Ok(()) => {}
            Err(Error::TupleArityMismatch) => println!("arity mismatch"),
            Err(Error::TypeMismatch((t1, t2))) => {
                println!(
                    "type mismatch between {} and {}",
                    print_type(&t1),
                    print_type(&t2)
                )
            }
            Err(Error::NonExhaustiveMatch) => {
                println!("non-exhaustive match detected")
            }
        };
    }
    let module_str = format!("{}", ast::print_module(&module));

    fs::create_dir("output").unwrap_or(());
    fs::File::create("output/module")
        .unwrap()
        .write_all(module_str.as_bytes())
        .unwrap();

    let mut js_code = js_backend::generate(&module);
    js_code.push_str("console.log(main);\n");

    fs::File::create("output/output.js")
        .unwrap()
        .write_all(js_code.as_bytes())
        .unwrap();

    let output = Command::new("node")
        .arg("output/output.js")
        .output()
        .expect("failed to execute process");
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    if output.status.success() {
        println!("{}", stdout);
    } else {
        println!("ERROR:\n\n");
        println!("stdout:\n{}", stdout);
        println!("stderr:\n{}", stderr);
    }
}
