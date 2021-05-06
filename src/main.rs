#![allow(dead_code)]
#![allow(unused_imports)]

use interpreter as inter;
use prelude::{sym, Symbol};
use std::collections::HashMap;
use type_recon as trc;

fn main() {
    let mut module: ast::Module = {
        let prelude: &str = include_str!("./prelude.src");
        let src: &str = include_str!("./program.src");
        parser::parse_module(&format!("{}\n{}", prelude, src)).unwrap()
    };
    let global_ctx = inter::ExecutionContext::new_empty();
    {
        use trc::Error;
        let mut ctx = trc::SymbolTypeContext::new();
        ctx.add_prelude();
        match ctx.annotate(&mut module) {
            Ok(()) => {}
            Err(Error::TupleArityMismatch) => println!("arity mismatch"),
            Err(Error::TypeMismatch((t1, t2))) => {
                println!("type mismatch between {:?} and {:?}", t1, t2)
            }
            Err(Error::NonExhaustiveMatch) => {
                println!("non-exhaustive match detected")
            }
        };
    }
    println!("{}\n\n", ast::print_module(&module));
    let mut interp = inter::Interpreter::new(global_ctx);
    match interp.eval_module(&module) {
        Err(e) => {
            use inter::{Error, ErrorKind};
            let msg = match &e.kind {
                ErrorKind::DepthLimitReached => "stack overflow".to_owned(),
                ErrorKind::TypeMismatch((expected, found)) => format!(
                    "type mismatch: expected something of type {:?} and found value {:?}",
                    expected, found
                ),
                ErrorKind::UndefinedSymbol(sym) => {
                    format!("symbol used before declaration: {:?}", sym)
                }
            };
            println!("Evaluation error: {}", msg);
            for x in e.stack {
                println!("  {:?}", x);
            }
            return;
        }
        Ok(()) => {}
    };
    match interp.current_ctx().find(&Symbol("main".to_owned())) {
        Some(main) => {
            println!("{:?}\n\n", main);
        }
        None => {
            println!("no main found\n\n");
        }
    };
}
