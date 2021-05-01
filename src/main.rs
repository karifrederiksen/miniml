#![allow(dead_code)]
#![allow(unused_imports)]
#![feature(test)]
extern crate test;

pub mod ast;
mod interpreter;
mod parser;
pub mod prelude;
mod type_recon;
use crate::prelude::{sym, Symbol};
use ast::Statement;
use interpreter as inter;
use std::collections::HashMap;
use type_recon as trc;

static PRELUDE: &'static str = "
let eq l = \\r -> intrinsic_eq (l, r)
let add l = \\r -> intrinsic_add (l, r)
let sub l = \\r -> intrinsic_sub (l, r)
let mul l = \\r -> intrinsic_mul (l, r)
let not = intrinsic_not
let and l = \\r -> intrinsic_and (l, r)
let or l = \\r -> intrinsic_or (l, r)
";

fn main() {
    let mut module: ast::Module = {
        let src: &str = "
type Option a = Some a | None

let map f = \\x -> match x with
    Some y -> Some (f y),
    None -> None

rec fact n =
    if eq n 0 then
        1
    else
        mul n (fact (sub n 1))

let x = Some 1

let incr : Int -> Int
let incr = add 1

let incr_opt = map incr

let main = (fact 6, incr_opt x)
";
        parser::parse_module(&format!("{}\n{}", PRELUDE, src)).unwrap()
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
                println!("type mismatch between {} and {}", t1, t2)
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
                    "type mismatch: expected something of type {} and found value {}",
                    expected, found
                ),
                ErrorKind::UndefinedSymbol(sym) => {
                    format!("symbol used before declaration: {}", sym)
                }
            };
            println!("Evaluation error: {}", msg);
            for x in e.stack {
                println!("  {}", x);
            }
            return;
        }
        Ok(()) => {}
    };
    match interp.current_ctx().find(&Symbol("main".to_owned())) {
        Some(main) => {
            println!("{}\n\n", main);
        }
        None => {
            println!("no main found\n\n");
        }
    };
}

#[cfg(test)]
mod tests {
    use crate::interpreter;
    use test::{black_box, Bencher};

    #[bench]
    fn bench_stuff(_b: &mut Bencher) {
        // let ast = factorial_expr(30);
        // let mut interp = interpreter::Interpreter::new();
        // b.iter(|| {
        //     black_box(interp.eval(&ast));
        // })
    }
}
