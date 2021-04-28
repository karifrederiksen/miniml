#![allow(dead_code)]
#![allow(unused_imports)]
#![feature(test)]
extern crate test;

pub mod ast;
mod interpreter;
mod parser;
pub mod prelude;
use crate::prelude::{sym, Symbol};
use interpreter as inter;
use std::collections::HashMap;

fn main() {
    let module: ast::Module = {
        let src: &str = "
type Boolean = Tr | Fa

let f x = match x with Tr -> 1, Fa -> 0

rec fact n =
    if eq n 0 then
        1
    else
        mul n (fact (sub n 1))

let main = (fact 6, f Fa)
    ";
        parser::parse_module(src).unwrap()
    };
    println!("{}\n\n", ast::print_module(&module));
    let global_ctx = {
        use inter::Value;
        let mut bindings: HashMap<Symbol, inter::Value> = HashMap::new();
        let globals = "
eq = \\l -> \\r -> builtin_eq (l, r)
add = \\l -> \\r -> builtin_add (l, r)
sub = \\l -> \\r -> builtin_sub (l, r)
mul = \\l -> \\r -> builtin_mul (l, r)
not = builtin_not
and = \\l -> \\r -> builtin_and (l, r)
or = \\l -> \\r -> builtin_or (l, r)
        "
        .trim();
        for x in globals.split("\n") {
            let kvp: Vec<&str> = x.split(" = ").collect();
            let key = sym(*kvp.get(0).unwrap());
            let val: ast::Expr = parser::parse(kvp.get(1).unwrap()).unwrap();
            let val: Value = match val {
                ast::Expr::Function(x) => Value::Function {
                    func: x,
                    context: inter::ExecutionContext::new_empty(),
                },
                ast::Expr::Symbol(x) if x.0.starts_with("builtin_") => Value::Builtin(x),
                _ => unreachable!("expected function"),
            };
            bindings.insert(key, val);
        }
        inter::ExecutionContext::new_global_ctx(bindings)
    };
    let mut interp = inter::Interpreter::new(global_ctx);
    match interp.eval_module(&module) {
        Err(e) => {
            use inter::InterpError;
            let msg = match e {
                InterpError::DepthLimitReached => "stack overflow".to_owned(),
                InterpError::TypeMismatch((expected, found)) => format!(
                    "type mismatch: expected something of type {} and found value {}",
                    expected, found
                ),
                InterpError::UndefinedSymbol(sym) => {
                    format!("symbol used before declaration: {}", sym)
                }
            };
            println!("Evaluation error: {}", msg);
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
    fn bench_stuff(b: &mut Bencher) {
        // let ast = factorial_expr(30);
        // let mut interp = interpreter::Interpreter::new();
        // b.iter(|| {
        //     black_box(interp.eval(&ast));
        // })
    }
}
