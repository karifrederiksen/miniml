#![allow(dead_code)]
#![allow(unused_imports)]
#![feature(test)]
extern crate test;

pub mod ast;
mod interpreter;
mod parser;
pub mod prelude;
use crate::prelude::{sym, Symbol};
use std::collections::HashMap;

fn factorial_expr(n: i32) -> ast::Module {
    let src: String = format!(
        "

let apply (f, x) = f x

rec fact n =
    if eq n 0 then
        1
    else
        mul n (fact (sub n 1))

let main = (fact {}, True)
    ",
        n
    );
    let src: &str = &src;
    parser::parse_module(src).unwrap()
}

fn main() {
    let module: ast::Module = factorial_expr(6);
    println!("{}\n\n", ast::print_module(&module));
    let global_ctx = {
        use interpreter::Value;
        let mut bindings: HashMap<Symbol, interpreter::Value> = HashMap::new();
        let globals = "
eq = \\l -> \\r -> builtin_eq (l, r)
add = \\l -> \\r -> builtin_add (l, r)
sub = \\l -> \\r -> builtin_sub (l, r)
mul = \\l -> \\r -> builtin_mul (l, r)
        "
        .trim();
        for x in globals.split("\n") {
            let kvp: Vec<&str> = x.split(" = ").collect();
            let key = sym(*kvp.get(0).unwrap());
            let val: ast::Expr = parser::parse(kvp.get(1).unwrap()).unwrap();
            let val: Value = match val {
                ast::Expr::Function(x) => Value::Function {
                    func: x,
                    context: interpreter::ExecutionContext::new_empty(),
                },
                _ => panic!("expected function"),
            };
            bindings.insert(key, val);
        }
        interpreter::ExecutionContext::new_global_ctx(bindings)
    };
    let mut interp = interpreter::Interpreter::new(global_ctx);
    interp.eval_module(&module);
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
    use super::factorial_expr;
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
