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
    let mut gen = ast::VariableTypeGenerator::new();
    let module: ast::Module = {
        let src: &str = "
type Option a = Some a | None

let map f = \\x -> match x with
    Some x -> Some (f x),
    None -> None

rec fact n =
    if eq n 0 then
        1
    else
        mul n (fact (sub n 1))

let x = Some 1

let incr = add 1

let incr_opt = map incr

let main = (fact 6, incr_opt x)
";
        parser::parse_module(&format!("{}\n{}", PRELUDE, src)).unwrap()
    };
    println!("{}\n\n", ast::print_module(&module));
    let global_ctx = inter::ExecutionContext::new_empty();
    {
        use trc::Error as TCError;
        let mut ctx = trc::SymbolTypeContext::new();
        ctx.add_prelude(&mut gen);
        for st in &module.statements {
            match st {
                Statement::Let(st) => {
                    if st.recursive {
                        ctx.add_global_symbol(st.bind.clone(), gen.next_scheme());
                    }
                    match ctx.infer(&mut gen, &st.expr) {
                        Ok(t) => {
                            let t = t.generalize(&mut gen);
                            ctx.add_global_symbol(st.bind.clone(), t.clone());
                            println!("{}: {}", st.bind, t);
                        }
                        Err(TCError::TupleArityMismatch) => println!("{}: arity mismatch", st.bind),
                        Err(TCError::TypeMismatch((t1, t2))) => {
                            println!("{}: type mismatch between {} and {}", st.bind, t1, t2)
                        }
                    }
                }
                Statement::Type(t) => {
                    use ast::{CustomType, FunctionType, Type, TypeScheme};
                    let ty = Type::Custom(t.type_.clone()).generalize(&mut gen);
                    for v in &t.variants {
                        let ty = match &v.contained_type {
                            None => ty.clone(),
                            Some(contained_type) => TypeScheme {
                                type_: Type::Func(Box::new(FunctionType {
                                    arg: contained_type.clone(),
                                    return_: ty.type_.clone(),
                                })),
                                variables: ty.variables.clone(),
                            },
                        };
                        println!("{}: {}", v.constr, ty);
                        ctx.add_global_symbol(v.constr.clone(), ty);
                    }
                }
            }
        }
    }
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
    fn bench_stuff(_b: &mut Bencher) {
        // let ast = factorial_expr(30);
        // let mut interp = interpreter::Interpreter::new();
        // b.iter(|| {
        //     black_box(interp.eval(&ast));
        // })
    }
}
