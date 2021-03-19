#![feature(test)]
extern crate test;

pub mod ast;
pub mod cst;
mod interpreter;
pub mod prelude;
use prelude::sym;

fn factorial_expr(n: i128) -> cst::Expression {
    use cst::*;
    // let fact = \n -> if n == 0 then 1 else n * (fact (n - 1))
    Expression::Let(Let {
        bind: sym("fact"),
        expr: Box::new(Expression::Function(Function {
            bind: sym("n"),
            expr: Box::new(Expression::Case(Case {
                expr: Box::new(Expression::BinOperator(BinOperator {
                    op: sym("=="),
                    left: Box::new(Expression::Symbol(sym("n"))),
                    right: Box::new(Expression::Literal(Literal::Int(0))),
                })),
                cases: vec![
                    (
                        CaseKey::Lit(Literal::Bool(true)),
                        Expression::Literal(Literal::Int(1)),
                    ),
                    (
                        CaseKey::Lit(Literal::Bool(false)),
                        Expression::BinOperator(BinOperator {
                            op: sym("*"),
                            left: Box::new(Expression::Symbol(sym("n"))),
                            right: Box::new(Expression::Application(Application {
                                func: Box::new(Expression::Symbol(sym("fact"))),
                                arg: Box::new(Expression::BinOperator(BinOperator {
                                    op: sym("-"),
                                    left: Box::new(Expression::Symbol(sym("n"))),
                                    right: Box::new(Expression::Literal(Literal::Int(1))),
                                })),
                            })),
                        }),
                    ),
                ],
                default: None,
            })),
        })),
        next: Box::new(Expression::Application(Application {
            func: Box::new(Expression::Symbol(sym("fact"))),
            arg: Box::new(Expression::Literal(Literal::Int(n))),
        })),
    })
}

fn main() {
    // let fact = \n -> if n == 0 then 1 else n * (fact (n - 1))
    let expr: cst::Expression = factorial_expr(30);
    println!("\n\n");
    println!("{}\n\n", &expr);
    let ast = expr.to_ast();
    println!("{}\n\n", ast);

    let mut interp = interpreter::Interpreter::new();
    println!("{}\n\n", interp.eval(&ast));
}

#[cfg(test)]
mod tests {
    use super::factorial_expr;
    use crate::interpreter;
    use test::{black_box, Bencher};

    #[bench]
    fn bench_stuff(b: &mut Bencher) {
        let ast = factorial_expr(30).to_ast();
        let mut interp = interpreter::Interpreter::new();
        b.iter(|| {
            black_box(interp.eval(&ast));
        })
    }
}
