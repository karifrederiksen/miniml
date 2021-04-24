#![feature(test)]
extern crate test;

pub mod ast;
mod interpreter;
mod parser;
pub mod prelude;

fn factorial_expr(n: i32) -> ast::Expr {
    let src: String = format!(
        "
let fact =
    fn b ->
        if eq n 0 then
            1
        else
            mul n (fact (sub n 1))
in
fact {}
    ",
        n
    );
    let src: &str = &src;
    parser::parse(src).unwrap()
}

fn main() {
    let ast: ast::Expr = factorial_expr(30);
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
        let ast = factorial_expr(30);
        let mut interp = interpreter::Interpreter::new();
        b.iter(|| {
            black_box(interp.eval(&ast));
        })
    }
}
