use crate::ast;
use crate::prelude::{sym, Symbol};
use std::fmt;

#[derive(Debug, Clone, Copy)]
pub enum Literal {
    Bool(bool),
    Int(i128),
}
impl Literal {
    pub fn to_ast(self) -> ast::Literal {
        match self {
            Literal::Bool(x) => ast::Literal::Bool(x),
            Literal::Int(x) => ast::Literal::Int(x),
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Bool(true) => {
                write!(f, "True")
            }
            Literal::Bool(false) => {
                write!(f, "False")
            }
            Literal::Int(x) => {
                write!(f, "{}", x)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub bind: Symbol,
    pub expr: Box<Expression>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(\\{} -> {})", self.bind, self.expr)
    }
}

#[derive(Debug, Clone)]
pub struct Pair(Box<Expression>, Box<Expression>);

impl fmt::Display for Pair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.0, self.1)
    }
}

#[derive(Debug, Clone)]
pub struct Application {
    pub func: Box<Expression>,
    pub arg: Box<Expression>,
}

impl fmt::Display for Application {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.func, self.arg)
    }
}

#[derive(Debug, Clone)]
pub struct Let {
    pub bind: Symbol,
    pub expr: Box<Expression>,
    pub next: Box<Expression>,
}

impl fmt::Display for Let {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "let {} = {} in\n{}", self.bind, self.expr, self.next)
    }
}

#[derive(Debug, Clone)]
pub enum CaseKey {
    Lit(Literal),
    Sym(Symbol),
}

impl fmt::Display for CaseKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CaseKey::Lit(x) => {
                write!(f, "{}", x)
            }
            CaseKey::Sym(x) => {
                write!(f, "{}", x)
            }
        }
    }
}

impl CaseKey {
    pub fn to_ast(self) -> ast::Expression {
        match self {
            CaseKey::Lit(x) => ast::Expression::Literal(x.to_ast()),
            CaseKey::Sym(x) => ast::Expression::Symbol(x),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Case {
    pub expr: Box<Expression>,
    pub cases: Vec<(CaseKey, Expression)>,
    pub default: Option<Box<Expression>>,
}

impl fmt::Display for Case {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "case {} of", self.expr)?;
        for (lit, expr) in self.cases.iter() {
            write!(f, "\n  {} -> {}", lit, expr)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct BinOperator {
    pub op: Symbol,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
}

impl fmt::Display for BinOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {})", self.left, self.op, self.right)
    }
}

#[derive(Debug, Clone)]
pub enum Expression {
    Symbol(Symbol),
    Literal(Literal),
    Pair(Pair),
    Function(Function),
    Application(Application),
    Let(Let),
    Case(Case),
    BinOperator(BinOperator),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Symbol(x) => {
                write!(f, "{}", x)
            }
            Expression::Literal(x) => {
                write!(f, "{}", x)
            }
            Expression::Pair(x) => {
                write!(f, "{}", x)
            }
            Expression::Function(x) => {
                write!(f, "{}", x)
            }
            Expression::Application(x) => {
                write!(f, "{}", x)
            }
            Expression::Let(x) => {
                write!(f, "{}", x)
            }
            Expression::Case(x) => {
                write!(f, "{}", x)
            }
            Expression::BinOperator(x) => {
                write!(f, "{}", x)
            }
        }
    }
}

impl Expression {
    pub fn to_ast(self) -> ast::Expression {
        match self {
            Expression::Symbol(x) => ast::Expression::Symbol(x),
            Expression::Literal(x) => ast::Expression::Literal(x.to_ast()),
            Expression::Pair(Pair(l, r)) => ast::pair_expr(l.to_ast(), r.to_ast()),
            Expression::Function(x) => ast::func_expr(x.bind, x.expr.to_ast()),
            Expression::Application(x) => ast::appl_expr(x.func.to_ast(), x.arg.to_ast()),
            Expression::Let(x) => {
                ast::appl_expr(ast::func_expr(x.bind, x.next.to_ast()), x.expr.to_ast())
            }
            Expression::BinOperator(x) => ast::appl_expr(
                ast::appl_builtin_expr(x.op, x.left.to_ast()),
                x.right.to_ast(),
            ),
            Expression::Case(x) => {
                let (last, second_last) = match x.default {
                    Some(y) => (*y, x.cases.get(x.cases.len() - 1).unwrap().clone()),
                    None => (
                        x.cases.get(x.cases.len() - 1).unwrap().clone().1,
                        x.cases.get(x.cases.len() - 2).unwrap().clone(),
                    ),
                };

                let key = x.expr.to_ast();

                let mut other_cases = ast::if_else_expr(
                    ast::appl_expr(
                        ast::appl_builtin_expr(sym("=="), key.clone()),
                        second_last.0.to_ast(),
                    ),
                    second_last.1.to_ast(),
                    last.to_ast(),
                );
                for (comp_key, expr) in x.cases.into_iter().rev().skip(2) {
                    let condition = ast::appl_expr(
                        ast::appl_builtin_expr(sym("=="), key.clone()),
                        comp_key.to_ast(),
                    );
                    other_cases = ast::if_else_expr(condition, expr.to_ast(), other_cases);
                }
                other_cases
            }
        }
    }
}
