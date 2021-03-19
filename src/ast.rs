use crate::prelude::{sym, Symbol};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Literal {
    Bool(bool),
    Int(i128),
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

pub fn bool_(x: bool) -> Literal {
    Literal::Bool(x)
}
pub fn bool_expr(x: bool) -> Expression {
    Expression::Literal(bool_(x))
}
pub fn integer(x: i128) -> Literal {
    Literal::Int(x)
}
pub fn integer_expr(x: i128) -> Expression {
    Expression::Literal(integer(x))
}

pub fn sym_expr<S: Into<String>>(x: S) -> Expression {
    Expression::Symbol(sym(x))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub bind: Symbol,
    pub expr: Box<Expression>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(\\{} -> {})", self.bind, self.expr)
    }
}
pub fn func(bind: Symbol, expr: Expression) -> Function {
    Function {
        bind,
        expr: Box::new(expr),
    }
}

pub fn func_expr(bind: Symbol, expr: Expression) -> Expression {
    Expression::Function(func(bind, expr))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pair(pub Box<Expression>, pub Box<Expression>);

impl fmt::Display for Pair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.0, self.1)
    }
}

pub fn pair(l: Expression, r: Expression) -> Pair {
    Pair(Box::new(l), Box::new(r))
}

pub fn pair_expr(l: Expression, r: Expression) -> Expression {
    Expression::Pair(pair(l, r))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Application {
    Normal {
        func: Box<Expression>,
        arg: Box<Expression>,
    },
    Builtin {
        func: Symbol,
        arg: Box<Expression>,
    },
}

impl fmt::Display for Application {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Normal { func, arg } => {
                write!(f, "({} {})", func, arg)?;
            }
            Self::Builtin { func, arg } => {
                write!(f, "({} {})", func, arg)?;
            }
        }
        Ok(())
    }
}

pub fn appl(f: Expression, a: Expression) -> Application {
    Application::Normal {
        func: Box::new(f),
        arg: Box::new(a),
    }
}

pub fn appl_expr(f: Expression, a: Expression) -> Expression {
    Expression::Application(appl(f, a))
}

pub fn appl_builtin(func: Symbol, arg: Expression) -> Application {
    Application::Builtin {
        func,
        arg: Box::new(arg),
    }
}

pub fn appl_builtin_expr(func: Symbol, arg: Expression) -> Expression {
    Expression::Application(appl_builtin(func, arg))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfElse {
    pub expr: Box<Expression>,
    pub case_true: Box<Expression>,
    pub case_false: Box<Expression>,
}

impl fmt::Display for IfElse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(if {} then {} else {})",
            self.expr, self.case_true, self.case_false
        )
    }
}
pub fn if_else_expr(expr: Expression, case_true: Expression, case_false: Expression) -> Expression {
    Expression::IfElse(IfElse {
        expr: Box::new(expr),
        case_true: Box::new(case_true),
        case_false: Box::new(case_false),
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression {
    Symbol(Symbol),
    Literal(Literal),
    Pair(Pair),
    Function(Function),
    Application(Application),
    IfElse(IfElse),
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
            Expression::IfElse(x) => {
                write!(f, "{}", x)
            }
        }
    }
}

pub fn pretty_print_expr(expr: &Expression) -> String {
    format!("{}", expr)
}
