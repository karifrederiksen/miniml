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
            Self::Bool(true) => {
                write!(f, "True")
            }
            Self::Bool(false) => {
                write!(f, "False")
            }
            Self::Int(x) => {
                write!(f, "{}", x)
            }
        }
    }
}

pub fn bool_(x: bool) -> Literal {
    Literal::Bool(x)
}
pub fn bool_expr(x: bool) -> Expr {
    Expr::Literal(bool_(x))
}
pub fn integer(x: i128) -> Literal {
    Literal::Int(x)
}
pub fn integer_expr(x: i128) -> Expr {
    Expr::Literal(integer(x))
}

pub fn sym_expr<S: Into<String>>(x: S) -> Expr {
    Expr::Symbol(sym(x))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub bind: Symbol,
    pub expr: Box<Expr>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(\\{} -> {})", self.bind, self.expr)
    }
}
pub fn func(bind: Symbol, expr: Expr) -> Function {
    Function {
        bind,
        expr: Box::new(expr),
    }
}

pub fn func_expr(bind: Symbol, expr: Expr) -> Expr {
    Expr::Function(func(bind, expr))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Let {
    pub bind: Symbol,
    pub bind_expr: Box<Expr>,
    pub next_expr: Box<Expr>,
}

impl fmt::Display for Let {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "let {} = {} in {}",
            self.bind, self.bind_expr, self.next_expr
        )?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Appl {
    pub func: Box<Expr>,
    pub arg: Box<Expr>,
}

impl fmt::Display for Appl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.func, self.arg)?;
        Ok(())
    }
}

pub fn appl(f: Expr, a: Expr) -> Appl {
    Appl {
        func: Box::new(f),
        arg: Box::new(a),
    }
}

pub fn appl_expr(f: Expr, a: Expr) -> Expr {
    Expr::Appl(appl(f, a))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfElse {
    pub expr: Box<Expr>,
    pub case_true: Box<Expr>,
    pub case_false: Box<Expr>,
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
pub fn if_else_expr(expr: Expr, case_true: Expr, case_false: Expr) -> Expr {
    Expr::IfElse(IfElse {
        expr: Box::new(expr),
        case_true: Box::new(case_true),
        case_false: Box::new(case_false),
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tuple {
    pub exprs: Vec<Expr>,
}
impl fmt::Display for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for e in self.exprs.iter().take(1) {
            write!(f, "{}", e)?;
        }
        for e in self.exprs.iter().skip(1) {
            write!(f, ", {}", e)?;
        }
        write!(f, ")")
    }
}
pub fn tuple_expr(exprs: Vec<Expr>) -> Expr {
    Expr::Tuple(Tuple { exprs })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Symbol(Symbol),
    Literal(Literal),
    Function(Function),
    Let(Let),
    Appl(Appl),
    IfElse(IfElse),
    Tuple(Tuple),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Symbol(x) => {
                write!(f, "{}", x)
            }
            Self::Literal(x) => {
                write!(f, "{}", x)
            }
            Self::Function(x) => {
                write!(f, "{}", x)
            }
            Self::Let(x) => {
                write!(f, "{}", x)
            }
            Self::Appl(x) => {
                write!(f, "{}", x)
            }
            Self::IfElse(x) => {
                write!(f, "{}", x)
            }
            Self::Tuple(x) => {
                write!(f, "{}", x)
            }
        }
    }
}

pub fn pretty_print_expr(expr: &Expr) -> String {
    format!("{}", expr)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BasicType {
    Bool,
    Int,
}

impl fmt::Display for BasicType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => {
                write!(f, "Bool")
            }
            Self::Int => {
                write!(f, "Int")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionType {
    pub arg: Type,
    pub return_: Type,
}

impl fmt::Display for FunctionType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.arg, self.return_)
    }
}

fn u32_to_ascii(n: u32) -> String {
    let mut s = String::new();
    let mut n = n;
    while n > 0 {
        let c = (96 + (n % 26)) as u8;
        s.push(c as char);
        n = n / 26;
    }
    s
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct VariableType(u32);

impl fmt::Display for VariableType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", u32_to_ascii(self.0))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    Basic(BasicType),
    Func(Box<FunctionType>),
    Var(VariableType),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Basic(x) => write!(f, "{}", x),
            Self::Func(x) => write!(f, "{}", x),
            Self::Var(x) => write!(f, "{}", x),
        }
    }
}
