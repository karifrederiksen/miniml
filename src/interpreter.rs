use crate::ast;
use crate::prelude::Symbol;
use ast::{Appl, Expr, Literal};
use rpds::HashTrieMap;
use std::borrow::Borrow;
use std::rc::Rc;

#[derive(Debug)]
pub struct StackFrame {
    bindings: HashTrieMap<Symbol, Expr>,
    previous: Rc<Stack>,
}

#[derive(Debug)]
pub enum Stack {
    Empty,
    Frame(StackFrame),
}

impl Stack {
    pub fn new() -> Rc<Self> {
        Rc::new(Self::Empty)
    }

    pub fn next(self: Rc<Self>, bind: Symbol, value: Expr) -> Rc<Self> {
        let stack = match self.borrow() {
            Self::Empty => Self::Frame(StackFrame {
                bindings: HashTrieMap::new().insert(bind, value),
                previous: self,
            }),
            Self::Frame(x) => Self::Frame(StackFrame {
                bindings: x.bindings.insert(bind, value),
                previous: self,
            }),
        };
        Rc::new(stack)
    }

    pub fn previous(self: Rc<Self>) -> Rc<Self> {
        match self.borrow() {
            Self::Empty => Rc::new(Self::Empty),
            Self::Frame(x) => x.previous.clone(),
        }
    }

    pub fn get(&self, bind: &Symbol) -> Option<&Expr> {
        match self {
            Self::Empty => None,
            Self::Frame(x) => x.bindings.get(bind),
        }
    }
}

#[derive(Debug)]
pub struct Interpreter {
    stack: Rc<Stack>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            stack: Stack::new(),
        }
    }

    fn enter_func(&mut self, bind: Symbol, value: Expr) {
        self.stack = self.stack.clone().next(bind, value);
    }

    fn exit_func(&mut self) {
        self.stack = self.stack.clone().previous();
    }

    fn get(&self, sym: &Symbol) -> Option<&Expr> {
        match self.stack.get(sym) {
            Some(x) => Some(x),
            None => None,
        }
    }

    pub fn eval(&mut self, expr: &Expr) -> Expr {
        match expr {
            Expr::Literal(x) => Expr::Literal(*x),
            Expr::Symbol(x) => {
                if ["eq", "sub", "mul"].contains(&x.0.as_ref()) {
                    todo!("handle built-in - might need to change the ast")
                }
                self.get(x)
                    .expect(&format!("symbol used before it was declared: \"{}\"", x))
                    .clone()
            }
            Expr::IfElse(x) => {
                if self.eval(&x.expr) == Expr::Literal(Literal::Bool(true)) {
                    self.eval(&x.case_true)
                } else {
                    self.eval(&x.case_false)
                }
            }
            Expr::Function(x) => Expr::Function(x.clone()),
            Expr::Let(_) => todo!(),
            Expr::Appl(Appl { func, arg }) => {
                let e = match self.eval(&func) {
                    Expr::Function(x) => {
                        let arg = self.eval(&arg);
                        self.enter_func(x.bind, arg);
                        let e = self.eval(&x.expr);
                        self.exit_func();
                        e
                    }
                    _ => panic!("expected function, found: {}", func),
                };
                return e;
            }
        }
    }
}

#[inline]
fn eq(l: Literal, r: Literal) -> Literal {
    return Literal::Bool(l == r);
}
#[inline]
fn sub(l: i128, r: i128) -> Literal {
    return Literal::Int(l - r);
}
#[inline]
fn mul(l: i128, r: i128) -> Literal {
    return Literal::Int(l * r);
}
