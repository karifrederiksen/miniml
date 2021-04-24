use crate::ast;
use crate::prelude::Symbol;
use ast::{Appl, Expr, Literal, Tuple};
use rpds::HashTrieMap;
use std::borrow::Borrow;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct StackFrame {
    bindings: HashTrieMap<Symbol, Expr>,
    previous: Box<Stack>,
}

#[derive(Debug, Clone)]
pub enum Stack {
    Empty,
    Frame(StackFrame),
}

impl Stack {
    pub fn new() -> Self {
        Self::Empty
    }

    pub fn enter_frame(&mut self) {
        *self = match self {
            Self::Empty => Self::Frame(StackFrame {
                bindings: HashTrieMap::new(),
                previous: Box::new(Stack::Empty),
            }),
            Self::Frame(x) => Self::Frame(StackFrame {
                bindings: x.bindings.clone(),
                previous: Box::new(self.clone()),
            }),
        };
    }

    pub fn bind(&mut self, bind: Symbol, value: Expr) {
        *self = match self {
            Self::Empty => panic!("no frame"),
            Self::Frame(x) => Self::Frame(StackFrame {
                bindings: x.bindings.insert(bind, value),
                previous: x.previous.clone(),
            }),
        };
    }

    pub fn exit_frame(&mut self) {
        *self = match self {
            Self::Empty => panic!("no frame to exit"),
            Self::Frame(x) => *x.previous.clone(),
        };
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
    stack: Stack,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            stack: Stack::new(),
        }
    }

    fn get(&self, sym: &Symbol) -> Option<&Expr> {
        match self.stack.get(sym) {
            Some(x) => Some(x),
            None => None,
        }
    }

    fn is_builtin(sy: &Symbol) -> bool {
        sy.0.starts_with("builtin_")
    }

    fn eval_builtin_tup2(&mut self, x: &Expr) -> (Expr, Expr) {
        match self.eval(x) {
            Expr::Tuple(t) if t.exprs.len() == 2 => (
                t.exprs.get(0).unwrap().clone(),
                t.exprs.get(1).unwrap().clone(),
            ),
            _ => panic!("a"),
        }
    }
    fn eval_builtin_int_int<F, O>(&mut self, x: &Expr, f: F) -> O
    where
        F: FnOnce(i128, i128) -> O,
    {
        match self.eval_builtin_tup2(x) {
            (Expr::Literal(Literal::Int(l)), Expr::Literal(Literal::Int(r))) => f(l, r),
            (l, r) => panic!(
                "type mismatch. expected expression of type (Int, Int), found: ({}, {})",
                l, r
            ),
        }
    }
    fn eval_builtin_bool_bool<F, O>(&mut self, x: &Expr, f: F) -> O
    where
        F: FnOnce(bool, bool) -> O,
    {
        match self.eval_builtin_tup2(x) {
            (Expr::Literal(Literal::Bool(l)), Expr::Literal(Literal::Bool(r))) => f(l, r),
            (l, r) => panic!(
                "type mismatch. expected expression of type (Bool, Bool), found: ({}, {})",
                l, r
            ),
        }
    }
    fn eval_builtin_bool<F, O>(&mut self, x: &Expr, f: F) -> O
    where
        F: FnOnce(bool) -> O,
    {
        match self.eval(x) {
            Expr::Literal(Literal::Bool(x)) => f(x),
            _ => panic!(
                "type mismatch. expected expression of type Bool, found: {}",
                x
            ),
        }
    }

    fn eval_builtin(&mut self, sy: &Symbol, x: &Expr) -> Expr {
        match &sy.0[8..] {
            "eq" => self.eval_builtin_int_int(x, |l, r| Expr::Literal(Literal::Bool(l == r))),
            "add" => self.eval_builtin_int_int(x, |l, r| Expr::Literal(Literal::Int(l + r))),
            "sub" => self.eval_builtin_int_int(x, |l, r| Expr::Literal(Literal::Int(l - r))),
            "mul" => self.eval_builtin_int_int(x, |l, r| Expr::Literal(Literal::Int(l * r))),
            "div" => self.eval_builtin_int_int(x, |l, r| Expr::Literal(Literal::Int(l / r))),
            "and" => self.eval_builtin_bool_bool(x, |l, r| Expr::Literal(Literal::Bool(l && r))),
            "or" => self.eval_builtin_bool_bool(x, |l, r| Expr::Literal(Literal::Bool(l || r))),
            "not" => self.eval_builtin_bool(x, |x| Expr::Literal(Literal::Bool(!x))),
            _ => panic!("unknown builtin: {}", sy),
        }
    }

    pub fn eval(&mut self, expr: &Expr) -> Expr {
        match expr {
            Expr::Literal(x) => Expr::Literal(*x),
            Expr::Symbol(x) => {
                if Self::is_builtin(x) {
                    expr.clone()
                } else {
                    self.get(x)
                        .expect(&format!("symbol used before it was declared: \"{}\"", x))
                        .clone()
                }
            }
            Expr::IfElse(x) => {
                if self.eval(&x.expr) == Expr::Literal(Literal::Bool(true)) {
                    self.eval(&x.case_true)
                } else {
                    self.eval(&x.case_false)
                }
            }
            Expr::Function(x) => Expr::Function(x.clone()),
            Expr::Let(x) => {
                self.stack.enter_frame();
                let bind_expr = self.eval(&*x.bind_expr);
                self.stack.bind(x.bind.clone(), bind_expr);
                let value = self.eval(&*x.next_expr);
                self.stack.exit_frame();
                value
            }
            Expr::Appl(Appl { func, arg }) => {
                let func_expr = self.eval(func);
                let arg_expr = self.eval(arg);
                match &func_expr {
                    Expr::Symbol(sy) if Self::is_builtin(sy) => {
                        return self.eval_builtin(sy, &arg_expr);
                    }
                    _ => {}
                };
                match func_expr {
                    Expr::Function(x) => {
                        self.stack.enter_frame();
                        println!("binding {} with value {}", x.bind, arg_expr);
                        self.stack.bind(x.bind.clone(), arg_expr);
                        let e = self.eval(&x.expr);
                        self.stack.exit_frame();
                        println!("unbinding {}", x.bind);
                        e
                    }
                    _ => panic!("expected function, found: {}", func),
                }
            }
            Expr::Tuple(Tuple { exprs }) => {
                let exprs: Vec<Expr> = exprs.iter().map(|e| self.eval(e)).collect();
                Expr::Tuple(Tuple { exprs })
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
