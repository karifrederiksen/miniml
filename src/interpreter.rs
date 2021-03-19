use crate::ast;
use crate::prelude::{sym, Symbol};
use ast::{Application, Expression, Literal, Pair};
use rpds::HashTrieMap;
use std::borrow::Borrow;
use std::rc::Rc;

#[derive(Debug)]
pub struct StackFrame {
    bindings: HashTrieMap<Symbol, Expression>,
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

    pub fn next(self: Rc<Self>, bind: Symbol, value: Expression) -> Rc<Self> {
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

    pub fn get(&self, bind: &Symbol) -> Option<&Expression> {
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

macro_rules! int_operator {
    ($name: literal, $arg: expr, $f: ident) => {
        match $arg {
            Expression::Pair(Pair(l, r)) => match (*l, *r) {
                (Expression::Literal(Literal::Int(l)), Expression::Literal(Literal::Int(r))) => {
                    Expression::Literal($f(l, r))
                }
                _ => panic!("unexpected argument type"),
            },
            Expression::Literal(l) => ast::func_expr(
                sym("r"),
                ast::appl_builtin_expr(
                    sym($name),
                    ast::pair_expr(Expression::Literal(l), ast::sym_expr("r")),
                ),
            ),
            _ => panic!("unexpected argument type"),
        }
    };
}

macro_rules! literal_operator {
    ($name: literal, $arg: expr, $f: ident) => {
        match $arg {
            Expression::Pair(Pair(l, r)) => match (*l, *r) {
                (Expression::Literal(l), Expression::Literal(r)) => Expression::Literal($f(l, r)),
                _ => panic!("unexpected argument type"),
            },
            Expression::Literal(l) => ast::func_expr(
                sym("r"),
                ast::appl_builtin_expr(
                    sym($name),
                    ast::pair_expr(Expression::Literal(l), ast::sym_expr("r")),
                ),
            ),
            _ => panic!("unexpected argument type"),
        }
    };
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            stack: Stack::new(),
        }
    }

    fn enter_func(&mut self, bind: Symbol, value: Expression) {
        self.stack = self.stack.clone().next(bind, value);
    }

    fn exit_func(&mut self) {
        self.stack = self.stack.clone().previous();
    }

    fn get(&self, sym: &Symbol) -> Option<&Expression> {
        match self.stack.get(sym) {
            Some(x) => Some(x),
            None => None,
        }
    }

    pub fn eval(&mut self, expr: &Expression) -> Expression {
        match expr {
            Expression::Literal(x) => Expression::Literal(*x),
            Expression::Symbol(x) => self
                .get(x)
                .expect(&format!("symbol used before it was declared: \"{}\"", x))
                .clone(),
            Expression::IfElse(x) => {
                if self.eval(&x.expr) == Expression::Literal(Literal::Bool(true)) {
                    self.eval(&x.case_true)
                } else {
                    self.eval(&x.case_false)
                }
            }
            Expression::Pair(Pair(l, r)) => {
                let l = self.eval(&l);
                let r = self.eval(&r);
                Expression::Pair(Pair(Box::new(l), Box::new(r)))
            }
            Expression::Function(x) => Expression::Function(x.clone()),
            Expression::Application(Application::Normal { func, arg }) => {
                let e = match self.eval(&func) {
                    Expression::Function(x) => {
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
            Expression::Application(Application::Builtin { func, arg }) => match func.0.as_ref() {
                "==" => literal_operator!("==", self.eval(arg), eq),
                "*" => int_operator!("*", self.eval(arg), mul),
                "-" => int_operator!("-", self.eval(arg), sub),
                _ => panic!("undefined builtin: {}", func.0),
            },
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
