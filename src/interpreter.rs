use crate::ast;
use crate::prelude::Symbol;
use ast::{Appl, Expr, Literal};
use rpds::HashTrieMap;
use std::borrow::Borrow;
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum Value {
    Literal(Literal),
    Tuple(Vec<Value>),
    Function {
        func: ast::Function,
        bindings: HashTrieMap<Symbol, Value>,
    },
    Builtin(Symbol),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(x) => {
                write!(f, "{}", x)
            }
            Self::Tuple(xs) => {
                write!(f, "(")?;
                for x in xs.iter().take(1) {
                    write!(f, "{}", x)?;
                }
                for x in xs.iter().skip(1) {
                    write!(f, ", {}", x)?;
                }
                write!(f, ")")
            }
            Self::Function { func, bindings: _ } => {
                write!(f, "{}", func)
            }
            Self::Builtin(sym) => {
                write!(f, "{}", sym)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct StackFrame {
    bindings: HashTrieMap<Symbol, Value>,
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
    pub fn enter_frame_with_bindings(&mut self, bindings: HashTrieMap<Symbol, Value>) {
        // probably not the most efficient way of enabling recursion
        let mut next_bindings = match self {
            Self::Empty => HashTrieMap::new(),
            Self::Frame(x) => x.bindings.clone(),
        };
        for (bind, val) in &bindings {
            next_bindings.insert_mut(bind.clone(), val.clone());
        }
        *self = Self::Frame(StackFrame {
            bindings: next_bindings,
            previous: Box::new(self.clone()),
        });
    }

    pub fn bind(&mut self, bind: Symbol, value: Value) {
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

    pub fn get(&self, bind: &Symbol) -> Option<&Value> {
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

    fn get(&self, sym: &Symbol) -> Option<&Value> {
        match self.stack.get(sym) {
            Some(x) => Some(x),
            None => None,
        }
    }

    fn bindings(&self) -> HashTrieMap<Symbol, Value> {
        match &self.stack {
            Stack::Empty => HashTrieMap::new(),
            Stack::Frame(x) => x.bindings.clone(),
        }
    }

    fn is_builtin(sy: &Symbol) -> bool {
        sy.0.starts_with("builtin_")
    }

    fn eval_builtin_tup2(x: &Value) -> (Value, Value) {
        match x {
            Value::Tuple(values) if values.len() == 2 => (
                values.get(0).unwrap().clone(),
                values.get(1).unwrap().clone(),
            ),
            _ => panic!("a"),
        }
    }
    fn eval_builtin_int_int<F, O>(x: &Value, f: F) -> O
    where
        F: FnOnce(i128, i128) -> O,
    {
        match Self::eval_builtin_tup2(x) {
            (Value::Literal(Literal::Int(l)), Value::Literal(Literal::Int(r))) => f(l, r),
            (l, r) => panic!(
                "type mismatch. expected expression of type (Int, Int), found: ({}, {})",
                l, r
            ),
        }
    }
    fn eval_builtin_bool_bool<F, O>(x: &Value, f: F) -> O
    where
        F: FnOnce(bool, bool) -> O,
    {
        match Self::eval_builtin_tup2(x) {
            (Value::Literal(Literal::Bool(l)), Value::Literal(Literal::Bool(r))) => f(l, r),
            (l, r) => panic!(
                "type mismatch. expected expression of type (Bool, Bool), found: ({}, {})",
                l, r
            ),
        }
    }
    fn eval_builtin_bool<F, O>(x: &Value, f: F) -> O
    where
        F: FnOnce(bool) -> O,
    {
        match x {
            Value::Literal(Literal::Bool(x)) => f(*x),
            _ => panic!(
                "type mismatch. expected expression of type Bool, found: {}",
                x
            ),
        }
    }

    fn eval_builtin(sy: &Symbol, x: &Value) -> Value {
        match &sy.0[8..] {
            "eq" => Self::eval_builtin_int_int(x, |l, r| Value::Literal(Literal::Bool(l == r))),
            "add" => Self::eval_builtin_int_int(x, |l, r| Value::Literal(Literal::Int(l + r))),
            "sub" => Self::eval_builtin_int_int(x, |l, r| Value::Literal(Literal::Int(l - r))),
            "mul" => Self::eval_builtin_int_int(x, |l, r| Value::Literal(Literal::Int(l * r))),
            "div" => Self::eval_builtin_int_int(x, |l, r| Value::Literal(Literal::Int(l / r))),
            "and" => Self::eval_builtin_bool_bool(x, |l, r| Value::Literal(Literal::Bool(l && r))),
            "or" => Self::eval_builtin_bool_bool(x, |l, r| Value::Literal(Literal::Bool(l || r))),
            "not" => Self::eval_builtin_bool(x, |x| Value::Literal(Literal::Bool(!x))),
            _ => panic!("unknown builtin: {}", sy),
        }
    }

    fn enable_recursion(bind: &Symbol, val: Value) -> Value {
        match val.clone() {
            Value::Function { func, bindings } => Value::Function {
                func,
                bindings: bindings.insert(bind.clone(), val.clone()),
            },
            x => x,
        }
    }

    pub fn eval(&mut self, expr: &Expr) -> Value {
        match expr {
            Expr::Literal(x) => Value::Literal(*x),
            Expr::Symbol(x) => {
                if Self::is_builtin(x) {
                    Value::Builtin(x.clone())
                } else {
                    self.get(x)
                        .expect(&format!("symbol used before it was declared: \"{}\"", x))
                        .clone()
                }
            }
            Expr::IfElse(x) => match self.eval(&x.expr) {
                Value::Literal(Literal::Bool(true)) => self.eval(&x.case_true),
                Value::Literal(Literal::Bool(false)) => self.eval(&x.case_false),
                _ => panic!("type error"),
            },
            Expr::Function(x) => Value::Function {
                func: x.clone(),
                bindings: self.bindings(),
            },
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
                    Value::Builtin(sy) => Self::eval_builtin(sy, &arg_expr),
                    Value::Function { func, bindings } => {
                        self.stack.enter_frame_with_bindings(bindings.clone());
                        self.stack.bind(func.bind.clone(), arg_expr);
                        let e = self.eval(&func.expr);
                        self.stack.exit_frame();
                        e
                    }
                    _ => panic!("expected function, found: {}", func),
                }
            }
            Expr::Tuple(x) => {
                let exprs: Vec<Value> = x.exprs.iter().map(|e| self.eval(e)).collect();
                Value::Tuple(exprs)
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
