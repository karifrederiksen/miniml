use crate::ast;
use crate::prelude::Symbol;
use ast::{Appl, Expr, Literal, Pattern};
use rpds::HashTrieMap;
use std::borrow::Borrow;
use std::collections::*;
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct ExecutionContext {
    bindings: HashMap<Symbol, Value>,
    recursives: Vec<ast::Let>,
    name: Pattern,
    height: u32,
    previous: Option<Rc<ExecutionContext>>,
}

impl fmt::Display for ExecutionContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let stack = self.stack();
        for &name in stack.iter() {
            writeln!(f, "  {}", name)?;
        }
        Ok(())
    }
}
impl ExecutionContext {
    pub fn new_empty() -> Self {
        Self {
            bindings: HashMap::new(),
            recursives: Vec::new(),
            name: Pattern::Symbol(Symbol("Empty_context".to_owned())),
            height: 0,
            previous: None,
        }
    }
    pub fn new_global_ctx(bindings: HashMap<Symbol, Value>) -> Self {
        Self {
            bindings,
            recursives: Vec::new(),
            name: Pattern::Symbol(Symbol("Global_context".to_owned())),
            height: 0,
            previous: None,
        }
    }

    pub fn stack(&self) -> Vec<&Pattern> {
        let mut ctx = self;
        let mut stack = vec![&self.name];
        while let Some(prev) = &ctx.previous {
            stack.push(&prev.name);
            ctx = &*prev;
        }
        stack
    }

    pub fn find<'a>(&'a self, name: &Symbol) -> Option<&'a Value> {
        let mut ctx: &'a ExecutionContext = self;
        loop {
            if let Some(v) = ctx.bindings.get(name) {
                return Some(v);
            }
            if let Some(prev) = &ctx.previous {
                ctx = prev;
            } else {
                return None;
            }
        }
    }

    pub fn bind(&mut self, pat: &Pattern, val: Value) {
        match (pat, val) {
            (Pattern::Symbol(s), val) => {
                self.bindings.insert(s.clone(), val);
            }
            (Pattern::Tuple(tp), Value::Tuple(tv)) => {
                for i in 0..tp.patterns.len() {
                    self.bind(tp.patterns.get(i).unwrap(), tv.get(i).unwrap().clone());
                }
            }
            (pat, val) => panic!("mismatch between pattern {} and value {}", pat, val),
        };
    }

    pub fn enter_ctx(self, name: &Pattern) -> Self {
        return ExecutionContext {
            bindings: HashMap::new(),
            recursives: Vec::new(),
            name: name.clone(),
            height: self.height + 1,
            previous: Some(Rc::new(self)),
        };
    }

    pub fn exit_ctx(&mut self) {
        match &self.previous {
            None => panic!("global context can't be exited"),
            Some(prev) => *self = (**prev).clone(),
        };
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Literal(Literal),
    Tuple(Vec<Value>),
    Function {
        func: ast::Function,
        context: ExecutionContext,
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
            Self::Function { func, context: _ } => {
                write!(f, "{}", func)
            }
            Self::Builtin(sym) => {
                write!(f, "{}", sym)
            }
        }
    }
}

#[derive(Debug)]
pub struct Interpreter {
    execution_contexts: Vec<ExecutionContext>,
}

impl Interpreter {
    pub fn new(global_context: ExecutionContext) -> Self {
        Self {
            execution_contexts: vec![global_context],
        }
    }

    fn get(&mut self, sym: &Symbol) -> Option<Value> {
        match self.current_ctx().find(sym) {
            Some(x) => Some(x.clone()),
            None => match self
                .current_ctx()
                .recursives
                .iter()
                .find(|x| x.bind.contains(sym))
                .cloned()
            {
                None => None,
                Some(x) => Some(self.eval(&*x.bind_expr)),
            },
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

    pub fn current_ctx_enter(&mut self, sy: &Pattern) {
        let ctx = self
            .execution_contexts
            .pop()
            .expect("global context should exist");
        self.execution_contexts.push(ctx.enter_ctx(sy));
    }

    pub fn current_ctx(&self) -> &ExecutionContext {
        self.execution_contexts
            .last()
            .expect("global context should exist")
    }

    pub fn current_ctx_mut(&mut self) -> &mut ExecutionContext {
        self.execution_contexts
            .last_mut()
            .expect("global context should exist")
    }

    pub fn eval(&mut self, expr: &Expr) -> Value {
        match expr {
            Expr::Literal(x) => Value::Literal(*x),
            Expr::Symbol(x) => {
                if Self::is_builtin(x) {
                    Value::Builtin(x.clone())
                } else {
                    self.get(x)
                        .expect(&format!(
                            "symbol used before it was declared: \"{}\"\n{}",
                            x,
                            self.current_ctx()
                        ))
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
                context: self.current_ctx().clone(),
            },
            Expr::Let(x) => {
                self.current_ctx_enter(&x.bind);
                if x.recursive {
                    self.current_ctx_mut().recursives.push(x.clone());
                }
                let bind_value = self.eval(&*x.bind_expr);
                self.current_ctx_mut().bind(&x.bind, bind_value);
                let next_value = self.eval(&*x.next_expr);
                self.current_ctx_mut().exit_ctx();
                if x.recursive {
                    self.current_ctx_mut().recursives.pop();
                }
                next_value
            }
            Expr::Appl(Appl { func, arg }) => {
                let func_expr = self.eval(func);
                let arg_expr = self.eval(arg);
                match func_expr {
                    Value::Builtin(sy) => Self::eval_builtin(&sy, &arg_expr),
                    Value::Function { func, mut context } => {
                        context.bind(&func.bind, arg_expr);
                        self.execution_contexts.push(context);
                        let e = self.eval(&func.expr);
                        self.execution_contexts.pop();
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
