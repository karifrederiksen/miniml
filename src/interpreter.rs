use crate::ast;
use crate::prelude::Symbol;
use ast::{Appl, BasicType, Expr, Literal, Module, Pattern, TupleType, Type, VariableType};
use rpds::HashTrieMap;
use std::borrow::Borrow;
use std::collections::*;
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct ExecutionContext {
    bindings: HashMap<Symbol, Value>,
    recursives: Vec<(Pattern, Expr)>,
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

#[derive(Debug, Clone)]
pub enum InterpError {
    TypeMismatch((Type, Value)),
    StackOverflow,
    UndefinedSymbol(Symbol),
}

#[derive(Debug)]
pub struct Interpreter {
    execution_contexts: Vec<ExecutionContext>,
    depth: usize,
}

impl Interpreter {
    pub fn new(global_context: ExecutionContext) -> Self {
        Self {
            execution_contexts: vec![global_context],
            depth: 0,
        }
    }

    fn get(&mut self, sym: &Symbol) -> Result<Value, InterpError> {
        match self.current_ctx().find(sym) {
            Some(x) => Ok(x.clone()),
            None => match self
                .current_ctx()
                .recursives
                .iter()
                .find(|x| x.0.contains(sym))
                .cloned()
            {
                None => Err(InterpError::UndefinedSymbol(sym.clone())),
                Some(x) => self.eval(&x.1),
            },
        }
    }

    fn is_builtin(sy: &Symbol) -> bool {
        sy.0.starts_with("builtin_")
    }

    fn eval_builtin_tup2(x: &Value) -> Result<(Value, Value), InterpError> {
        match x {
            Value::Tuple(values) if values.len() == 2 => Ok((
                values.get(0).unwrap().clone(),
                values.get(1).unwrap().clone(),
            )),
            _ => Err(InterpError::TypeMismatch((
                Type::Tuple(TupleType(vec![
                    Type::Var(VariableType(0)),
                    Type::Var(VariableType(1)),
                ])),
                x.clone(),
            ))),
        }
    }
    fn eval_builtin_int_int<F, O>(x: &Value, f: F) -> Result<O, InterpError>
    where
        F: FnOnce(i128, i128) -> O,
    {
        match Self::eval_builtin_tup2(x)? {
            (Value::Literal(Literal::Int(l)), Value::Literal(Literal::Int(r))) => Ok(f(l, r)),
            (l, r) => Err(InterpError::TypeMismatch((
                Type::Tuple(TupleType(vec![
                    Type::Basic(BasicType::Int),
                    Type::Basic(BasicType::Int),
                ])),
                Value::Tuple(vec![l, r]),
            ))),
        }
    }
    fn eval_builtin_bool_bool<F, O>(x: &Value, f: F) -> Result<O, InterpError>
    where
        F: FnOnce(bool, bool) -> O,
    {
        match Self::eval_builtin_tup2(x)? {
            (Value::Literal(Literal::Bool(l)), Value::Literal(Literal::Bool(r))) => Ok(f(l, r)),
            (l, r) => Err(InterpError::TypeMismatch((
                Type::Tuple(TupleType(vec![
                    Type::Basic(BasicType::Bool),
                    Type::Basic(BasicType::Bool),
                ])),
                Value::Tuple(vec![l, r]),
            ))),
        }
    }
    fn eval_builtin_bool<F, O>(x: &Value, f: F) -> Result<O, InterpError>
    where
        F: FnOnce(bool) -> O,
    {
        match x {
            Value::Literal(Literal::Bool(x)) => Ok(f(*x)),
            x => Err(InterpError::TypeMismatch((
                Type::Basic(BasicType::Bool),
                x.clone(),
            ))),
        }
    }

    fn eval_builtin(sy: &Symbol, x: &Value) -> Result<Value, InterpError> {
        match &sy.0[8..] {
            "eq" => Self::eval_builtin_int_int(x, |l, r| Value::Literal(Literal::Bool(l == r))),
            "add" => Self::eval_builtin_int_int(x, |l, r| Value::Literal(Literal::Int(l + r))),
            "sub" => Self::eval_builtin_int_int(x, |l, r| Value::Literal(Literal::Int(l - r))),
            "mul" => Self::eval_builtin_int_int(x, |l, r| Value::Literal(Literal::Int(l * r))),
            "div" => Self::eval_builtin_int_int(x, |l, r| Value::Literal(Literal::Int(l / r))),
            "and" => Self::eval_builtin_bool_bool(x, |l, r| Value::Literal(Literal::Bool(l && r))),
            "or" => Self::eval_builtin_bool_bool(x, |l, r| Value::Literal(Literal::Bool(l || r))),
            "not" => Self::eval_builtin_bool(x, |x| Value::Literal(Literal::Bool(!x))),
            _ => Err(InterpError::UndefinedSymbol(sy.clone())),
        }
    }

    pub fn current_ctx_enter(&mut self, sy: &Pattern) {
        if self.execution_contexts.len() > 10_000 {
            panic!("Stack overflow");
        }
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

    pub fn eval(&mut self, expr: &Expr) -> Result<Value, InterpError> {
        if self.depth > 1_000 {
            return Err(InterpError::StackOverflow);
        }
        self.depth += 1;
        let val = match expr {
            Expr::Literal(x) => Ok(Value::Literal(*x)),
            Expr::Symbol(x) => {
                if Self::is_builtin(x) {
                    Ok(Value::Builtin(x.clone()))
                } else {
                    self.get(x)
                }
            }
            Expr::IfElse(x) => match self.eval(&x.expr)? {
                Value::Literal(Literal::Bool(true)) => self.eval(&x.case_true),
                Value::Literal(Literal::Bool(false)) => self.eval(&x.case_false),
                _ => panic!("type error"),
            },
            Expr::Function(x) => Ok(Value::Function {
                func: x.clone(),
                context: self.current_ctx().clone(),
            }),
            Expr::Let(x) => {
                self.current_ctx_enter(&x.bind);
                if x.recursive {
                    self.current_ctx_mut()
                        .recursives
                        .push((x.bind.clone(), *x.bind_expr.clone()));
                }
                let bind_value = self.eval(&*x.bind_expr)?;
                self.current_ctx_mut().bind(&x.bind, bind_value);
                let next_value = self.eval(&*x.next_expr)?;
                self.current_ctx_mut().exit_ctx();
                if x.recursive {
                    self.current_ctx_mut().recursives.pop();
                }
                Ok(next_value)
            }
            Expr::Appl(Appl { func, arg }) => {
                let func_expr = self.eval(func)?;
                let arg_expr = self.eval(arg)?;
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
                let mut exprs = Vec::with_capacity(x.exprs.len());
                for e in &x.exprs {
                    exprs.push(self.eval(e)?);
                }
                Ok(Value::Tuple(exprs))
            }
        };
        self.depth -= 1;
        val
    }
    fn eval_statement(&mut self, st: &ast::Statement) -> Result<(), InterpError> {
        match st {
            ast::Statement::Let(st) => {
                self.current_ctx_enter(&Pattern::Symbol(st.bind.clone()));
                if st.recursive {
                    self.current_ctx_mut()
                        .recursives
                        .push((Pattern::Symbol(st.bind.clone()), st.expr.clone()));
                }
                let bind_value = self.eval(&st.expr)?;
                self.current_ctx_mut().exit_ctx();
                self.current_ctx_mut()
                    .bind(&Pattern::Symbol(st.bind.clone()), bind_value);
                if st.recursive {
                    self.current_ctx_mut().recursives.pop();
                }
            }
        }
        Ok(())
    }
    pub fn eval_module(&mut self, module: &Module) -> Result<(), InterpError> {
        for st in &module.statements {
            self.eval_statement(st)?;
        }
        Ok(())
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
