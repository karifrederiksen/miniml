use ast::*;
use prelude::*;
use std::collections::*;
use std::fmt;
use std::rc::Rc;

// here's some inspiration
//   https://betterprogramming.pub/execution-context-lexical-environment-and-closures-in-javascript-b57c979341a5
//   https://medium.com/@5066aman/lexical-environment-the-hidden-part-to-understand-closures-71d60efac0e0

#[derive(Debug, Clone)]
pub enum Value {
    Literal(Literal),
    Tuple(Vec<Value>),
    Function {
        func: ast::Function,
        context: ExecutionContext,
    },
    Variant((Symbol, Option<Box<Value>>)),
    Intrinsic(Symbol),
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
            Self::Variant((ty, sym)) => {
                write!(f, "{}", ty)?;
                if let Some(sym) = sym {
                    write!(f, " {}", sym)?;
                }
                Ok(())
            }
            Self::Intrinsic(sym) => {
                write!(f, "{}", sym)
            }
        }
    }
}
impl Value {
    fn matches(&self, pat: &Pattern) -> bool {
        match (pat, self) {
            (Pattern::Symbol(_), _) => true,
            (Pattern::Variant(p), Self::Variant((v_constr, _))) => p.constr == *v_constr,
            (Pattern::Tuple(p), Self::Tuple(vals)) => {
                if p.0.len() != vals.len() {
                    return false;
                }
                for i in 0..p.0.len() {
                    if !vals.get(i).unwrap().matches(p.0.get(i).unwrap()) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
}

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
            write!(f, "  {}: ", name)?;
            writeln!(f)?;
        }
        Ok(())
    }
}
impl ExecutionContext {
    pub fn new_empty() -> Self {
        Self {
            bindings: HashMap::new(),
            recursives: Vec::new(),
            name: Pattern::Symbol(Symbol("Global context".to_owned())),
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

    pub fn bind(&mut self, pat: &Pattern, val: Value) -> Result<(), Error> {
        match (pat, val) {
            (Pattern::Symbol(s), val) => {
                self.bindings.insert(s.clone(), val);
                Ok(())
            }
            (Pattern::Tuple(tp), Value::Tuple(tv)) => {
                for i in 0..tp.0.len() {
                    self.bind(tp.0.get(i).unwrap(), tv.get(i).unwrap().clone())?;
                }
                Ok(())
            }
            (Pattern::Variant(v), Value::Variant((ty, val))) => {
                if v.constr == ty {
                    match (&v.contained_pattern, val) {
                        (Some(pattern), Some(val)) => {
                            self.bind(&*pattern, *val)?;
                        }
                        _ => panic!("pattern mismatch"),
                    }
                    Ok(())
                } else {
                    unreachable!("I think this is supposed to be handled earlier")
                }
            }
            (pat, val) => panic!("mismatch between pattern {} and value {}", pat, val),
        }
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
            None => unreachable!("global context can't be exited"),
            Some(prev) => *self = (**prev).clone(),
        };
    }
}

#[derive(Debug, Clone)]
pub struct Error {
    pub stack: Vec<Pattern>,
    pub kind: ErrorKind,
}

#[derive(Debug, Clone)]
pub enum ErrorKind {
    TypeMismatch((Type, Value)),
    DepthLimitReached,
    UndefinedSymbol(Symbol),
}

#[derive(Debug)]
pub struct Interpreter {
    execution_contexts: Vec<ExecutionContext>,
    types: HashMap<CustomTypeSymbol, CustomTypeDefinition>,
    depth: usize,
}

impl Interpreter {
    pub fn new(global_context: ExecutionContext) -> Self {
        Self {
            execution_contexts: vec![global_context],
            types: HashMap::new(),
            depth: 0,
        }
    }

    fn error<A>(&self, kind: ErrorKind) -> Result<A, Error> {
        Err(Error {
            stack: self.current_ctx().stack().into_iter().cloned().collect(),
            kind,
        })
    }

    fn get(&mut self, sym: &Symbol) -> Result<Value, Error> {
        match self.current_ctx().find(sym) {
            Some(x) => Ok(x.clone()),
            None => match self
                .current_ctx()
                .recursives
                .iter()
                .find(|x| x.0.contains(sym))
                .cloned()
            {
                None => self.error(ErrorKind::UndefinedSymbol(sym.clone())),
                Some(x) => self.eval(&x.1),
            },
        }
    }

    #[inline]
    fn is_intrinsic(sy: &Symbol) -> bool {
        sy.0.starts_with("intrinsic_")
    }

    #[inline]
    fn eval_tup2(x: &Value) -> Result<(Value, Value), ErrorKind> {
        match x {
            Value::Tuple(values) if values.len() == 2 => Ok((
                values.get(0).unwrap().clone(),
                values.get(1).unwrap().clone(),
            )),
            _ => Err(ErrorKind::TypeMismatch((
                Type::Tuple(TupleType(vec![
                    Type::Var(VariableType("?a".to_owned())),
                    Type::Var(VariableType("?b".to_owned())),
                ])),
                x.clone(),
            ))),
        }
    }
    #[inline]
    fn eval_intrinsic_int_int<F, O>(x: &Value, f: F) -> Result<O, ErrorKind>
    where
        F: FnOnce(i128, i128) -> O,
    {
        match Self::eval_tup2(x)? {
            (Value::Literal(Literal::Int(l)), Value::Literal(Literal::Int(r))) => Ok(f(l, r)),
            (l, r) => Err(ErrorKind::TypeMismatch((
                Type::Tuple(TupleType(vec![
                    Type::Intrinsic(IntrinsicType::Int),
                    Type::Intrinsic(IntrinsicType::Int),
                ])),
                Value::Tuple(vec![l, r]),
            ))),
        }
    }
    #[inline]
    fn eval_intrinsic_bool_bool<F, O>(x: &Value, f: F) -> Result<O, ErrorKind>
    where
        F: FnOnce(bool, bool) -> O,
    {
        match Self::eval_tup2(x)? {
            (Value::Literal(Literal::Bool(l)), Value::Literal(Literal::Bool(r))) => Ok(f(l, r)),
            (l, r) => Err(ErrorKind::TypeMismatch((
                Type::Tuple(TupleType(vec![
                    Type::Intrinsic(IntrinsicType::Bool),
                    Type::Intrinsic(IntrinsicType::Bool),
                ])),
                Value::Tuple(vec![l, r]),
            ))),
        }
    }
    #[inline]
    fn eval_intrinsic_bool<F, O>(x: &Value, f: F) -> Result<O, ErrorKind>
    where
        F: FnOnce(bool) -> O,
    {
        match x {
            Value::Literal(Literal::Bool(x)) => Ok(f(*x)),
            x => Err(ErrorKind::TypeMismatch((
                Type::Intrinsic(IntrinsicType::Bool),
                x.clone(),
            ))),
        }
    }

    #[inline]
    fn eval_intrinsic(sy: &Symbol, x: &Value) -> Result<Value, ErrorKind> {
        match &sy.0[10..] {
            "eq" => Self::eval_intrinsic_int_int(x, |l, r| Value::Literal(Literal::Bool(l == r))),
            "add" => Self::eval_intrinsic_int_int(x, |l, r| Value::Literal(Literal::Int(l + r))),
            "sub" => Self::eval_intrinsic_int_int(x, |l, r| Value::Literal(Literal::Int(l - r))),
            "mul" => Self::eval_intrinsic_int_int(x, |l, r| Value::Literal(Literal::Int(l * r))),
            "div" => Self::eval_intrinsic_int_int(x, |l, r| Value::Literal(Literal::Int(l / r))),
            "and" => {
                Self::eval_intrinsic_bool_bool(x, |l, r| Value::Literal(Literal::Bool(l && r)))
            }
            "or" => Self::eval_intrinsic_bool_bool(x, |l, r| Value::Literal(Literal::Bool(l || r))),
            "not" => Self::eval_intrinsic_bool(x, |x| Value::Literal(Literal::Bool(!x))),
            _ => Err(ErrorKind::UndefinedSymbol(sy.clone())),
        }
    }

    #[inline]
    pub fn current_ctx_enter(&mut self, sy: &Pattern) {
        let ctx = self
            .execution_contexts
            .pop()
            .expect("global context should exist");
        self.execution_contexts.push(ctx.enter_ctx(sy));
    }

    #[inline]
    pub fn current_ctx(&self) -> &ExecutionContext {
        self.execution_contexts
            .last()
            .expect("global context should exist")
    }

    #[inline]
    pub fn current_ctx_mut(&mut self) -> &mut ExecutionContext {
        self.execution_contexts
            .last_mut()
            .expect("global context should exist")
    }

    pub fn eval(&mut self, expr: &Expr) -> Result<Value, Error> {
        if self.depth > 1_000 {
            return self.error(ErrorKind::DepthLimitReached);
        }
        self.depth += 1;
        let val = match expr {
            Expr::Literal(x) => Ok(Value::Literal(*x)),
            Expr::Symbol(x) => {
                if Self::is_intrinsic(x) {
                    Ok(Value::Intrinsic(x.clone()))
                } else {
                    self.get(x)
                }
            }
            Expr::VariantConstr(x) => {
                if let Some(arg) = &x.value {
                    let arg = self.eval(arg)?;
                    Ok(Value::Variant((x.constr.clone(), Some(Box::new(arg)))))
                } else {
                    // Value::Variant((Symbol, Option<Box<Value>>))
                    todo!()
                }
            }
            Expr::IfElse(x) => match self.eval(&x.expr)? {
                Value::Literal(Literal::Bool(true)) => self.eval(&x.case_true),
                Value::Literal(Literal::Bool(false)) => self.eval(&x.case_false),
                x => self.error(ErrorKind::TypeMismatch((
                    Type::Intrinsic(IntrinsicType::Bool),
                    x.clone(),
                ))),
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
                self.current_ctx_mut().bind(&x.bind, bind_value)?;
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
                    Value::Intrinsic(sy) => match Self::eval_intrinsic(&sy, &arg_expr) {
                        Err(e) => self.error(e),
                        Ok(x) => Ok(x),
                    },
                    Value::Function { func, mut context } => {
                        context.bind(&func.bind, arg_expr)?;
                        self.execution_contexts.push(context);
                        let e = self.eval(&func.expr);
                        self.execution_contexts.pop();
                        e
                    }
                    _ => panic!("expected function, found: {}", func),
                }
            }
            Expr::Tuple(x) => {
                let mut exprs = Vec::with_capacity(x.0.len());
                for e in &x.0 {
                    exprs.push(self.eval(e)?);
                }
                Ok(Value::Tuple(exprs))
            }
            Expr::Match(x) => {
                let mut val: Option<Value> = None;
                let value = self.eval(&x.expr)?;
                for c in &x.cases {
                    if value.matches(&c.pattern) {
                        self.current_ctx_enter(&c.pattern);
                        self.current_ctx_mut().bind(&c.pattern, value)?;
                        val = Some(self.eval(&*c.expr)?);
                        self.current_ctx_mut().exit_ctx();
                        break;
                    }
                }
                let val = match val {
                    None => panic!("no matching pattern"),
                    Some(x) => x,
                };
                Ok(val)
            }
        };
        self.depth -= 1;
        val
    }
    fn eval_statement(&mut self, st: &ast::Statement) -> Result<(), Error> {
        match st {
            Statement::SymbolBinding(st) => {
                self.current_ctx_enter(&Pattern::Symbol(st.bind.clone()));
                if st.recursive {
                    self.current_ctx_mut()
                        .recursives
                        .push((Pattern::Symbol(st.bind.clone()), st.expr.clone()));
                }
                let bind_value = self.eval(&st.expr)?;
                self.current_ctx_mut().exit_ctx();
                self.current_ctx_mut()
                    .bind(&Pattern::Symbol(st.bind.clone()), bind_value)?;
                if st.recursive {
                    self.current_ctx_mut().recursives.pop();
                }
            }
            Statement::CustomType(t) => {
                for v in &t.variants {
                    let value = match &v.contained_type {
                        None => Value::Variant((v.constr.clone(), None)),
                        Some(_) => Value::Function {
                            func: Function {
                                bind: Pattern::Symbol(sym("a")),
                                expr: Box::new(Expr::VariantConstr(Variant {
                                    constr: v.constr.clone(),
                                    value: Some(Box::new(Expr::Symbol(sym("a")))),
                                })),
                            },
                            context: self.current_ctx().clone(),
                        },
                    };
                    self.current_ctx_mut()
                        .bind(&Pattern::Symbol(v.constr.clone()), value)?;
                }
            }
        }
        Ok(())
    }
    pub fn eval_module(&mut self, module: &Module) -> Result<(), Error> {
        for st in &module.statements {
            self.eval_statement(st)?;
        }
        Ok(())
    }
}
