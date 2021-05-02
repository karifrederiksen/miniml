#![allow(dead_code)]
#![allow(unused_imports)]

use ast::*;
use prelude::{sym, Symbol};
use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Debug)]
pub enum Error {
    TypeMismatch((Type, Type)),
    TupleArityMismatch,
}

pub struct SymbolTypeContext {
    global_symbol_type_map: HashMap<Symbol, TypeScheme>,
}

impl SymbolTypeContext {
    pub fn new() -> SymbolTypeContext {
        SymbolTypeContext {
            global_symbol_type_map: HashMap::new(),
        }
    }

    pub fn add_prelude(&mut self) {
        let t_a = Type::Var(VariableType("'a".to_owned()));
        let t_bool = Type::Intrinsic(IntrinsicType::Bool);
        let t_int = Type::Intrinsic(IntrinsicType::Int);
        let arity_1_intrinsics = vec![("not", (t_bool.clone(), t_bool.clone()))];
        let arity_2_intrinsics = vec![
            ("eq", (t_a.clone(), t_a.clone(), t_bool.clone())),
            ("add", (t_int.clone(), t_int.clone(), t_int.clone())),
            ("sub", (t_int.clone(), t_int.clone(), t_int.clone())),
            ("mul", (t_int.clone(), t_int.clone(), t_int.clone())),
            ("div", (t_int.clone(), t_int.clone(), t_int.clone())),
            ("mod", (t_int.clone(), t_int.clone(), t_int.clone())),
            ("and", (t_bool.clone(), t_bool.clone(), t_bool.clone())),
            ("or", (t_bool.clone(), t_bool.clone(), t_bool.clone())),
        ];
        for (name, (r, out)) in arity_1_intrinsics.into_iter() {
            let t = Type::Func(Box::new(FunctionType {
                arg: r,
                return_: out,
            }));
            self.global_symbol_type_map
                .insert(sym(format!("intrinsic_{}", name)), TypeScheme { type_: t });
        }
        for (name, (l, r, out)) in arity_2_intrinsics.into_iter() {
            let t = Type::Func(Box::new(FunctionType {
                arg: Type::Tuple(TupleType(vec![l, r])),
                return_: out,
            }));
            self.global_symbol_type_map
                .insert(sym(format!("intrinsic_{}", name)), TypeScheme { type_: t });
        }
    }
    pub fn add_global_symbol(&mut self, sy: Symbol, sch: TypeScheme) {
        self.global_symbol_type_map.insert(sy, sch);
    }
    pub fn annotate(&mut self, module: &mut Module) -> Result<(), Error> {
        for st in &mut module.statements {
            match st {
                Statement::SymbolBinding(st) => {
                    let mut gen = VariableTypeGenerator::new();
                    if st.recursive {
                        self.add_global_symbol(st.bind.clone(), gen.next_scheme());
                    }
                    let ty = self.infer(&mut gen, &st.expr)?;
                    let ty = ty.generalize(&mut gen);
                    self.add_global_symbol(st.bind.clone(), ty.clone());
                    st.type_ = Some(ty);
                }
                Statement::CustomType(t) => {
                    let ty = Type::Custom(t.type_.clone());
                    for v in &t.variants {
                        let ty = TypeScheme {
                            type_: match &v.contained_type {
                                None => ty.clone(),
                                Some(contained_type) => Type::Func(Box::new(FunctionType {
                                    arg: contained_type.clone(),
                                    return_: ty.clone(),
                                })),
                            },
                        };
                        self.add_global_symbol(v.constr.clone(), ty);
                    }
                }
            }
        }
        Ok(())
    }

    pub fn infer(&self, gen: &mut VariableTypeGenerator, expr: &Expr) -> Result<Type, Error> {
        let mut subber = Substitution::new();
        let mut scope_bindings = Vec::new();
        let type_ = self.infer_expr(gen, &mut scope_bindings, &mut subber, expr)?;
        Ok(subber.apply(type_))
    }
    fn infer_expr(
        &self,
        gen: &mut VariableTypeGenerator,
        scope_bindings: &mut Vec<(Symbol, Type)>,
        subst: &mut Substitution,
        expr: &Expr,
    ) -> Result<Type, Error> {
        match expr {
            Expr::Literal(Literal::Bool(_)) => Ok(Type::Intrinsic(IntrinsicType::Bool)),
            Expr::Literal(Literal::Int(_)) => Ok(Type::Intrinsic(IntrinsicType::Int)),
            Expr::Symbol(x) => match self.global_symbol_type_map.get(x) {
                Some(t) => Ok(t.instantiate(gen)),
                None => match scope_bindings.iter().rev().find(|(key, _)| key == x) {
                    Some((_, t)) => Ok(t.clone()),
                    None => todo!("undefined symbol: {}", x),
                },
            },
            Expr::VariantConstr(Variant { constr, value }) => {
                match self.global_symbol_type_map.get(&constr) {
                    Some(constr_t) => {
                        let arg_t = match value {
                            None => None,
                            Some(x) => Some(self.infer_expr(gen, scope_bindings, subst, &*x)),
                        };
                        match (constr_t.instantiate(gen), arg_t) {
                            (Type::Func(func_t), Some(arg_t)) => {
                                let arg_t = arg_t?;
                                subst.unify(func_t.arg.clone(), arg_t)?;
                                Ok(subst.apply(func_t.return_))
                            }
                            (t, None) => Ok(t),
                            (x, y) => todo!("this should be an error?\n {:?}\n {:?}", x, y),
                        }
                    }
                    None => todo!("undefined variant constructor: {}", constr),
                }
            }
            Expr::Function(x) => {
                let (arg_t, arg_n) = self.infer_pattern(gen, scope_bindings, subst, &x.bind)?;
                let return_t = self.infer_expr(gen, scope_bindings, subst, &*x.expr);
                Self::remove_n_bindings(scope_bindings, arg_n);
                Ok(Type::Func(Box::new(FunctionType {
                    arg: subst.apply(arg_t),
                    return_: return_t?,
                })))
            }
            Expr::Appl(x) => {
                let return_t = Type::Var(gen.next());
                let func = self.infer_expr(gen, scope_bindings, subst, &x.func)?;
                let arg = self.infer_expr(gen, scope_bindings, subst, &x.arg)?;
                subst.unify(
                    subst.apply(func),
                    Type::Func(Box::new(FunctionType {
                        arg,
                        return_: return_t.clone(),
                    })),
                )?;
                let t = subst.apply(return_t);
                Ok(t)
            }
            Expr::IfElse(x) => {
                let expr = self.infer_expr(gen, scope_bindings, subst, &x.expr)?;
                subst.unify(expr, Type::Intrinsic(IntrinsicType::Bool))?;
                let case_true = self.infer_expr(gen, scope_bindings, subst, &x.case_true)?;
                let case_false = self.infer_expr(gen, scope_bindings, subst, &x.case_false)?;
                subst.unify(case_true.clone(), case_false)?;
                Ok(subst.apply(case_true))
            }
            Expr::Match(x) => {
                let expr_t = self.infer_expr(gen, scope_bindings, subst, &x.expr)?;
                let return_ = Type::Var(gen.next());

                for case in &x.cases {
                    let (pattern_t, n) =
                        self.infer_pattern(gen, scope_bindings, subst, &case.pattern)?;
                    if let Err(e) = subst.unify(pattern_t, expr_t.clone()) {
                        Self::remove_n_bindings(scope_bindings, n);
                        return Err(e);
                    };
                    let expr_t = self.infer_expr(gen, scope_bindings, subst, &case.expr);
                    Self::remove_n_bindings(scope_bindings, n);
                    let expr_t = subst.apply(expr_t?);
                    subst.unify(return_.clone(), expr_t)?;
                }
                let t = subst.apply(return_);
                Ok(t)
            }
            Expr::Let(x) => {
                let (bind_t, bind_n) = self.infer_pattern(gen, scope_bindings, subst, &x.bind)?;
                let bind_expr_t = match self.infer_expr(gen, scope_bindings, subst, &x.bind_expr) {
                    Ok(x) => x,
                    e => {
                        Self::remove_n_bindings(scope_bindings, bind_n);
                        return e;
                    }
                };
                if let Err(e) = subst.unify(bind_t, bind_expr_t) {
                    Self::remove_n_bindings(scope_bindings, bind_n);
                    return Err(e);
                };
                let next_expr_t = self.infer_expr(gen, scope_bindings, subst, &x.next_expr);
                Self::remove_n_bindings(scope_bindings, bind_n);
                next_expr_t
            }
            Expr::Tuple(x) => {
                let mut ts: Vec<Type> = Vec::with_capacity(x.0.len());
                for e in &x.0 {
                    ts.push(self.infer_expr(gen, scope_bindings, subst, e)?);
                }
                Ok(subst.apply(Type::Tuple(TupleType(ts))))
            }
        }
    }
    fn infer_pattern(
        &self,
        gen: &mut VariableTypeGenerator,
        scope_bindings: &mut Vec<(Symbol, Type)>,
        subst: &mut Substitution,
        pat: &Pattern,
    ) -> Result<(Type, usize), Error> {
        match pat {
            Pattern::Symbol(x) => {
                let t = Type::Var(gen.next());
                scope_bindings.push((x.clone(), t.clone()));
                Ok((t, 1))
            }
            Pattern::Tuple(x) => {
                let mut n = 0;
                let mut ts = Vec::<Type>::new();
                for pat in &x.0 {
                    let (t, tn) = self.infer_pattern(gen, scope_bindings, subst, pat)?;
                    ts.push(t);
                    n += tn;
                }
                Ok((Type::Tuple(TupleType(ts)), n))
            }
            Pattern::Variant(x) => {
                match (
                    self.global_symbol_type_map.get(&x.constr),
                    &x.contained_pattern,
                ) {
                    (Some(t), Some(p)) => match t.instantiate(gen) {
                        Type::Func(ft) => {
                            let (p_t, n) = self.infer_pattern(gen, scope_bindings, subst, p)?;
                            subst.unify(p_t, ft.arg)?;
                            Ok((subst.apply(ft.return_), n))
                        }
                        _ => panic!("this is a compiler/interpreter invariant error"),
                    },
                    (Some(t), None) => Ok((t.instantiate(gen), 0)),
                    _ => todo!("this'll have to be an error"),
                }
            }
        }
    }
    fn remove_n_bindings(scope_bindings: &mut Vec<(Symbol, Type)>, n: usize) {
        scope_bindings.truncate(scope_bindings.len() - n);
    }
}

#[derive(Debug)]
struct Substitution {
    subs: HashMap<VariableType, Type>,
}

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ ")?;
        for (k, v) in &self.subs {
            write!(f, "{} => {}, ", k, v)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl Substitution {
    fn new() -> Self {
        Self {
            subs: HashMap::new(),
        }
    }

    fn insert(&mut self, var: VariableType, ty: Type) {
        let var_t = Type::Var(var.clone());
        let keys_to_update: Vec<_> = self
            .subs
            .iter()
            .filter(|(_, val)| *val == &var_t)
            .map(|(key, _)| key.clone())
            .collect();
        for key in keys_to_update.into_iter() {
            self.subs.insert(key, ty.clone());
        }
        self.subs.insert(var, ty);
    }

    fn apply(&self, ty: Type) -> Type {
        match ty {
            Type::Var(v) => match self.subs.get(&v).cloned() {
                Some(v) => v,
                None => Type::Var(v),
            },
            Type::Func(t) => Type::Func(Box::new(FunctionType {
                arg: self.apply(t.arg),
                return_: self.apply(t.return_),
            })),
            Type::Tuple(t) => {
                Type::Tuple(TupleType(t.0.into_iter().map(|t| self.apply(t)).collect()))
            }
            Type::Intrinsic(t) => Type::Intrinsic(t),
            Type::Custom(t) => Type::Custom(CustomType {
                name: t.name.clone(),
                variables: t.variables.iter().map(|v| self.apply(v.clone())).collect(),
            }),
        }
    }
    fn apply_scheme(&self, sch: &TypeScheme) -> TypeScheme {
        TypeScheme {
            type_: self.apply(sch.type_.clone()),
        }
    }
    fn apply_context(&self, ctx: &SymbolTypeContext) -> SymbolTypeContext {
        SymbolTypeContext {
            global_symbol_type_map: ctx
                .global_symbol_type_map
                .iter()
                .map(|(s, t_sch)| (s.clone(), self.apply_scheme(t_sch)))
                .collect(),
        }
    }

    fn bind_symbol(&mut self, v: VariableType, t: Type) -> Result<(), Error> {
        if t.vars().contains(&v) {
            todo!("contains check failed");
        }
        if let Some(old_t) = self.subs.get(&v).cloned() {
            self.unify(t.clone(), old_t)?;
            self.insert(v, self.apply(t));
        } else {
            self.insert(v, t);
        }
        Ok(())
    }

    fn unify(&mut self, t1: Type, t2: Type) -> Result<(), Error> {
        if t1 == t2 {
            return Ok(());
        }
        match (t1, t2) {
            (Type::Var(t1), t2) => self.bind_symbol(t1, t2),
            (t1, Type::Var(t2)) => self.bind_symbol(t2, t1),
            (Type::Func(t1), Type::Func(t2)) => {
                self.unify(t1.arg.clone(), t2.arg.clone())?;
                self.unify(t1.return_.clone(), t2.return_.clone())?;
                Ok(())
            }
            (Type::Tuple(t1), Type::Tuple(t2)) => {
                if t1.0.len() != t2.0.len() {
                    Err(Error::TupleArityMismatch)
                } else {
                    for (t1, t2) in t1.0.iter().zip(t2.0.iter()) {
                        self.unify(self.apply(t1.clone()), self.apply(t2.clone()))?;
                    }
                    Ok(())
                }
            }
            (Type::Custom(t1), Type::Custom(t2)) => {
                if t1.variables.len() != t2.variables.len() {
                    Err(Error::TupleArityMismatch) // make another error variant
                } else {
                    for (t1, t2) in t1.variables.iter().zip(t2.variables.iter()) {
                        self.unify(self.apply(t1.clone()), self.apply(t2.clone()))?;
                    }
                    Ok(())
                }
            }
            (t1, t2) => Err(Error::TypeMismatch((t1, t2))),
        }
    }
}

fn print_subst(subst: &Substitution) {
    print!("subst: {{");
    for (k, v) in &subst.subs {
        print!("{} = {}, ", k, v);
    }
    println!("}}");
}
