use crate::ast::*;
use crate::prelude::{sym, Symbol};
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

enum Error {
    TypeMismatch((Type, Type)),
    TupleArityMismatch,
}

type SymbolTypeContext = HashMap<Symbol, TypeScheme>;

pub fn prelude_ctx(gen: &mut VariableTypeGenerator) -> SymbolTypeContext {
    let mut ctx = SymbolTypeContext::new();

    let t_a = Type::Var(gen.next());
    let t_bool = Type::Basic(BasicType::Bool);
    let t_int = Type::Basic(BasicType::Int);
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
        ctx.insert(
            sym(format!("intrinsic_{}", name)),
            TypeScheme {
                variables: t.vars(),
                type_: t,
            },
        );
    }
    for (name, (l, r, out)) in arity_2_intrinsics.into_iter() {
        let t = Type::Func(Box::new(FunctionType {
            arg: Type::Tuple(TupleType(vec![l, r])),
            return_: out,
        }));
        ctx.insert(
            sym(format!("intrinsic_{}", name)),
            TypeScheme {
                variables: t.vars(),
                type_: t,
            },
        );
    }
    ctx
}

pub fn infer(expr: &Expr) -> Type {
    todo!()
}

#[derive(Debug)]
struct Substitution {
    subs: HashMap<VariableType, Type>,
}

impl Substitution {
    fn insert(&mut self, var: VariableType, ty: Type) {
        self.subs.insert(var, ty);
    }

    fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(v) => match self.subs.get(v).cloned() {
                Some(v) => v,
                None => Type::Var(*v),
            },
            Type::Func(t) => Type::Func(Box::new(FunctionType {
                arg: self.apply(&t.arg),
                return_: self.apply(&t.return_),
            })),
            Type::Tuple(t) => Type::Tuple(TupleType(t.0.iter().map(|t| self.apply(t)).collect())),
            Type::Basic(t) => Type::Basic(*t),
        }
    }
    fn apply_scheme(&self, ty: &TypeScheme) -> TypeScheme {
        let next = Substitution {
            subs: {
                let mut subs = self.subs.clone();
                for v in &ty.variables {
                    subs.remove(v);
                }
                subs
            },
        };
        TypeScheme {
            variables: ty.variables.clone(),
            type_: next.apply(&ty.type_),
        }
    }
    fn apply_context(&self, ctx: &SymbolTypeContext) -> SymbolTypeContext {
        ctx.iter()
            .map(|(s, t_sch)| (s.clone(), self.apply_scheme(t_sch)))
            .collect()
    }

    fn bind_symbol(&mut self, v: VariableType, t: Type) {
        if t.vars().contains(&v) {
            panic!("AAaaaaaaa");
        }
        self.subs.insert(v, t);
    }

    fn unify(&mut self, t1: Type, t2: Type) -> Result<(), Error> {
        match (t1, t2) {
            (Type::Var(t1), t2) => {
                self.bind_symbol(t1, t2);
                Ok(())
            }
            (t1, Type::Var(t2)) => {
                self.bind_symbol(t2, t1);
                Ok(())
            }
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
                        self.unify(t1.clone(), t2.clone())?;
                    }
                    Ok(())
                }
            }
            (t1, t2) => Err(Error::TypeMismatch((t1, t2))),
        }
    }
}
