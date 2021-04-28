use crate::ast::*;
use crate::prelude::{sym, Symbol};
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

type SymbolTypeContext = HashMap<Symbol, TypeScheme>;

pub fn prelude_ctx(gen: &mut VariableTypeGenerator) -> SymbolTypeContext {
    let mut ctx = SymbolTypeContext::new();

    let t_a = Type::Var(gen.next());
    let t_bool = Type::Basic(BasicType::Bool);
    let t_int = Type::Basic(BasicType::Int);
    let arity_1_builtins = vec![("not", (t_bool.clone(), t_bool.clone()))];
    let arity_2_builtins = vec![
        ("eq", (t_a.clone(), t_a.clone(), t_bool.clone())),
        ("add", (t_int.clone(), t_int.clone(), t_int.clone())),
        ("sub", (t_int.clone(), t_int.clone(), t_int.clone())),
        ("mul", (t_int.clone(), t_int.clone(), t_int.clone())),
        ("div", (t_int.clone(), t_int.clone(), t_int.clone())),
        ("mod", (t_int.clone(), t_int.clone(), t_int.clone())),
        ("and", (t_bool.clone(), t_bool.clone(), t_bool.clone())),
        ("or", (t_bool.clone(), t_bool.clone(), t_bool.clone())),
    ];

    for (name, (r, out)) in arity_1_builtins.into_iter() {
        let t = Type::Func(Box::new(FunctionType {
            arg: r,
            return_: out,
        }));
        ctx.insert(
            sym(format!("builtin_{}", name)),
            TypeScheme {
                variables: t.vars(),
                type_: t,
            },
        );
    }
    for (name, (l, r, out)) in arity_2_builtins.into_iter() {
        let t = Type::Func(Box::new(FunctionType {
            arg: Type::Tuple(TupleType(vec![l, r])),
            return_: out,
        }));
        ctx.insert(
            sym(format!("builtin_{}", name)),
            TypeScheme {
                variables: t.vars(),
                type_: t,
            },
        );
    }
    ctx
}
