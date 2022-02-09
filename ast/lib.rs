#![feature(box_patterns)]
mod printer;

use prelude::*;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Literal {
    Bool(bool),
    Int(i128),
}

#[derive(Clone, PartialEq, Eq)]
pub struct VariantDefinition {
    pub constr: Symbol,
    pub contained_type: Option<Type>,
}

#[derive(Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct CustomTypeSymbol(pub String);

#[derive(Clone, PartialEq, Eq)]
pub struct CustomTypeDefinition {
    pub type_: CustomType,
    pub variants: Vec<VariantDefinition>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct VariantPattern {
    pub constr: Symbol,
    pub contained_pattern: Option<Box<Pattern>>,
}

#[derive(Clone, PartialEq, Eq)]
pub enum Pattern {
    Symbol((Span, Symbol)),
    Tuple((Span, Vec<Pattern>)),
    Variant((Span, VariantPattern)),
}

impl Pattern {
    pub fn contains(&self, s: &Symbol) -> bool {
        match self {
            Self::Symbol(x) => &x.1 == s,
            Self::Tuple(ts) => ts.1.iter().any(|x| x.contains(s)),
            Self::Variant(v) => match &v.1.contained_pattern {
                None => false,
                Some(x) => x.contains(s),
            },
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Function {
    pub bind: Pattern,
    pub expr: Box<Expr>,
}

impl Function {
    pub fn replace_symbols(&mut self, symbols: &HashMap<Symbol, Expr>) {
        Self::replace_bound_expr(&mut self.expr, symbols);
    }

    fn replace_bound_expr(e: &mut Expr, symbols: &HashMap<Symbol, Expr>) {
        match e {
            Expr::Symbol((_, x)) => {
                if let Some(val) = symbols.get(x) {
                    *e = val.clone();
                }
            }
            Expr::Literal(_) => (),
            Expr::Function((_, x)) => {
                Self::replace_bound_expr(&mut x.expr, symbols);
            }
            Expr::Let((_, x)) => {
                Self::replace_bound_expr(&mut x.bind_expr, symbols);
                Self::replace_bound_expr(&mut x.next_expr, symbols);
            }
            Expr::Appl((_, x)) => {
                Self::replace_bound_expr(&mut x.arg, symbols);
                Self::replace_bound_expr(&mut x.func, symbols);
            }
            Expr::IfElse((_, x)) => {
                Self::replace_bound_expr(&mut x.expr, symbols);
                Self::replace_bound_expr(&mut x.case_true, symbols);
                Self::replace_bound_expr(&mut x.case_false, symbols);
            }
            Expr::Tuple((_, x)) => {
                for e in x.iter_mut() {
                    Self::replace_bound_expr(e, symbols);
                }
            }
            Expr::Match((_, x)) => {
                Self::replace_bound_expr(&mut x.expr, symbols);
                for c in x.cases.iter_mut() {
                    Self::replace_bound_expr(&mut c.expr, symbols);
                }
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Let {
    pub bind: Pattern,
    pub bind_expr: Box<Expr>,
    pub next_expr: Box<Expr>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct Appl {
    pub func: Box<Expr>,
    pub arg: Box<Expr>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct IfElse {
    pub expr: Box<Expr>,
    pub case_true: Box<Expr>,
    pub case_false: Box<Expr>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct Match {
    pub expr: Box<Expr>,
    pub cases: Vec<MatchCase>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct MatchCase {
    pub pattern: Pattern,
    pub expr: Box<Expr>,
}

#[derive(Clone, PartialEq, Eq)]
pub enum Expr {
    Symbol((Span, Symbol)),
    Literal((Span, Literal)),
    Function((Span, Function)),
    Let((Span, Let)),
    Appl((Span, Appl)),
    IfElse((Span, IfElse)),
    Tuple((Span, Vec<Expr>)),
    Match((Span, Match)),
}

impl Expr {
    pub fn boxed(self) -> Box<Expr> {
        Box::new(self)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct SymbolBinding {
    pub bind: Symbol,
    pub type_: Option<TypeScheme>,
    pub expr: Expr,
}

#[derive(Clone, PartialEq, Eq)]
pub enum Statement {
    SymbolBinding((Span, SymbolBinding)),
    CustomType((Span, CustomTypeDefinition)),
}

#[derive(Clone, PartialEq, Eq)]
pub struct Module {
    pub statements: Vec<Statement>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntrinsicType {
    Bool,
    Int,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionType {
    pub arg: Type,
    pub return_: Type,
}

#[derive(Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct VariableType(pub String);

impl fmt::Debug for VariableType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug)]
pub struct VariableTypeGenerator {
    next: u32,
}
impl VariableTypeGenerator {
    pub fn new() -> Self {
        Self { next: 1 }
    }
    pub fn next(&mut self) -> VariableType {
        let id = self.next;
        self.next += 1;
        VariableType(format!("'{}", u32_to_ascii(id)))
    }
    pub fn next_scheme(&mut self) -> TypeScheme {
        TypeScheme {
            type_: Type::Var(self.next()),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CustomType {
    pub name: CustomTypeSymbol,
    pub variables: Vec<Type>,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    Intrinsic(IntrinsicType),
    Func(Box<FunctionType>),
    Var(VariableType),
    Tuple(Vec<Type>),
    Custom(CustomType),
}

impl Type {
    fn add_vars(&self, vars: &mut HashSet<VariableType>) {
        match self {
            Self::Var(x) => {
                vars.insert(x.clone());
            }
            Self::Tuple(xs) => {
                for x in xs {
                    x.add_vars(vars);
                }
            }
            Self::Func(x) => {
                x.arg.add_vars(vars);
                x.return_.add_vars(vars);
            }
            Self::Intrinsic(_) => {}
            Self::Custom(x) => {
                for v in &x.variables {
                    if let Type::Var(v) = v {
                        vars.insert(v.clone());
                    }
                }
            }
        }
    }
    pub fn vars(&self) -> HashSet<VariableType> {
        let mut vars: HashSet<_> = HashSet::new();
        self.add_vars(&mut vars);
        vars
    }
    fn replace(&mut self, replacement: &HashMap<VariableType, Type>) {
        match self {
            Self::Var(x) => {
                if let Some(next) = replacement.get(x).cloned() {
                    *self = next;
                }
            }
            Self::Tuple(xs) => {
                for x in xs.iter_mut() {
                    x.replace(replacement);
                }
            }
            Self::Func(x) => {
                x.arg.replace(replacement);
                x.return_.replace(replacement);
            }
            Self::Intrinsic(_) => {}
            Self::Custom(x) => {
                for v in x.variables.iter_mut() {
                    v.replace(replacement);
                }
            }
        }
    }

    pub fn generalize(self, gen: &mut VariableTypeGenerator) -> TypeScheme {
        let replacements: HashMap<VariableType, Type> = self
            .vars()
            .into_iter()
            .map(|from| (from, Type::Var(gen.next())))
            .collect();
        let mut t = self;
        t.replace(&replacements);
        TypeScheme { type_: t }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct TypeScheme {
    pub type_: Type,
}
impl TypeScheme {
    pub fn instantiate(&self, gen: &mut VariableTypeGenerator) -> Type {
        let replacements: HashMap<VariableType, Type> = self
            .type_
            .vars()
            .into_iter()
            .map(|v| (v, Type::Var(gen.next())))
            .collect();
        let mut t = self.type_.clone();
        t.replace(&replacements);
        t
    }
}

pub fn print_type(t: &Type) -> String {
    let mut printer = printer::Printer::new();
    printer.print_type(t);
    printer.output()
}

pub fn print_expr(e: &Expr) -> String {
    let mut printer = printer::Printer::new();
    printer.print_expr(e);
    printer.output()
}

pub fn print_module(p: &Module) -> String {
    let mut printer = printer::Printer::new();
    printer.print_module(&p);
    printer.output()
}
