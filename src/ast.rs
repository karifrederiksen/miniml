use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Literal {
    Bool(bool),
    Int(i128),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(true) => {
                write!(f, "True")
            }
            Self::Bool(false) => {
                write!(f, "False")
            }
            Self::Int(x) => {
                write!(f, "{}", x)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TuplePattern(pub Vec<Pattern>);

impl fmt::Display for TuplePattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for e in self.0.iter().take(1) {
            write!(f, "{}", e)?;
        }
        for e in self.0.iter().skip(1) {
            write!(f, ", {}", e)?;
        }
        write!(f, ")")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantDefinition {
    pub constr: Symbol,
    pub contained_type: Option<Type>,
}
impl fmt::Display for VariantDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.constr)?;
        if let Some(contained_type) = &self.contained_type {
            write!(f, " {}", contained_type)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variant {
    pub constr: Symbol,
    pub value: Option<Expr>,
}
impl fmt::Display for Variant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.constr)?;
        if let Some(val) = &self.value {
            write!(f, " {}", val)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct CustomTypeSymbol(pub String);

impl fmt::Display for CustomTypeSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CustomTypeDefinition {
    pub type_: CustomType,
    pub variants: Vec<VariantDefinition>,
}
impl fmt::Display for CustomTypeDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "type {}", self.type_)?;
        for v in self.variants.iter().take(1) {
            writeln!(f, "    = {}", v)?;
        }
        for v in self.variants.iter().skip(1) {
            writeln!(f, "    | {}", v)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantPattern {
    pub constr: Symbol,
    pub contained_pattern: Option<Box<Pattern>>,
}

impl fmt::Display for VariantPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.constr)?;
        if let Some(contained_pattern) = &self.contained_pattern {
            write!(f, "{}", contained_pattern)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Symbol(Symbol),
    Tuple(TuplePattern),
    Variant(VariantPattern),
}
impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Symbol(x) => write!(f, "{}", x),
            Self::Tuple(x) => write!(f, "{}", x),
            Self::Variant(x) => write!(f, "{}", x),
        }
    }
}
impl Pattern {
    pub fn contains(&self, s: &Symbol) -> bool {
        match self {
            Self::Symbol(x) => x == s,
            Self::Tuple(ts) => ts.0.iter().any(|x| x.contains(s)),
            Self::Variant(v) => match &v.contained_pattern {
                None => false,
                Some(x) => x.contains(s),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub bind: Pattern,
    pub expr: Box<Expr>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(\\{} -> {})", self.bind, self.expr)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Let {
    pub recursive: bool,
    pub bind: Pattern,
    pub bind_expr: Box<Expr>,
    pub next_expr: Box<Expr>,
}

impl fmt::Display for Let {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} = {} in {}",
            (if self.recursive { "rec" } else { "let" }),
            self.bind,
            self.bind_expr,
            self.next_expr
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Appl {
    pub func: Box<Expr>,
    pub arg: Box<Expr>,
}

impl fmt::Display for Appl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.func, self.arg)?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfElse {
    pub expr: Box<Expr>,
    pub case_true: Box<Expr>,
    pub case_false: Box<Expr>,
}

impl fmt::Display for IfElse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "if {} then {} else {}",
            self.expr, self.case_true, self.case_false
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tuple(pub Vec<Expr>);
impl fmt::Display for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for e in self.0.iter().take(1) {
            write!(f, "{}", e)?;
        }
        for e in self.0.iter().skip(1) {
            write!(f, ", {}", e)?;
        }
        write!(f, ")")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Match {
    pub expr: Box<Expr>,
    pub cases: Vec<MatchCase>,
}
impl fmt::Display for Match {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "match {} with", self.expr)?;
        for c in self.cases.iter().take(1) {
            write!(f, "{} -> {}", c.pattern, c.expr)?;
        }
        for c in self.cases.iter().skip(1) {
            write!(f, ", {} -> {}", c.pattern, c.expr)?;
        }
        write!(f, ")")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchCase {
    pub pattern: Pattern,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Symbol(Symbol),
    VariantConstr((Symbol, Option<Box<Expr>>)),
    Literal(Literal),
    Function(Function),
    Let(Let),
    Appl(Appl),
    IfElse(IfElse),
    Tuple(Tuple),
    Match(Match),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Symbol(x) => {
                write!(f, "{}", x)
            }
            Self::VariantConstr((x, arg)) => {
                write!(f, "{}", x)?;
                if let Some(arg) = arg {
                    write!(f, " {}", arg)?;
                }
                Ok(())
            }
            Self::Literal(x) => {
                write!(f, "{}", x)
            }
            Self::Function(x) => {
                write!(f, "{}", x)
            }
            Self::Let(x) => {
                write!(f, "{}", x)
            }
            Self::Appl(x) => {
                write!(f, "{}", x)
            }
            Self::IfElse(x) => {
                write!(f, "{}", x)
            }
            Self::Tuple(x) => {
                write!(f, "{}", x)
            }
            Self::Match(x) => {
                write!(f, "{}", x)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetStatement {
    pub recursive: bool,
    pub bind: Symbol,
    pub expr: Expr,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Let(LetStatement),
    Type(CustomTypeDefinition),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    pub statements: Vec<Statement>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntrinsicType {
    Bool,
    Int,
}

impl fmt::Display for IntrinsicType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => {
                write!(f, "Bool")
            }
            Self::Int => {
                write!(f, "Int")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionType {
    pub arg: Type,
    pub return_: Type,
}

impl fmt::Display for FunctionType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} -> {})", self.arg, self.return_)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct VariableType(pub String);

impl fmt::Display for VariableType {
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TupleType(pub Vec<Type>);

impl fmt::Display for TupleType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for e in self.0.iter().take(1) {
            write!(f, "{}", e)?;
        }
        for e in self.0.iter().skip(1) {
            write!(f, ", {}", e)?;
        }
        write!(f, ")")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CustomType {
    pub name: CustomTypeSymbol,
    pub variables: Vec<Type>,
}
impl fmt::Display for CustomType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        if !self.variables.is_empty() {
            for v in &self.variables {
                write!(f, " {}", v)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    Intrinsic(IntrinsicType),
    Func(Box<FunctionType>),
    Var(VariableType),
    Tuple(TupleType),
    Custom(CustomType),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Intrinsic(x) => write!(f, "{}", x),
            Self::Func(x) => write!(f, "{}", x),
            Self::Var(x) => write!(f, "{}", x),
            Self::Tuple(x) => write!(f, "{}", x),
            Self::Custom(x) => write!(f, "{}", x),
        }
    }
}

impl Type {
    fn add_vars(&self, vars: &mut HashSet<VariableType>) {
        match self {
            Self::Var(x) => {
                vars.insert(x.clone());
            }
            Self::Tuple(xs) => {
                for x in &xs.0 {
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
                for x in xs.0.iter_mut() {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeScheme {
    pub type_: Type,
}

impl fmt::Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vars = self.type_.vars();
        if !vars.is_empty() {
            write!(f, "forall ")?;
            for v in vars.into_iter() {
                write!(f, "{} ", v)?;
            }
            write!(f, "=> ")?;
        }
        write!(f, "{}", self.type_)
    }
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

struct Printer {
    space_per_indent: usize,
    ind_level: usize,
    current_line_len: usize,
    text: String,
}

enum PrintToken {
    Space,
    IndentIncr,
    IndentDecl,
    Newline,
    Text(String),
}

impl Printer {
    fn new() -> Self {
        Self {
            space_per_indent: 4,
            ind_level: 0,
            current_line_len: 0,
            text: String::new(),
        }
    }
    fn print(&mut self, expr: &Expr) {
        match expr {
            Expr::Literal(x) => {
                let s = format!("{}", x);
                self.print_str(&s);
            }
            Expr::Symbol(x) => {
                self.print_str(&x.0);
            }
            Expr::VariantConstr((x, arg)) => {
                self.print_str(&x.0);
                if let Some(arg) = arg {
                    self.space();
                    self.print(arg);
                }
            }
            Expr::Appl(x) => {
                self.print_str("(");
                self.print(&*x.func);
                self.space();
                self.print(&*x.arg);
                self.print_str(")");
            }
            Expr::IfElse(x) => {
                self.print_str("if");
                self.space();
                self.print(&*x.expr);
                self.space();
                self.print_str("then");
                self.indent_incr();
                self.print(&*x.case_true);
                self.indent_decr();
                self.print_str("else");
                self.indent_incr();
                self.print(&*x.case_false);
                self.indent_decr();
            }
            Expr::Tuple(x) => {
                self.print_str("(");
                for x in x.0.iter().take(1) {
                    self.print(x);
                }
                for x in x.0.iter().skip(1) {
                    self.print_str(", ");
                    self.print(x);
                }
                self.print_str(")");
            }
            Expr::Let(x) => {
                if x.recursive {
                    self.print_str("letrec");
                } else {
                    self.print_str("let");
                }
                self.space();

                self.print_str(&format!("{}", x.bind));
                self.space();
                self.print_str("=");
                self.indent_incr();
                self.print(&x.bind_expr);
                self.indent_decr();
                self.print_str("in");
                self.newline();
                self.print(&x.next_expr);
            }
            Expr::Function(x) => {
                self.print_str("(\\");
                self.print_str(&format!("{}", x.bind));
                self.space();
                self.print_str("->");
                self.indent_incr();
                self.print(&x.expr);
                self.indent_decr();
                self.print_str(")");
            }
            Expr::Match(x) => {
                self.print_str("match ");
                self.print(&*x.expr);
                self.print_str(" with");
                self.indent_incr();
                for c in &x.cases {
                    self.print_str(&format!("{}", c.pattern));
                    self.space();
                    self.print_str("->");
                    self.space();
                    self.print(&c.expr);
                    self.print_str(",");
                    self.newline();
                }
                self.indent_decr();
            }
        }
    }
    fn indent_incr(&mut self) {
        self.ind_level += 1;
        self.newline();
    }
    fn indent_decr(&mut self) {
        self.ind_level -= 1;
        self.newline();
    }
    fn newline(&mut self) {
        self.current_line_len = 0;
    }
    fn space(&mut self) {
        self.text.push(' ');
        self.current_line_len += 1;
    }
    fn print_str(&mut self, s: &str) {
        if self.current_line_len == 0 && self.text.len() != 0 {
            self.text.push('\n');
            let ind = " ".repeat(self.ind_level * self.space_per_indent);
            self.current_line_len += ind.len();
            self.text.push_str(&ind);
        }
        self.text.push_str(&s);
        self.current_line_len += s.len();
    }
}

pub fn print_expr(e: &Expr) -> String {
    let mut printer = Printer::new();
    printer.print(e);
    printer.text
}

pub fn print_module(p: &Module) -> String {
    let mut s = String::new();
    for st in &p.statements {
        let mut printer = Printer::new();
        match st {
            Statement::Let(st) => {
                printer.print(&st.expr);
                if st.recursive {
                    s.push_str("rec");
                } else {
                    s.push_str("let");
                }
                s.push_str(&format!(" {} = {}\n\n", &st.bind, &printer.text));
            }
            Statement::Type(t) => {
                s.push_str(&format!("{}\n", t));
            }
        }
    }
    s
}
