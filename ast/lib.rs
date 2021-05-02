use prelude::*;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Literal {
    Bool(bool),
    Int(i128),
}

impl fmt::Debug for Literal {
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

#[derive(Clone, PartialEq, Eq)]
pub struct TuplePattern(pub Vec<Pattern>);

impl fmt::Debug for TuplePattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for e in self.0.iter().take(1) {
            write!(f, "{:?}", e)?;
        }
        for e in self.0.iter().skip(1) {
            write!(f, ", {:?}", e)?;
        }
        write!(f, ")")
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct VariantDefinition {
    pub constr: Symbol,
    pub contained_type: Option<Type>,
}
impl fmt::Debug for VariantDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.constr)?;
        if let Some(contained_type) = &self.contained_type {
            write!(f, " {:?}", contained_type)?;
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Variant {
    pub constr: Symbol,
    pub value: Option<Box<Expr>>,
}
impl fmt::Debug for Variant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.constr)?;
        if let Some(val) = &self.value {
            write!(f, " {:?}", val)?;
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct CustomTypeSymbol(pub String);

impl fmt::Debug for CustomTypeSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct CustomTypeDefinition {
    pub type_: CustomType,
    pub variants: Vec<VariantDefinition>,
}
impl fmt::Debug for CustomTypeDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "type {:?}", self.type_)?;
        for v in self.variants.iter().take(1) {
            writeln!(f, "    = {:?}", v)?;
        }
        for v in self.variants.iter().skip(1) {
            writeln!(f, "    | {:?}", v)?;
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct VariantPattern {
    pub constr: Symbol,
    pub contained_pattern: Option<Box<Pattern>>,
}

impl fmt::Debug for VariantPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.constr)?;
        if let Some(contained_pattern) = &self.contained_pattern {
            write!(f, " {:?}", contained_pattern)?;
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Pattern {
    Symbol(Symbol),
    Tuple(TuplePattern),
    Variant(VariantPattern),
}
impl fmt::Debug for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Symbol(x) => write!(f, "{:?}", x),
            Self::Tuple(x) => write!(f, "{:?}", x),
            Self::Variant(x) => write!(f, "{:?}", x),
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

#[derive(Clone, PartialEq, Eq)]
pub struct Function {
    pub bind: Pattern,
    pub expr: Box<Expr>,
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(\\{:?} -> {:?})", self.bind, self.expr)
    }
}

impl Function {
    pub fn replace_symbols(&mut self, symbols: &HashMap<Symbol, Expr>) {
        Self::replace_bound_expr(&mut self.expr, symbols);
    }

    fn replace_bound_expr(e: &mut Expr, symbols: &HashMap<Symbol, Expr>) {
        match e {
            Expr::Symbol(x) => {
                if let Some(val) = symbols.get(x) {
                    *e = val.clone();
                }
            }
            Expr::VariantConstr(x) => {
                if let Some(val) = &mut x.value {
                    Self::replace_bound_expr(val, symbols);
                }
            }
            Expr::Literal(_) => (),
            Expr::Function(x) => {
                Self::replace_bound_expr(&mut x.expr, symbols);
            }
            Expr::Let(x) => {
                Self::replace_bound_expr(&mut x.bind_expr, symbols);
                Self::replace_bound_expr(&mut x.next_expr, symbols);
            }
            Expr::Appl(x) => {
                Self::replace_bound_expr(&mut x.arg, symbols);
                Self::replace_bound_expr(&mut x.func, symbols);
            }
            Expr::IfElse(x) => {
                Self::replace_bound_expr(&mut x.expr, symbols);
                Self::replace_bound_expr(&mut x.case_true, symbols);
                Self::replace_bound_expr(&mut x.case_false, symbols);
            }
            Expr::Tuple(x) => {
                for e in x.0.iter_mut() {
                    Self::replace_bound_expr(e, symbols);
                }
            }
            Expr::Match(x) => {
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
    pub recursive: bool,
    pub bind: Pattern,
    pub bind_expr: Box<Expr>,
    pub next_expr: Box<Expr>,
}

impl fmt::Debug for Let {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {:?} = {:?} in {:?}",
            (if self.recursive { "rec" } else { "let" }),
            self.bind,
            self.bind_expr,
            self.next_expr
        )
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Appl {
    pub func: Box<Expr>,
    pub arg: Box<Expr>,
}

impl fmt::Debug for Appl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({:?} {:?})", self.func, self.arg)?;
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct IfElse {
    pub expr: Box<Expr>,
    pub case_true: Box<Expr>,
    pub case_false: Box<Expr>,
}

impl fmt::Debug for IfElse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "if {:?} then {:?} else {:?}",
            self.expr, self.case_true, self.case_false
        )
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Tuple(pub Vec<Expr>);

impl fmt::Debug for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for e in self.0.iter().take(1) {
            write!(f, "{:?}", e)?;
        }
        for e in self.0.iter().skip(1) {
            write!(f, ", {:?}", e)?;
        }
        write!(f, ")")
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Match {
    pub expr: Box<Expr>,
    pub cases: Vec<MatchCase>,
}
impl fmt::Debug for Match {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "match {:?} with", self.expr)?;
        for c in self.cases.iter().take(1) {
            write!(f, "{:?} -> {:?}", c.pattern, c.expr)?;
        }
        for c in self.cases.iter().skip(1) {
            write!(f, ", {:?} -> {:?}", c.pattern, c.expr)?;
        }
        write!(f, ")")
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct MatchCase {
    pub pattern: Pattern,
    pub expr: Box<Expr>,
}

#[derive(Clone, PartialEq, Eq)]
pub enum Expr {
    Symbol(Symbol),
    VariantConstr(Variant),
    Literal(Literal),
    Function(Function),
    Let(Let),
    Appl(Appl),
    IfElse(IfElse),
    Tuple(Tuple),
    Match(Match),
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Symbol(x) => {
                write!(f, "{:?}", x)
            }
            Self::VariantConstr(x) => {
                write!(f, "{:?}", x.constr)?;
                if let Some(arg) = &x.value {
                    write!(f, " {:?}", arg)?;
                }
                Ok(())
            }
            Self::Literal(x) => {
                write!(f, "{:?}", x)
            }
            Self::Function(x) => {
                write!(f, "{:?}", x)
            }
            Self::Let(x) => {
                write!(f, "{:?}", x)
            }
            Self::Appl(x) => {
                write!(f, "{:?}", x)
            }
            Self::IfElse(x) => {
                write!(f, "{:?}", x)
            }
            Self::Tuple(x) => {
                write!(f, "{:?}", x)
            }
            Self::Match(x) => {
                write!(f, "{:?}", x)
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct SymbolBinding {
    pub recursive: bool,
    pub bind: Symbol,
    pub type_: Option<TypeScheme>,
    pub expr: Expr,
}
#[derive(Clone, PartialEq, Eq)]
pub enum Statement {
    SymbolBinding(SymbolBinding),
    CustomType(CustomTypeDefinition),
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

impl fmt::Debug for IntrinsicType {
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

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionType {
    pub arg: Type,
    pub return_: Type,
}

impl fmt::Debug for FunctionType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({:?} -> {:?})", self.arg, self.return_)
    }
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
pub struct TupleType(pub Vec<Type>);

impl fmt::Debug for TupleType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for e in self.0.iter().take(1) {
            write!(f, "{:?}", e)?;
        }
        for e in self.0.iter().skip(1) {
            write!(f, ", {:?}", e)?;
        }
        write!(f, ")")
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CustomType {
    pub name: CustomTypeSymbol,
    pub variables: Vec<Type>,
}
impl fmt::Debug for CustomType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.name)?;
        if !self.variables.is_empty() {
            for v in &self.variables {
                write!(f, " {:?}", v)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    Intrinsic(IntrinsicType),
    Func(Box<FunctionType>),
    Var(VariableType),
    Tuple(TupleType),
    Custom(CustomType),
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Intrinsic(x) => write!(f, "{:?}", x),
            Self::Func(x) => write!(f, "{:?}", x),
            Self::Var(x) => write!(f, "{:?}", x),
            Self::Tuple(x) => write!(f, "{:?}", x),
            Self::Custom(x) => write!(f, "{:?}", x),
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

#[derive(Clone, PartialEq, Eq)]
pub struct TypeScheme {
    pub type_: Type,
}

impl fmt::Debug for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vars = self.type_.vars();
        if !vars.is_empty() {
            let replacements: Vec<(VariableType, Type)> = vars
                .into_iter()
                .enumerate()
                .map(|(n, key)| (key, Type::Var(VariableType(u32_to_ascii((n + 1) as u32)))))
                .collect();
            write!(f, "forall ")?;
            for (_, v) in &replacements {
                write!(f, "{:?} ", v)?;
            }
            let mut t = self.type_.clone();
            let replacements: HashMap<VariableType, Type> = replacements.into_iter().collect();
            t.replace(&replacements);
            write!(f, "=> {:?}", t)
        } else {
            write!(f, "{:?}", self.type_)
        }
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
                let s = match x {
                    Literal::Bool(true) => "True".to_owned(),
                    Literal::Bool(false) => "False".to_owned(),
                    Literal::Int(n) => format!("{}", n),
                };
                self.print_str(&s);
            }
            Expr::Symbol(x) => {
                self.print_str(&x.0);
            }
            Expr::VariantConstr(x) => {
                self.print_str(&x.constr.0);
                if let Some(arg) = &x.value {
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

                self.print_str(&format!("{:?}", x.bind));
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
                self.print_str(&format!("{:?}", x.bind));
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
                    self.print_str(&format!("{:?}", c.pattern));
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
    fn print_statement(&mut self, st: &Statement) {
        match st {
            Statement::SymbolBinding(st) => {
                let decl_sym = if st.recursive { "rec" } else { "let" };
                if let Some(type_) = &st.type_ {
                    self.print_str(decl_sym);
                    self.space();
                    self.print_str(&st.bind.0);
                    self.space();
                    self.print_str(":");
                    self.space();
                    self.print_str(&format!("{:?}", type_));
                    self.newline();
                }
                self.print_str(decl_sym);
                self.space();
                self.print_str(&st.bind.0);
                self.space();
                self.print_str("=");
                self.space();
                self.print(&st.expr);
            }
            Statement::CustomType(t) => {
                self.print_str(&format!("{:?}", t));
            }
        }
    }
    fn print_module(&mut self, module: &Module) {
        for st in &module.statements {
            self.print_statement(&st);
            self.newline();
            self.force_newline();
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
    fn force_newline(&mut self) {
        self.text.push('\n');
        self.current_line_len = 0;
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
    let mut printer = Printer::new();
    printer.print_module(&p);
    printer.text
}
