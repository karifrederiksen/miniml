use crate::*;
use std::collections::HashMap;

pub struct Printer {
    space_per_indent: usize,
    ind_level: usize,
    current_line_len: usize,
    text: String,
}

impl Printer {
    pub fn new() -> Self {
        Self {
            space_per_indent: 4,
            ind_level: 0,
            current_line_len: 0,
            text: String::new(),
        }
    }
    pub fn output(self) -> String {
        self.text
    }
    pub fn print_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Literal((_, x)) => {
                let s = match x {
                    Literal::Bool(true) => "True".to_owned(),
                    Literal::Bool(false) => "False".to_owned(),
                    Literal::Int(n) => format!("{}", n),
                };
                self.str(&s);
            }
            Expr::Symbol((_, x)) => {
                self.str(&x.0);
            }
            Expr::Appl((_, x)) => {
                self.print_expr(&*x.func);
                self.space();
                self.print_expr(&*x.arg);
            }
            Expr::IfElse((_, x)) => {
                self.str("if");
                self.space();
                self.print_expr(&*x.expr);
                self.space();
                self.str("then");
                self.indent_incr();
                self.print_expr(&*x.case_true);
                self.indent_decr();
                self.str("else");
                self.indent_incr();
                self.print_expr(&*x.case_false);
                self.indent_decr();
            }
            Expr::Tuple((_, x)) => {
                self.str("(");
                for x in x.iter().take(1) {
                    self.print_expr(x);
                }
                for x in x.iter().skip(1) {
                    self.str(",");
                    self.space();
                    self.print_expr(x);
                }
                self.str(")");
            }
            Expr::Let((_, x)) => {
                self.str("let");
                self.space();
                self.print_pattern(&x.bind);
                self.space();
                self.str("=");
                self.indent_incr();
                self.print_expr(&x.bind_expr);
                self.indent_decr();
                self.str("in");
                self.newline();
                self.print_expr(&x.next_expr);
            }
            Expr::Function((_, x)) => {
                self.str("(fn");
                self.space();
                self.print_pattern(&x.bind);
                self.space();
                self.str("->");
                self.indent_incr();
                self.print_expr(&x.expr);
                self.indent_decr();
                self.str(")");
            }
            Expr::Match((_, x)) => {
                self.str("match ");
                self.print_expr(&*x.expr);
                for c in &x.cases {
                    self.newline();
                    self.str("|");
                    self.space();
                    self.print_pattern(&c.pattern);
                    self.space();
                    self.str("->");
                    self.space();
                    self.print_expr(&c.expr);
                }
            }
        }
    }
    pub fn print_statement(&mut self, st: &Statement) {
        match st {
            Statement::SymbolBinding(st) => {
                let decl_sym = if st.1.recursive { "rec" } else { "let" };
                if let Some(type_) = &st.1.type_ {
                    self.str(decl_sym);
                    self.space();
                    self.str(&st.1.bind.0);
                    self.space();
                    self.str(":");
                    self.space();
                    self.print_type_scheme(type_);
                    self.newline();
                }
                self.str(decl_sym);
                self.space();
                self.str(&st.1.bind.0);
                self.space();
                self.str("=");
                self.space();
                self.print_expr(&st.1.expr);
            }
            Statement::CustomType((_, d)) => {
                self.str("type");
                self.space();
                // TODO: clean this up
                self.print_type(&Type::Custom(d.type_.clone()));
                self.indent_incr();
                for v in d.variants.iter().take(1) {
                    self.newline();
                    self.str("=");
                    self.space();
                    if let Some(t) = &v.contained_type {
                        self.str("(");
                        self.str(&v.constr.0);
                        self.space();
                        self.print_type(t);
                        self.str(")");
                    } else {
                        self.str(&v.constr.0);
                    }
                }
                for v in d.variants.iter().skip(1) {
                    self.newline();
                    self.str("|");
                    self.space();
                    if let Some(t) = &v.contained_type {
                        self.str("(");
                        self.str(&v.constr.0);
                        self.space();
                        self.print_type(t);
                        self.str(")");
                    } else {
                        self.str(&v.constr.0);
                    }
                }
                self.indent_decr();
            }
        }
    }
    pub fn print_module(&mut self, module: &Module) {
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
    fn str<S: AsRef<str>>(&mut self, s: S) {
        if self.current_line_len == 0 && self.text.len() != 0 {
            self.text.push('\n');
            let ind = " ".repeat(self.ind_level * self.space_per_indent);
            self.current_line_len += ind.len();
            self.text.push_str(&ind);
        }
        let s = s.as_ref();
        self.text.push_str(s);
        self.current_line_len += s.len();
    }
    pub fn print_pattern(&mut self, pat: &Pattern) {
        match pat {
            Pattern::Symbol((_, s)) => {
                self.str(&s.0);
            }
            Pattern::Tuple((_, xs)) => {
                self.str("(");
                for x in xs.iter().take(1) {
                    self.print_pattern(x);
                }
                for x in xs.iter().skip(1) {
                    self.str(",");
                    self.space();
                    self.print_pattern(x);
                }
                self.str(")");
            }
            Pattern::Variant((_, x)) => {
                if let Some(box contained) = &x.contained_pattern {
                    self.str("(");
                    self.str(&x.constr.0);
                    self.space();
                    self.print_pattern(contained);
                    self.str(")");
                } else {
                    self.str(&x.constr.0);
                }
            }
        }
    }

    pub fn print_type(&mut self, ty: &Type) {
        match ty {
            Type::Intrinsic(IntrinsicType::Bool) => {
                self.str("Bool");
            }
            Type::Intrinsic(IntrinsicType::Int) => {
                self.str("Int");
            }
            Type::Custom(x) => {
                if !x.variables.is_empty() {
                    self.str("(");
                    self.indent_incr();
                    self.str(&x.name.0);
                    for v in &x.variables {
                        self.space();
                        self.print_type(v);
                    }
                    self.indent_decr();
                    self.str(")");
                } else {
                    self.str(&x.name.0);
                }
            }
            Type::Var(x) => {
                self.str(&x.0);
            }
            Type::Tuple(xs) => {
                self.str("(");
                self.indent_incr();
                for x in xs.iter().take(1) {
                    self.print_type(x);
                }
                for x in xs.iter().skip(1) {
                    self.str(",");
                    self.space();
                    self.print_type(x);
                }
                self.indent_decr();
                self.str(")");
            }
            Type::Func(box f) => {
                self.str("(");
                self.print_type(&f.arg);
                self.space();
                self.str("->");
                self.space();
                self.print_type(&f.return_);
                self.str(")");
            }
        }
    }
    pub fn print_type_scheme(&mut self, ty: &TypeScheme) {
        let vars = ty.type_.vars();
        if vars.is_empty() {
            self.print_type(&ty.type_);
        } else {
            let replacements: Vec<(VariableType, Type)> = vars
                .into_iter()
                .enumerate()
                .map(|(n, key)| (key, Type::Var(VariableType(u32_to_ascii((n + 1) as u32)))))
                .collect();
            self.str("forall");
            self.space();
            for (_, v) in replacements.iter().take(1) {
                self.print_type(v);
            }
            for (_, v) in replacements.iter().skip(1) {
                self.str(",");
                self.space();
                self.print_type(v);
            }
            let mut t = ty.type_.clone();
            let replacements: HashMap<VariableType, Type> = replacements.into_iter().collect();
            t.replace(&replacements);
            self.space();
            self.str(".");
            self.space();
            self.print_type(&t);
        }
    }
}
