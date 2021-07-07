use ast::*;

pub fn generate(module: &Module) -> String {
    let mut gen = Generator {
        out: PRELUDE.to_owned(),
        line_idx: 0,
        indent: 0,
        next_id: 1,
    };
    for st in &module.statements {
        match st {
            Statement::SymbolBinding((_, x)) => {
                gen.print(format!("const {} = ", x.bind.0));
                gen.generate_expr(&x.expr);
                gen.println(";");
            }
            Statement::CustomType((_, x)) => {
                for v in &x.variants {
                    gen.print(format!("const {} = ", v.constr.0));
                    if let Some(_) = &v.contained_type {
                        gen.print(format!("v => ({{ $: \"{}\", V: v }})", v.constr.0));
                    } else {
                        gen.print(format!("{{ $: \"{}\" }}", v.constr.0));
                    }
                    gen.println(";");
                }
            }
        };
    }
    gen.out
}

struct Generator {
    out: String,
    line_idx: usize,
    indent: usize,
    next_id: usize,
}

const PRELUDE: &'static str = "
const intrinsic_eq = x => x[0] === x[1];
const intrinsic_neq = x => x[0] !== x[1];
const intrinsic_gt = x => x[0] > x[1];
const intrinsic_gte = x => x[0] >= x[1];
const intrinsic_lt = x => x[0] < x[1];
const intrinsic_lte = x => x[0] <= x[1];
const intrinsic_add = x => x[0] + x[1];
const intrinsic_sub = x => x[0] - x[1];
const intrinsic_mul = x => x[0] * x[1];
const intrinsic_and = x => x[0] && x[1];
const intrinsic_or = x => x[0] || x[1];
const intrinsic_not = x => !x;
const intrinsic_print = x => {
    console.log(x);
    return x;
};
const intrinsic_println = x => {
    console.log(x);
    return x;
};
";

impl Generator {
    fn unpack_pattern<S: AsRef<str>>(&mut self, patt: &Pattern, id: S) {
        let id = id.as_ref();
        match patt {
            Pattern::Symbol(x) => {
                self.println(format!("const {} = {};", x.1 .0, id));
            }
            Pattern::Tuple(xs) => match &xs.1[..] {
                [x] => self.unpack_pattern(x, id),
                xs => {
                    for (idx, x) in xs.iter().enumerate() {
                        self.unpack_pattern(x, format!("{}[{}]", id, idx));
                    }
                }
            },
            Pattern::Variant(x) => {
                if let Some(contained_pattern) = &x.1.contained_pattern {
                    self.unpack_pattern(contained_pattern, format!("{}.V", id));
                }
            }
        }
    }

    fn pattern_matches<S: AsRef<str>>(&mut self, patt: &Pattern, id: S) {
        let id = id.as_ref();
        match patt {
            Pattern::Symbol(_) => self.print("true"),
            Pattern::Tuple(xs) => match &xs.1[..] {
                [x] => self.pattern_matches(x, id),
                xs => {
                    for x in xs.iter().take(1) {
                        self.pattern_matches(x, id);
                    }
                    for x in xs.iter().skip(1) {
                        self.print(" && ");
                        self.pattern_matches(x, id);
                    }
                }
            },
            Pattern::Variant(x) => {
                self.print(format!("{}.$ === \"{}\"", id, x.1.constr.0));
                if let Some(su) = &x.1.contained_pattern {
                    self.print(" && ");
                    self.pattern_matches(su, format!("{}.V", id));
                }
            }
        }
    }

    fn generate_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Appl((_, x)) => {
                self.generate_expr(&x.func);
                self.print("(");
                self.generate_expr(&x.arg);
                self.print(")");
            }
            Expr::Function((_, x)) => {
                let id = format!("$_{}", self.next_id);
                self.next_id += 1;
                self.print(format!("(({}) => ", id));
                self.enter_block();
                self.unpack_pattern(&x.bind, &id);
                self.print("return ");
                self.generate_expr(&x.expr);
                self.println(";");
                self.exit_block();
                self.print(")");
            }
            Expr::IfElse((_, x)) => {
                self.generate_expr(&x.expr);
                self.indent += 1;
                self.println("");
                self.print("? ");
                self.generate_expr(&x.case_true);
                self.print(": ");
                self.generate_expr(&x.case_false);
                self.indent -= 1;
            }
            Expr::Let((_, x)) => {
                let id = format!("$_{}", self.next_id);
                self.next_id += 1;
                self.print(format!("(({}) => ", id));
                self.enter_block();
                self.unpack_pattern(&x.bind, &id);
                self.print("return ");
                self.generate_expr(&x.next_expr);
                self.println(";");
                self.exit_block();
                self.print(")(");
                self.generate_expr(&x.bind_expr);
                self.print(")");
            }
            Expr::Literal((_, Literal::Bool(x))) => self.print(if *x { "true" } else { "false" }),
            Expr::Literal((_, Literal::Int(n))) => self.print(format!("{}", n)),
            Expr::Match((_, x)) => {
                let id = format!("$_{}", self.next_id);
                self.next_id += 1;
                self.print(format!("(({}) => ", id));
                self.enter_block();
                for c in &x.cases {
                    self.print("if (");
                    self.pattern_matches(&c.pattern, &id);
                    self.print(") ");
                    self.enter_block();
                    self.unpack_pattern(&c.pattern, &id);
                    self.print("return ");
                    self.generate_expr(&c.expr);
                    self.println(";");
                    self.exit_block();
                    self.println("");
                }
                self.println("throw new Error('Invariant violation: No match');");
                self.exit_block();
                self.print(")(");
                self.generate_expr(&x.expr);
                self.print(")");
            }
            Expr::Symbol((_, x)) => {
                self.print(&x.0);
            }
            Expr::Tuple((_, xs)) => match &xs[..] {
                [x] => self.generate_expr(x),
                xs => {
                    self.print("[");
                    for x in xs.iter().take(1) {
                        self.generate_expr(x);
                    }
                    for x in xs.iter().skip(1) {
                        self.print(", ");
                        self.generate_expr(x);
                    }
                    self.print("]");
                }
            },
            Expr::VariantConstr((_, x)) => {
                self.print(&x.constr.0);
                if let Some(y) = &x.value {
                    self.print("(");
                    self.generate_expr(&*y);
                    self.print(")");
                }
            }
        };
    }

    fn print<S: AsRef<str>>(&mut self, s: S) {
        if self.line_idx == 0 {
            let indent = self.indent * 2;
            self.out.push_str(&" ".repeat(indent));
            self.line_idx = indent;
        }
        self.out.push_str(s.as_ref())
    }
    fn println<S: AsRef<str>>(&mut self, s: S) {
        let s = s.as_ref();
        if s.len() != 0 {
            self.print(s);
        }
        self.out.push('\n');
        self.line_idx = 0;
    }

    fn enter_block(&mut self) {
        self.println("{");
        self.indent += 1;
    }

    fn exit_block(&mut self) {
        self.indent -= 1;
        self.print("}");
    }
}
