#![feature(iter_intersperse)]
#![feature(box_patterns)]
#[allow(dead_code)]
mod lexer;
use ast as a;
use lexer::*;
use prelude::*;

// Use the bottom-up method

type Idx = u32;

#[derive(Debug)]
enum Error {
    B(String),
}

fn err<A: Into<String>>(s: A) -> Error {
    Error::B(s.into())
}

fn err2<A: Into<String>>(s: A, s2: &[Token]) -> Error {
    let rest: String = s2.iter().map(|x| x.to_string()).collect();
    Error::B(format!("{}\n{}", s.into(), rest))
}

type IResult<I, O> = Result<(I, O), Error>;

fn expr_function(s: &[Token]) -> IResult<&[Token], (Idx, a::Function)> {
    let s = trivia0(s);
    let (s, (_, p)) = pattern(s)?;
    let s = trivia0(s);
    let s = match s {
        [Token::ArrowSkinny(_), rest @ ..] => rest,
        _ => return Err(err("Unexpected token")),
    };
    let s = trivia0(s);
    let (s, (end, e)) = expr(s)?;
    let f = a::Function {
        bind: p,
        expr: e.boxed(),
    };
    Ok((s, (end.end, f)))
}

fn token_symbol_lower(s: &[Token]) -> IResult<&[Token], (Span, Symbol)> {
    match s {
        [Token::SymbolLower(box (range, x)), rest @ ..] => Ok((rest, (range.clone(), x.clone()))),
        _ => Err(err("token_symbol_lower")),
    }
}

fn token_symbol_upper(s: &[Token]) -> IResult<&[Token], (Span, Symbol)> {
    match s {
        [Token::SymbolUpper(box (range, x)), rest @ ..] => Ok((rest, (range.clone(), x.clone()))),
        _ => Err(err("token_symbol_upper")),
    }
}

fn trivia0_except_newline(s: &[Token]) -> &[Token] {
    let mut s = s;
    loop {
        s = match s {
            [Token::Space(_) | Token::Comment(_), rest @ ..] => rest,
            _ => break,
        };
    }
    s
}

fn trivia0(s: &[Token]) -> &[Token] {
    let mut s = s;
    loop {
        s = match s {
            [Token::Newline(_) | Token::Space(_) | Token::Comment(_), rest @ ..] => rest,
            _ => break,
        };
    }
    s
}

fn trivia1(s: &[Token]) -> IResult<&[Token], ()> {
    match s {
        [Token::Newline(_) | Token::Space(_) | Token::Comment(_), rest @ ..] => {
            Ok((trivia0(rest), ()))
        }
        _ => Err(err("unexpected token. expected 1 or more trivia")),
    }
}

fn pattern_variant(
    constr: Symbol,
    start: Span,
    s: &[Token],
) -> IResult<&[Token], (Span, a::VariantPattern)> {
    if let Ok((s, ())) = trivia1(s) {
        if let Ok((s, (end, pat))) = pattern(s) {
            let range = Span {
                start: start.start,
                end: end.end,
            };
            let var = a::VariantPattern {
                constr,
                contained_pattern: Some(Box::new(pat)),
            };
            return Ok((s, (range, var)));
        }
    }
    return Ok((
        s,
        (
            start,
            a::VariantPattern {
                constr,
                contained_pattern: None,
            },
        ),
    ));
}

fn pattern_tuple(s: &[Token]) -> IResult<&[Token], (Idx, Vec<a::Pattern>)> {
    let s = trivia0(s);
    if let [Token::RParens(end), s @ ..] = s {
        return Ok((s, (end.end, vec![])));
    }
    let (s, (_, first_pat)) = pattern(s)?;
    let mut patterns = vec![first_pat];
    let mut s = s;
    let end = loop {
        let s_ = trivia0(s);
        let s_ = match s_ {
            [Token::RParens(end), s_ @ ..] => {
                s = s_;
                break end.end;
            }
            [Token::Comma(_), s @ ..] => s,
            _ => return Err(err("pattern_tuple: missing comma")),
        };
        let s_ = trivia0(s_);
        let (s_, (_, pat)) = pattern(s_)?;
        s = s_;
        patterns.push(pat);
    };
    Ok((s, (end, patterns)))
}

fn pattern(s: &[Token]) -> IResult<&[Token], (Span, a::Pattern)> {
    match s {
        [Token::SymbolLower(box (range, sym)), s @ ..] => {
            let p = a::Pattern::Symbol((range.clone(), sym.clone()));
            Ok((s, (range.clone(), p)))
        }
        [Token::LParens(start), s @ ..] => {
            let (s, (end, x)) = pattern_tuple(s)?;
            let range = Span {
                start: start.start,
                end,
            };
            Ok((s, (range.clone(), a::Pattern::Tuple((range, x)))))
        }
        [Token::SymbolUpper(box (start, constr)), s @ ..] => {
            let (s, x) = pattern_variant(constr.clone(), start.clone(), s)?;
            Ok((s, (x.0.clone(), a::Pattern::Variant(x))))
        }
        _ => Err(err("pattern")),
    }
}

fn expr_tuple(s: &[Token]) -> IResult<&[Token], (Idx, Vec<a::Expr>)> {
    let s = trivia0(s);
    if let [Token::RParens(end), s @ ..] = s {
        return Ok((s, (end.end, vec![])));
    }
    let (s, (_, first_expr)) = expr(s)?;
    let mut exprs = vec![first_expr];
    let mut s = s;
    let end = loop {
        let s_ = trivia0(s);
        let s_ = match s_ {
            [Token::RParens(end), s_ @ ..] => {
                s = s_;
                break end.end;
            }
            [Token::Comma(_), s @ ..] => s,
            _ => return Err(err("expr_tuple: missing comma")),
        };
        let s_ = trivia0(s_);
        let (s_, (_, e)) = expr(s_)?;
        s = s_;
        exprs.push(e);
    };
    Ok((s, (end, exprs)))
}

fn expr_match(s: &[Token]) -> IResult<&[Token], (Idx, a::Match)> {
    let (s, ()) = trivia1(s)?;
    let (s, (_, e)) = expr(s)?;
    let (s, ()) = trivia1(s)?;
    let mut branches = Vec::new();
    let (s, end) = {
        let mut end = Span::default();
        let mut s = s;
        loop {
            let s_ = trivia0(s);
            let s_ = match s_ {
                [Token::VerticalBar(_), rest @ ..] => rest,
                _ => break,
            };
            let (s_, (end_, branch)) = match_branch(s_)?;
            branches.push(branch);
            s = s_;
            end = end_;
        }
        (s, end)
    };
    Ok((
        s,
        (
            end.end,
            a::Match {
                expr: e.boxed(),
                cases: branches,
            },
        ),
    ))
}

fn match_branch(s: &[Token]) -> IResult<&[Token], (Span, a::MatchCase)> {
    let s = trivia0(s);
    let (s, (_, pat)) = pattern(s)?;
    let s = trivia0(s);
    let s = match s {
        [Token::ArrowSkinny(_), rest @ ..] => rest,
        _ => return Err(err("expected '->', found something else")),
    };
    let s = trivia0(s);
    let (s, (end, e)) = expr(s)?;
    Ok((
        s,
        (
            end,
            a::MatchCase {
                pattern: pat,
                expr: e.boxed(),
            },
        ),
    ))
}

fn expr_let(s: &[Token]) -> IResult<&[Token], (Idx, a::Let)> {
    let (s, (_, bind)) = pattern(s)?;
    let s = match s {
        [Token::Equals(_), rest @ ..] => rest,
        _ => return Err(err("expected '=', found something else")),
    };
    let (s, (_, bind_expr)) = expr(s)?;
    let s = match s {
        [Token::In(_), rest @ ..] => rest,
        _ => return Err(err("expected 'in', found something else")),
    };
    let (s, (end, next_expr)) = expr(s)?;
    let val = a::Let {
        bind: bind,
        bind_expr: bind_expr.boxed(),
        next_expr: next_expr.boxed(),
    };
    Ok((s, (end.end, val)))
}

fn expr_if(s: &[Token]) -> IResult<&[Token], (Idx, a::IfElse)> {
    let (s, ()) = trivia1(s)?;
    let (s, (_, cond)) = expr(s)?;
    let (s, ()) = trivia1(s)?;
    let s = match s {
        [Token::Then(_), rest @ ..] => rest,
        _ => return Err(err("expected 'then', found something else")),
    };
    let (s, ()) = trivia1(s)?;
    let (s, (_, case_true)) = expr(s)?;
    let (s, ()) = trivia1(s)?;
    let s = match s {
        [Token::Else(_), rest @ ..] => rest,
        _ => return Err(err("expected 'else', found something else")),
    };
    let (s, ()) = trivia1(s)?;
    let (s, (end, case_false)) = expr(s)?;
    let val = a::IfElse {
        expr: cond.boxed(),
        case_true: case_true.boxed(),
        case_false: case_false.boxed(),
    };
    Ok((s, (end.end, val)))
}

fn expr_inner(s: &[Token]) -> IResult<&[Token], (Span, a::Expr)> {
    match s {
        [Token::If(start), s @ ..] => {
            let (s, (end, val)) = expr_if(s)?;
            let range = Span {
                start: start.start,
                end: end,
            };
            let e = a::Expr::IfElse((range.clone(), val));
            Ok((s, (range, e)))
        }
        [Token::LiteralInt(box (range, n)), s @ ..] => {
            let e = a::Expr::Literal((range.clone(), a::Literal::Int(*n as i128)));
            Ok((s, (range.clone(), e)))
        }
        [Token::LiteralFloat(box (_range, _n)), _s @ ..] => {
            todo!()
        }
        [Token::ConstrTrue(range), s @ ..] => {
            let e = a::Expr::Literal((range.clone(), a::Literal::Bool(true)));
            Ok((s, (range.clone(), e)))
        }
        [Token::ConstrFalse(range), s @ ..] => {
            let e = a::Expr::Literal((range.clone(), a::Literal::Bool(false)));
            Ok((s, (range.clone(), e)))
        }
        [Token::SymbolLower(box (range, sym)) | Token::SymbolUpper(box (range, sym)), s @ ..] => {
            let e = a::Expr::Symbol((range.clone(), sym.clone()));
            Ok((s, (range.clone(), e)))
        }
        [Token::Backslash(start), s @ ..] => {
            let (s, (end, val)) = expr_function(s)?;
            let range = Span {
                start: start.start,
                end: end,
            };
            let e = a::Expr::Function((range.clone(), val));
            Ok((s, (range, e)))
        }
        [Token::LParens(start), s @ ..] => {
            let (s, (end, val)) = expr_tuple(s)?;
            let range = Span {
                start: start.start,
                end: end,
            };
            let e = a::Expr::Tuple((range.clone(), val));
            Ok((s, (range, e)))
        }
        [Token::Let(start), s @ ..] => {
            let (s, (end, val)) = expr_let(s)?;
            let range = Span {
                start: start.start,
                end: end,
            };
            let e = a::Expr::Let((range.clone(), val));
            Ok((s, (range, e)))
        }
        [Token::Match(start), s @ ..] => {
            let (s, (end, val)) = expr_match(s)?;
            let range = Span {
                start: start.start,
                end: end,
            };
            let e = a::Expr::Match((range.clone(), val));
            Ok((s, (range, e)))
        }
        _ => Err(err(
            "Unexpected token at position x1..x2. Expected something else",
        )),
    }
}

fn expr(s: &[Token]) -> IResult<&[Token], (Span, a::Expr)> {
    let (s, (start, e)) = expr_inner(s)?;
    let mut e = e;
    let mut s = s;
    let mut range = start;
    loop {
        let s_ = match trivia1(s) {
            Err(_) => break,
            Ok((s, _)) => s,
        };
        let (s_, (end, arg)) = match expr_inner(s_) {
            Err(_) => break,
            Ok(x) => x,
        };
        let val = a::Appl {
            func: e.boxed(),
            arg: arg.boxed(),
        };
        range.end = end.end;
        e = a::Expr::Appl((range.clone(), val));
        s = s_;
    }
    Ok((s, (range, e)))
}

fn type_sub_variant_args(s: &[Token]) -> (&[Token], Vec<a::Type>) {
    let mut s = s;
    let mut types = Vec::<a::Type>::new();
    loop {
        let s_ = match trivia1(s) {
            Err(_) => break,
            Ok((s, _)) => s,
        };
        let (s_, t) = match type_(s_) {
            Err(_) => break,
            Ok((s, (_, t))) => (s, t),
        };
        s = s_;
        types.push(t);
    }
    (s, types)
}

fn type_inner_upper<'a>(
    x: &str,
    start: Span,
    s: &'a [Token],
) -> IResult<&'a [Token], (Span, a::Type)> {
    // TODO: get end idx for args
    let (s, variables) = type_sub_variant_args(s);
    Ok((
        s,
        (
            start,
            a::Type::Custom(a::CustomType {
                name: a::CustomTypeSymbol(x.to_string()),
                variables: variables,
            }),
        ),
    ))
}

fn type_inner_tuple<'a>(s: &'a [Token]) -> IResult<&'a [Token], (Idx, Vec<a::Type>)> {
    let s = trivia0(s);
    if let [Token::RParens(end), s @ ..] = s {
        return Ok((s, (end.end, vec![])));
    }
    let (s, (_, first_type)) = type_(s)?;
    let mut types = vec![first_type];
    let mut s = s;
    let end = loop {
        let s_ = trivia0(s);
        let s_ = match s_ {
            [Token::RParens(end), s_ @ ..] => {
                s = s_;
                break end.end;
            }
            [Token::Comma(_), s @ ..] => s,
            _ => return Err(err("type_inner_tuple: missing comma")),
        };
        let s_ = trivia0(s_);
        let (s_, (_, t)) = type_(s_)?;
        s = s_;
        types.push(t);
    };
    Ok((s, (end, types)))
}

fn type_inner(s: &[Token]) -> IResult<&[Token], (Span, a::Type)> {
    match s {
        [Token::SymbolUpper(box (start, x)), s @ ..] => {
            return match x.0.as_ref() {
                "Int" => Ok((
                    s,
                    (start.clone(), a::Type::Intrinsic(a::IntrinsicType::Int)),
                )),
                "Bool" => Ok((
                    s,
                    (start.clone(), a::Type::Intrinsic(a::IntrinsicType::Bool)),
                )),
                x => type_inner_upper(x, start.clone(), s),
            };
        }
        [Token::SymbolLower(box (range, x)), s @ ..] => {
            let t: a::Type = a::Type::Var(a::VariableType(x.0.to_string()));
            return Ok((s, (range.clone(), t)));
        }
        [Token::LParens(start), s @ ..] => {
            let (s, (end, types)) = type_inner_tuple(s)?;
            let t = a::Type::Tuple(types);
            let range = Span {
                start: start.start,
                end,
            };
            return Ok((s, (range, t)));
        }
        _ => {
            return Err(err("type_inner"));
        }
    }
}

fn type_(s: &[Token]) -> IResult<&[Token], (Span, a::Type)> {
    // todo: lookahead
    //       if followed by an arrow, turn it into a function-type
    type_inner(s)
}

fn custom_type_variant_type(s: &[Token]) -> IResult<&[Token], (Span, a::Type)> {
    let (s, ()) = trivia1(s)?;
    type_(s)
}

fn custom_type_variant(s: &[Token]) -> IResult<&[Token], (Span, a::VariantDefinition)> {
    let (s, (start, sym)) = token_symbol_upper(s)?;
    // TODO cleanup
    let (s, t) = match custom_type_variant_type(s) {
        Err(_) => (s, None),
        Ok((s, (_, t))) => (s, Some(t)),
    };

    let range = start;
    let var = a::VariantDefinition {
        constr: sym,
        contained_type: t,
    };

    Ok((s, (range, var)))
}

fn custom_type(start: Idx, s: &[Token]) -> IResult<&[Token], (Span, a::CustomTypeDefinition)> {
    let (s, ()) = trivia1(s)?;
    let (s, (_, sym)) = token_symbol_upper(s)?;
    let (s, params) = symbols(s);
    let s = trivia0(s);
    let s = match s {
        [Token::Equals(_), rest @ ..] => rest,
        _ => return Err(err("custom_type: missing equals")),
    };
    let s = trivia0(s);
    let (s, (end, first_var)) = custom_type_variant(s)?;
    let mut s = s;
    let mut end = end;
    let mut variants = vec![first_var];

    loop {
        let s_ = trivia0(s);
        let s_ = match s_ {
            [Token::VerticalBar(_), rest @ ..] => rest,
            _ => break,
        };
        let s_ = trivia0(s_);
        let (s_, (end_, next_var)) = match custom_type_variant(s_) {
            Err(_) => break,
            Ok(x) => x,
        };
        s = s_;
        end = end_;
        variants.push(next_var);
    }

    let range = Span {
        start: start,
        end: end.end,
    };
    let type_def = a::CustomTypeDefinition {
        type_: a::CustomType {
            name: a::CustomTypeSymbol(sym.0),
            variables: match params {
                None => vec![],
                Some((_, params)) => params
                    .into_iter()
                    .map(|x| a::Type::Var(a::VariableType(x.0)))
                    .collect(),
            },
        },
        variants,
    };
    Ok((s, (range, type_def)))
}

fn symbols(s: &[Token]) -> (&[Token], Option<(Span, Vec<Symbol>)>) {
    let mut syms = Vec::<Symbol>::new();
    let mut s = s;
    let mut range = Span::default();
    loop {
        let s_ = match trivia1(s) {
            Err(_) => break,
            Ok((s, ())) => s,
        };
        let (s_, (end, sym)) = match token_symbol_lower(s_) {
            Err(_) => break,
            Ok(x) => x,
        };
        s = s_;
        syms.push(sym);
        if syms.len() == 1 {
            range.start = end.start;
        }
        range.end = end.end;
    }
    if syms.len() == 0 {
        (s, None)
    } else {
        (s, Some((range, syms)))
    }
}

fn patterns(s: &[Token]) -> (&[Token], Option<(Span, Vec<a::Pattern>)>) {
    let mut patterns = Vec::<a::Pattern>::new();
    let mut s = s;
    let mut range = Span::default();
    loop {
        let s_ = match trivia1(s) {
            Err(_) => break,
            Ok((s, ())) => s,
        };
        let (s_, (end, pat)) = match pattern(s_) {
            Err(_) => break,
            Ok(x) => x,
        };
        s = s_;
        patterns.push(pat);
        if patterns.len() == 1 {
            range.start = end.start;
        }
        range.end = end.end;
    }
    if patterns.len() == 0 {
        (s, None)
    } else {
        (s, Some((range, patterns)))
    }
}

fn global_binding(start: Idx, s: &[Token]) -> IResult<&[Token], (Span, a::SymbolBinding)> {
    let (s, ()) = trivia1(s)?;
    let (s, (_, sym)) = token_symbol_lower(s)?;
    let (s, patterns) = patterns(s);
    let s = trivia0(s);
    let s = match s {
        [Token::Equals(_), rest @ ..] => rest,
        _ => return Err(err("global_binding: missing equals")),
    };
    let s = trivia0(s);
    let (s, (end, e)) = expr(s)?;
    let mut e: a::Expr = e;
    let range = Span {
        start: start,
        end: end.end,
    };
    if let Some((_, patterns)) = patterns {
        for p in patterns.into_iter().rev() {
            e = a::Expr::Function((
                range.clone(),
                a::Function {
                    bind: p,
                    expr: e.boxed(),
                },
            ));
        }
    }

    let bind = a::SymbolBinding {
        bind: sym,
        type_: None,
        expr: e,
    };
    Ok((s, (range, bind)))
}

fn statement(s: &[Token]) -> IResult<&[Token], Option<a::Statement>> {
    match s {
        [Token::Let(range), s @ ..] => {
            let (s, (range, x)) = global_binding(range.start, s)?;
            let st = a::Statement::SymbolBinding((range, x));
            Ok((s, Some(st)))
        }
        [Token::Type(range), s @ ..] => {
            let (s, (range, x)) = custom_type(range.start, s)?;
            let st = a::Statement::CustomType((range, x));
            Ok((s, Some(st)))
        }
        [] => Ok((s, None)),
        _ => Err(err("unexpected token")),
    }
}

fn module(s: &[Token]) -> IResult<&[Token], a::Module> {
    let s = trivia0(s);
    let (s, first_st) = match statement(s)? {
        (s, Some(x)) => (s, x),
        (s, None) => return Ok((s, a::Module { statements: vec![] })),
    };
    let mut statements = vec![first_st];
    let mut s = s;
    loop {
        let s_ = trivia0_except_newline(s);
        let s_ = match s_ {
            [Token::Newline(_), rest @ ..] => rest,
            _ => break,
        };
        let s_ = trivia0(s_);
        let (s_, st) = match statement(s_)? {
            (s, Some(x)) => (s, x),
            (s_, None) => {
                s = s_;
                break;
            }
        };
        statements.push(st);
        s = s_;
    }

    let m = a::Module { statements };
    Ok((s, m))
}

pub fn parse_module(s: &str) -> Result<a::Module, String> {
    let tokens: Vec<Token> = lex(s);
    match module(&tokens) {
        Ok((_, e)) => Ok(e),
        Err(e) => Err(format!("oops {:?}", e)),
    }
}

pub fn parse_expr(s: &str) -> Result<a::Expr, String> {
    let tokens: Vec<Token> = lex(s);
    match expr(&tokens) {
        Ok((_, (_, e))) => Ok(e),
        Err(e) => Err(format!("oopsie {:?}", e)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_literal() {
        let tokens: Vec<Token> = lex("0");
        let e = expr(&tokens);
        assert!(e.is_ok());
        let tokens: Vec<Token> = lex("1234567890");
        let e = expr(&tokens);
        assert!(e.is_ok());
        let tokens: Vec<Token> = lex("01");
        let e = expr(&tokens);
        assert!(e.is_ok());
        let tokens: Vec<Token> = lex("True");
        let e = expr(&tokens);
        assert!(e.is_ok());
        let tokens: Vec<Token> = lex("False");
        let e = expr(&tokens);
        assert!(e.is_ok());
    }
    #[test]
    fn test_expr_appl() {
        let tokens: Vec<Token> = lex("f x");
        let e = expr(&tokens);
        assert!(e.is_ok());
    }
    #[test]
    fn test_expr_fn() {
        let tokens: Vec<Token> = lex("\\x -> x");
        let e = expr(&tokens);
        assert!(e.is_ok());
    }
    #[test]
    fn test_expr_tup() {
        let tokens: Vec<Token> = lex("()");
        let e = expr(&tokens);
        assert!(e.is_ok());
        let tokens: Vec<Token> = lex("(1)");
        let e = expr(&tokens);
        assert!(e.is_ok());
        let tokens: Vec<Token> = lex("(1,2,3)");
        let e = expr(&tokens);
        assert!(e.is_ok());
    }
    #[test]
    fn test_expr_if_else() {}
    #[test]
    fn test_expr_let() {}
    #[test]
    fn test_expr_match() {}

    #[test]
    fn test_stmt_let() {
        let tokens: Vec<Token> = lex("let x = ()");
        let e = statement(&tokens);
        assert!(e.is_ok());
    }
    #[test]
    fn test_stmt_let_fn_sugar() {
        let tokens: Vec<Token> = lex("let x a = ()");
        let e = statement(&tokens);
        assert!(e.is_ok());
    }

    #[test]
    fn test_stmt_type() {
        let tokens: Vec<Token> = lex("type B = T | F");
        let e = statement(&tokens);
        assert!(e.is_ok());
    }
}
