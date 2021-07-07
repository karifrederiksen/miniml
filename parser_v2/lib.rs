#![feature(iter_intersperse)]
#[allow(dead_code)]
mod lexer;
use ast as a;
use lexer::*;
use prelude::*;

// Use the bottom-up method

#[derive(Debug)]
enum Error {
    A,
}

type IResult<I, O> = Result<(I, O), Error>;

fn token_newline(s: &[Token]) -> IResult<&[Token], ()> {
    match s {
        [Token::Newline(_), rest @ ..] => Ok((rest, ())),
        _ => Err(Error::A),
    }
}
fn token_comment(s: &[Token]) -> IResult<&[Token], ()> {
    match s {
        [Token::Comment(_), rest @ ..] => Ok((rest, ())),
        _ => Err(Error::A),
    }
}

fn token_backslash(s: &[Token]) -> IResult<&[Token], Span> {
    match s {
        [Token::Backslash(span), rest @ ..] => Ok((rest, span.clone())),
        _ => Err(Error::A),
    }
}

fn token_skinnyarrow(s: &[Token]) -> IResult<&[Token], ()> {
    match s {
        [Token::ArrowSkinny(_), rest @ ..] => Ok((rest, ())),
        _ => Err(Error::A),
    }
}

fn token_if(s: &[Token]) -> IResult<&[Token], Span> {
    match s {
        [Token::If(span), rest @ ..] => Ok((rest, span.clone())),
        _ => Err(Error::A),
    }
}

fn token_then(s: &[Token]) -> IResult<&[Token], ()> {
    match s {
        [Token::Then(_), rest @ ..] => Ok((rest, ())),
        _ => Err(Error::A),
    }
}

fn token_else(s: &[Token]) -> IResult<&[Token], ()> {
    match s {
        [Token::Else(_), rest @ ..] => Ok((rest, ())),
        _ => Err(Error::A),
    }
}

fn token_match(s: &[Token]) -> IResult<&[Token], Span> {
    match s {
        [Token::Match(span), rest @ ..] => Ok((rest, span.clone())),
        _ => Err(Error::A),
    }
}

fn token_let(s: &[Token]) -> IResult<&[Token], Span> {
    match s {
        [Token::Let(span), rest @ ..] => Ok((rest, span.clone())),
        _ => Err(Error::A),
    }
}

fn token_rec(s: &[Token]) -> IResult<&[Token], Span> {
    match s {
        [Token::Rec(span), rest @ ..] => Ok((rest, span.clone())),
        _ => Err(Error::A),
    }
}

fn token_equal(s: &[Token]) -> IResult<&[Token], ()> {
    match s {
        [Token::Equals(_), rest @ ..] => Ok((rest, ())),
        _ => Err(Error::A),
    }
}

fn token_in(s: &[Token]) -> IResult<&[Token], ()> {
    match s {
        [Token::In(_), rest @ ..] => Ok((rest, ())),
        _ => Err(Error::A),
    }
}

fn token_type(s: &[Token]) -> IResult<&[Token], Span> {
    match s {
        [Token::Type(span), rest @ ..] => Ok((rest, span.clone())),
        _ => Err(Error::A),
    }
}

fn token_lparen(s: &[Token]) -> IResult<&[Token], Span> {
    match s {
        [Token::LParens(span), rest @ ..] => Ok((rest, span.clone())),
        _ => Err(Error::A),
    }
}

fn token_rparen(s: &[Token]) -> IResult<&[Token], Span> {
    match s {
        [Token::RParens(span), rest @ ..] => Ok((rest, span.clone())),
        _ => Err(Error::A),
    }
}

fn token_comma(s: &[Token]) -> IResult<&[Token], Span> {
    match s {
        [Token::Comma(span), rest @ ..] => Ok((rest, span.clone())),
        _ => Err(Error::A),
    }
}
fn token_space(s: &[Token]) -> IResult<&[Token], ()> {
    match s {
        [Token::Space(_), rest @ ..] => Ok((rest, ())),
        _ => Err(Error::A),
    }
}

fn literal(s: &[Token]) -> IResult<&[Token], (Span, a::Literal)> {
    match s {
        [Token::LiteralInt(x), rest @ ..] => {
            Ok((rest, (x.0.clone(), a::Literal::Int(x.1 as i128))))
        }
        [Token::ConstrTrue(x), rest @ ..] => Ok((rest, (x.clone(), a::Literal::Bool(true)))),
        [Token::ConstrFalse(x), rest @ ..] => Ok((rest, (x.clone(), a::Literal::Bool(false)))),
        _ => Err(Error::A),
    }
}

fn function(s: &[Token]) -> IResult<&[Token], (Span, a::Expr)> {
    let (s, start) = token_backslash(s)?;
    let s = trivia0(s);
    let (s, (_, p)) = pattern(s)?;
    let s = trivia0(s);
    let (s, ()) = token_skinnyarrow(s)?;
    let s = trivia0(s);
    let (s, (end, e)) = expr(s)?;
    let range = Span {
        start: start.start,
        end: end.end,
    };
    let f_expr = a::Expr::Function((
        range.clone(),
        a::Function {
            bind: p,
            expr: e.boxed(),
        },
    ));
    Ok((s, (range, f_expr)))
}

fn token_symbol_lower(s: &[Token]) -> IResult<&[Token], (Span, Symbol)> {
    match s {
        [Token::SymbolLower(x), rest @ ..] => Ok((rest, (x.0.clone(), Symbol(x.1.clone())))),
        _ => Err(Error::A),
    }
}

fn token_symbol_upper(s: &[Token]) -> IResult<&[Token], (Span, Symbol)> {
    match s {
        [Token::SymbolUpper(x), rest @ ..] => Ok((rest, (x.0.clone(), Symbol(x.1.clone())))),
        _ => Err(Error::A),
    }
}

fn token_vertical_bar(s: &[Token]) -> IResult<&[Token], ()> {
    match s {
        [Token::VerticalBar(_), rest @ ..] => Ok((rest, ())),
        _ => Err(Error::A),
    }
}

fn variant_ctor(s: &[Token]) -> IResult<&[Token], (Span, Symbol)> {
    match s {
        [Token::SymbolUpper(x), rest @ ..] => Ok((rest, (x.0.clone(), Symbol(x.1.clone())))),
        _ => Err(Error::A),
    }
}

fn trivia0_except_newline(s: &[Token]) -> &[Token] {
    let mut s = s;
    loop {
        s = if let Ok((s, _)) = token_space(s) {
            s
        } else if let Ok((s, _)) = token_comment(s) {
            s
        } else {
            break;
        };
    }
    s
}

fn trivia0(s: &[Token]) -> &[Token] {
    let mut s = s;
    loop {
        s = if let Ok((s_, ())) = token_newline(s) {
            s_
        } else if let Ok((s_, ())) = token_space(s) {
            s_
        } else if let Ok((s_, ())) = token_comment(s) {
            s_
        } else {
            break;
        };
    }
    s
}

fn trivia1(s: &[Token]) -> IResult<&[Token], ()> {
    if let Ok((s, _)) = token_space(s) {
        return Ok((trivia0(s), ()));
    }
    if let Ok((s, _)) = token_newline(s) {
        return Ok((trivia0(s), ()));
    }
    if let Ok((s, _)) = token_comment(s) {
        return Ok((trivia0(s), ()));
    }
    Err(Error::A)
}

fn pattern_variant(s: &[Token]) -> IResult<&[Token], (Span, a::VariantPattern)> {
    let (s, (start, constr)) = token_symbol_upper(s)?;
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

fn pattern_tuple(s: &[Token]) -> IResult<&[Token], (Span, Vec<a::Pattern>)> {
    let (s, start) = token_lparen(s)?;
    let mut s = s;
    let mut patterns = Vec::<a::Pattern>::new();
    loop {
        let (s_, pat) = match pattern(s) {
            Err(_) => break,
            Ok((s, (_, pat))) => (s, pat),
        };
        s = s_;
        patterns.push(pat);
    }
    let (s, end) = token_rparen(s)?;
    let range = Span {
        start: start.start,
        end: end.end,
    };
    Ok((s, (range, patterns)))
}

fn pattern(s: &[Token]) -> IResult<&[Token], (Span, a::Pattern)> {
    if let Ok((s, x)) = token_symbol_lower(s) {
        return Ok((s, (x.0.clone(), a::Pattern::Symbol(x))));
    }
    if let Ok((s, x)) = pattern_variant(s) {
        return Ok((s, (x.0.clone(), a::Pattern::Variant(x))));
    }
    if let Ok((s, x)) = pattern_tuple(s) {
        return Ok((s, (x.0.clone(), a::Pattern::Tuple(x))));
    }
    return Err(Error::A);
}

fn if_else(s: &[Token]) -> IResult<&[Token], (Span, a::IfElse)> {
    let (s, start) = token_if(s)?;
    let (s, ()) = trivia1(s)?;
    let (s, (_, cond)) = expr(s)?;
    let (s, ()) = trivia1(s)?;
    let (s, ()) = token_then(s)?;
    let (s, ()) = trivia1(s)?;
    let (s, (_, case_true)) = expr(s)?;
    let (s, ()) = trivia1(s)?;
    let (s, ()) = token_else(s)?;
    let (s, ()) = trivia1(s)?;
    let (s, (end, case_false)) = expr(s)?;
    let range = Span {
        start: start.start,
        end: end.end,
    };
    let val = a::IfElse {
        expr: cond.boxed(),
        case_true: case_true.boxed(),
        case_false: case_false.boxed(),
    };
    Ok((s, (range, val)))
}

fn tuple(s: &[Token]) -> IResult<&[Token], (Span, Vec<a::Expr>)> {
    let (s, start) = token_lparen(s)?;
    let s = trivia0(s);
    let mut exprs = Vec::new();
    let (s, end) = match expr(s) {
        Err(_) => token_rparen(s)?,
        Ok((s, (_, e))) => {
            let mut s = s;
            exprs.push(e);
            loop {
                s = trivia0(s);
                if let Ok(x) = token_rparen(s) {
                    break x;
                } else {
                    s = token_comma(s)?.0;
                    s = trivia0(s);
                    let (s_, (_, e)) = expr(s)?;
                    s = s_;
                    exprs.push(e);
                }
            }
        }
    };
    let range = Span {
        start: start.start,
        end: end.end,
    };
    Ok((s, (range, exprs)))
}

fn match_(s: &[Token]) -> IResult<&[Token], (Span, a::Match)> {
    let (s, start) = token_match(s)?;
    let (s, ()) = trivia1(s)?;
    let (s, (_, e)) = expr(s)?;
    let (s, ()) = trivia1(s)?;
    let mut branches = Vec::new();
    let (s, end) = {
        let mut end = Span::default();
        let mut s = s;
        loop {
            let s_ = trivia0(s);
            match match_branch(s_) {
                Err(_) => break,
                Ok((s_, (end_, branch))) => {
                    branches.push(branch);
                    s = s_;
                    end = end_;
                }
            };
        }
        (s, end)
    };
    let range = Span {
        start: start.start,
        end: end.end,
    };
    Ok((
        s,
        (
            range,
            a::Match {
                expr: e.boxed(),
                cases: branches,
            },
        ),
    ))
}

fn match_branch(s: &[Token]) -> IResult<&[Token], (Span, a::MatchCase)> {
    let (s, ()) = token_vertical_bar(s)?;
    let s = trivia0(s);
    let (s, (_, pat)) = pattern(s)?;
    let s = trivia0(s);
    let (s, ()) = token_skinnyarrow(s)?;
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

fn let_or_rec(s: &[Token]) -> IResult<&[Token], (Span, bool)> {
    if let Ok((s, range)) = token_let(s) {
        return Ok((s, (range, false)));
    }
    if let Ok((s, range)) = token_rec(s) {
        return Ok((s, (range, true)));
    }
    return Err(Error::A);
}

fn let_(s: &[Token]) -> IResult<&[Token], (Span, a::Let)> {
    let (s, start) = token_let(s)?;
    let (s, (_, bind)) = pattern(s)?;
    let (s, ()) = token_equal(s)?;
    let (s, (_, bind_expr)) = expr(s)?;
    let (s, ()) = token_in(s)?;
    let (s, (end, next_expr)) = expr(s)?;
    let range = Span {
        start: start.start,
        end: end.end,
    };
    let val = a::Let {
        bind: bind,
        bind_expr: bind_expr.boxed(),
        next_expr: next_expr.boxed(),
    };
    Ok((s, (range, val)))
}

fn expr(s: &[Token]) -> IResult<&[Token], (Span, a::Expr)> {
    let (s, (start, e)) = expr_inner(s)?;
    match expr_appl(s) {
        Err(_) => Ok((s, (start, e))),
        Ok((s, (end, arg))) => {
            let range = Span {
                start: start.start,
                end: end.end,
            };
            let val = a::Appl {
                func: e.boxed(),
                arg: arg.boxed(),
            };
            Ok((s, (range.clone(), a::Expr::Appl((range, val)))))
        }
    }
}

fn expr_appl(s: &[Token]) -> IResult<&[Token], (Span, a::Expr)> {
    let (s, ()) = trivia1(s)?;
    expr(s)
}

fn expr_inner(s: &[Token]) -> IResult<&[Token], (Span, a::Expr)> {
    if let Ok((s, x)) = literal(s) {
        return Ok((s, (x.0.clone(), a::Expr::Literal(x))));
    }
    if let Ok((s, x)) = token_symbol_lower(s) {
        return Ok((s, (x.0.clone(), a::Expr::Symbol(x))));
    }
    if let Ok((s, x)) = function(s) {
        return Ok((s, x));
    }
    if let Ok((s, x)) = variant_ctor(s) {
        let var = a::Variant {
            constr: x.1,
            value: None,
        };
        println!("3");
        return Ok((s, (x.0.clone(), a::Expr::VariantConstr((x.0, var)))));
    }
    if let Ok((s, x)) = if_else(s) {
        return Ok((s, (x.0.clone(), a::Expr::IfElse((x.0, x.1)))));
    }
    if let Ok((s, x)) = tuple(s) {
        return Ok((s, (x.0.clone(), a::Expr::Tuple((x.0, x.1)))));
    }
    if let Ok((s, x)) = let_(s) {
        return Ok((s, (x.0.clone(), a::Expr::Let((x.0, x.1)))));
    }
    if let Ok((s, x)) = match_(s) {
        return Ok((s, (x.0.clone(), a::Expr::Match((x.0, x.1)))));
    }
    return Err(Error::A);
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

fn type_sub(s: &[Token]) -> IResult<&[Token], (Span, a::Type)> {
    if let Ok((s, (range, x))) = token_symbol_upper(s) {
        let (s, t) = match x.0.as_ref() {
            "Int" => (s, a::Type::Intrinsic(a::IntrinsicType::Int)),
            "Bool" => (s, a::Type::Intrinsic(a::IntrinsicType::Bool)),
            x => {
                let (s, variables) = type_sub_variant_args(s);
                (
                    s,
                    a::Type::Custom(a::CustomType {
                        name: a::CustomTypeSymbol(x.to_string()),
                        variables: variables,
                    }),
                )
            }
        };
        return Ok((s, (range, t)));
    }
    if let Ok((s, (range, x))) = token_symbol_lower(s) {
        let t: a::Type = a::Type::Var(a::VariableType(x.0.to_string()));
        return Ok((s, (range, t)));
    }
    if let Ok((s, start)) = token_lparen(s) {
        let mut types = Vec::<a::Type>::new();
        let mut s = s;
        if let Ok((s_, (_, t))) = type_(s) {
            types.push(t);
            s = s_;

            loop {
                let s_ = trivia0(s);
                let s_ = match token_comma(s_) {
                    Err(_) => break,
                    Ok((s, _)) => s,
                };
                let s_ = trivia0(s_);
                match type_(s_) {
                    Err(_) => break,
                    Ok((s_, (_, t))) => {
                        types.push(t);
                        s = s_;
                    }
                };
            }
        }
        let s = trivia0(s);
        let (s, end) = token_rparen(s)?;
        let range = Span {
            start: start.start,
            end: end.end,
        };
        let t = a::Type::Tuple(types);
        return Ok((s, (range, t)));
    }
    return Err(Error::A);
}

fn type_(s: &[Token]) -> IResult<&[Token], (Span, a::Type)> {
    // todo: lookahead
    //       if followed by an arrow, turn it into a function-type
    type_sub(s)
}

fn custom_type_variant_type(s: &[Token]) -> IResult<&[Token], (Span, a::Type)> {
    let (s, ()) = trivia1(s)?;
    type_(s)
}

fn custom_type_variant(s: &[Token]) -> IResult<&[Token], (Span, a::VariantDefinition)> {
    let (s, (start, sym)) = token_symbol_upper(s)?;
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
fn custom_type_variant2(s: &[Token]) -> IResult<&[Token], (Span, a::VariantDefinition)> {
    let s = trivia0(s);
    let (s, ()) = token_vertical_bar(s)?;
    let s = trivia0(s);
    custom_type_variant(s)
}
fn custom_type(s: &[Token]) -> IResult<&[Token], (Span, a::CustomTypeDefinition)> {
    let (s, start) = token_type(s)?;
    let (s, ()) = trivia1(s)?;
    let (s, (_, sym)) = token_symbol_upper(s)?;
    let (s, params) = params_list(s);
    let s = trivia0(s);
    let (s, ()) = token_equal(s)?;
    let s = trivia0(s);
    let (s, (end, first_var)) = custom_type_variant(s)?;
    let mut s = s;
    let mut end = end;
    let mut variants = vec![first_var];

    loop {
        let (s_, (end_, next_var)) = match custom_type_variant2(s) {
            Err(_) => break,
            Ok(x) => x,
        };
        s = s_;
        end = end_;
        variants.push(next_var);
    }

    let range = Span {
        start: start.start,
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

fn symbols_lower0(s: &[Token]) -> (&[Token], Span, Vec<Symbol>) {
    println!("1");
    let mut syms = Vec::<Symbol>::new();
    println!("2");
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

    (s, range, syms)
}

fn params_list(s: &[Token]) -> (&[Token], Option<(Span, Vec<Symbol>)>) {
    let (s, range, syms) = symbols_lower0(s);
    if syms.len() == 0 {
        (s, None)
    } else {
        (s, Some((range, syms)))
    }
}

fn global_binding(s: &[Token]) -> IResult<&[Token], (Span, a::SymbolBinding)> {
    println!("a");
    let (s, (start, recursive)) = let_or_rec(s)?;
    println!("b");
    let (s, ()) = trivia1(s)?;
    println!("c");
    let (s, (_, sym)) = token_symbol_lower(s)?;
    println!("d");
    let (s, params) = params_list(s);
    println!("e {:?}", params);
    let s = trivia0(s);
    let (s, ()) = token_equal(s)?;
    println!("f");
    let s = trivia0(s);
    let (s, (end, e)) = expr(s)?;
    let range = Span {
        start: start.start,
        end: end.end,
    };
    let mut e: a::Expr = e;
    if let Some((_, params)) = params {
        for p in params.into_iter().rev() {
            e = a::Expr::Function((
                range.clone(),
                a::Function {
                    bind: a::Pattern::Symbol((range.clone(), p)),
                    expr: e.boxed(),
                },
            ));
        }
    }

    let bind = a::SymbolBinding {
        recursive,
        bind: sym,
        type_: None,
        expr: e,
    };
    Ok((s, (range, bind)))
}

fn statement(s: &[Token]) -> IResult<&[Token], (Span, a::Statement)> {
    if let Ok((s, x)) = global_binding(s) {
        return Ok((s, (x.0.clone(), a::Statement::SymbolBinding((x.0, x.1)))));
    }
    if let Ok((s, x)) = custom_type(s) {
        return Ok((s, (x.0.clone(), a::Statement::CustomType((x.0, x.1)))));
    }
    return Err(Error::A);
}

fn module_statement(s: &[Token]) -> IResult<&[Token], (Span, a::Statement)> {
    let s = trivia0_except_newline(s);
    let (s, ()) = token_newline(s)?;
    let s = trivia0(s);
    statement(s)
}

fn module(s: &[Token]) -> IResult<&[Token], (Span, a::Module)> {
    let s = trivia0(s);
    let (s, (start, first_st)) = statement(s)?;
    let mut statements = vec![first_st];
    let mut s = s;
    let mut range = start;
    loop {
        let (s_, (end, st)) = match module_statement(s) {
            Err(err) => {
                println!("==== rest ====");
                println!("{}", s.iter().map(|x| x.to_string()).collect::<String>());
                println!("==== tres ====");
                println!("err: {:?}", err);
                break;
            }
            Ok(x) => x,
        };
        range.end = end.end;
        statements.push(st);
        s = s_;
    }

    let m = a::Module { statements };

    Ok((s, (range, m)))
}

pub fn parse_module(s: &str) -> Result<a::Module, String> {
    let tokens: Vec<Token> = lex(s);
    match module(&tokens) {
        Ok((_, (_, e))) => Ok(e),
        Err(_) => Err("oops".to_owned()),
    }
}

pub fn parse_expr(s: &str) -> Result<a::Expr, String> {
    let tokens: Vec<Token> = lex(s);
    match expr(&tokens) {
        Ok((_, (_, e))) => Ok(e),
        Err(_) => Err("oops".to_owned()),
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
