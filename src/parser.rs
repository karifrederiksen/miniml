extern crate nom;
use nom::branch;
use nom::bytes::complete::*;
use nom::character::complete as character;
use nom::combinator;
use nom::combinator::{map, map_res, recognize, success, verify};
use nom::error::context;
use nom::multi;
use nom::sequence as seq;
use nom::IResult;

use crate::ast::*;
use crate::prelude::{sym, Symbol};

fn is_space_or_lf(c: char) -> bool {
    " \t\n\r".contains(c)
}

fn space_lf0(s: &str) -> IResult<&str, &str> {
    let mut p = recognize(multi::many0(branch::alt((
        recognize(character::satisfy(is_space_or_lf)),
        parse_line_comment,
        parse_multiline_comment,
    ))));
    p(s)
}
fn space_lf1(s: &str) -> IResult<&str, &str> {
    let mut p = recognize(multi::many1(branch::alt((
        recognize(character::satisfy(is_space_or_lf)),
        parse_line_comment,
        parse_multiline_comment,
    ))));
    p(s)
}

fn parse_bool(s: &str) -> IResult<&str, bool> {
    let mut p = branch::alt((map(tag("True"), |_| true), map(tag("False"), |_| false)));
    p(s)
}

fn parse_int(s: &str) -> IResult<&str, i128> {
    let mut p = map_res(character::digit1, |s: &str| s.parse::<i128>());
    p(s)
}

fn parse_literal(s: &str) -> IResult<&str, Literal> {
    let mut p = branch::alt((map(parse_bool, Literal::Bool), map(parse_int, Literal::Int)));
    p(s)
}
fn parse_literal_expr(s: &str) -> IResult<&str, Expr> {
    let mut p = context("Literal", map(parse_literal, Expr::Literal));
    p(s)
}

const RESERVED_SYMBOLS: [&'static str; 9] = [
    "let", "rec", "in", "if", "then", "else", "fn", "match", "with",
];

fn is_not_reserved(s: &str) -> bool {
    !RESERVED_SYMBOLS.contains(&s)
}

fn parse_sym(s: &str) -> IResult<&str, Symbol> {
    use std::iter::FromIterator;
    let mut p = map(
        verify(
            map(
                seq::tuple((
                    character::one_of("_abcdefghijklmnopqrstuvwxyz"),
                    map(
                        multi::many0(character::one_of("_abcdefghijklmnopqrstuvwxyz0123456789")),
                        String::from_iter,
                    ),
                )),
                |(first, second): (char, String)| format!("{}{}", first, second),
            ),
            is_not_reserved,
        ),
        sym,
    );
    p(s)
}
fn parse_sym_expr(s: &str) -> IResult<&str, Expr> {
    let mut p = context("Symbol", map(parse_sym, Expr::Symbol));
    p(s)
}
fn parse_sym_pattern(s: &str) -> IResult<&str, Pattern> {
    let mut p = map(parse_sym, Pattern::Symbol);
    p(s)
}
fn parse_tuple_pattern(s: &str) -> IResult<&str, Pattern> {
    let p = map(
        multi::separated_list0(
            tag(","),
            seq::preceded(space_lf0, seq::terminated(parse_pattern, space_lf0)),
        ),
        |x| Pattern::Tuple(TuplePattern(x)),
    );
    let mut p = seq::preceded(tag("("), seq::terminated(p, tag(")")));
    p(s)
}

fn parse_variant_pattern(s: &str) -> IResult<&str, Pattern> {
    let mut p = map(parse_custom_type, |t| {
        Pattern::Variant(VariantPattern {
            constr: t,
            pattern: None,
        })
    });
    p(s)
}
fn parse_pattern(s: &str) -> IResult<&str, Pattern> {
    let mut p = branch::alt((
        parse_sym_pattern,
        parse_tuple_pattern,
        parse_variant_pattern,
    ));
    p(s)
}
fn parse_line_comment(s: &str) -> IResult<&str, &str> {
    // todo: do this properly
    let mut p = context(
        "LineComment",
        recognize(seq::tuple((
            tag("--"),
            multi::many0(branch::alt((
                space_lf1,
                character::alphanumeric1,
                recognize(character::one_of(",.;:!?")),
            ))),
            character::newline,
        ))),
    );
    p(s)
}
fn parse_multiline_comment(s: &str) -> IResult<&str, &str> {
    // todo: do this properly
    let mut p = recognize(seq::tuple((
        tag("{-"),
        multi::many0(branch::alt((
            space_lf1,
            character::alphanumeric1,
            recognize(character::one_of(",.;:!?")),
        ))),
        tag("-}"),
    )));
    p(s)
}
fn parse_if_else_expr(s: &str) -> IResult<&str, Expr> {
    let mut p = context(
        "IfElse",
        seq::tuple((
            tag("if"),
            space_lf1,
            parse_expr,
            space_lf1,
            tag("then"),
            space_lf1,
            parse_expr,
            space_lf1,
            tag("else"),
            space_lf1,
            parse_expr,
        )),
    );
    let (s, (_, _, expr, _, _, _, case_true, _, _, _, case_false)) = p(s)?;
    Ok((
        s,
        Expr::IfElse(IfElse {
            expr: Box::new(expr),
            case_true: Box::new(case_true),
            case_false: Box::new(case_false),
        }),
    ))
}
fn parse_func_expr(s: &str) -> IResult<&str, Expr> {
    let mut p = context(
        "Func",
        seq::tuple((
            tag("\\"),
            space_lf0,
            parse_pattern,
            space_lf0,
            tag("->"),
            space_lf0,
            parse_expr,
        )),
    );
    let (s, (_, _, bind, _, _, _, expr)) = p(s)?;
    Ok((
        s,
        Expr::Function(Function {
            bind,
            expr: Box::new(expr),
        }),
    ))
}
fn parse_let_expr(s: &str) -> IResult<&str, Expr> {
    let mut p = context(
        "LetExpr",
        seq::tuple((
            seq::terminated(
                branch::alt((map(tag("rec"), |_| true), map(tag("let"), |_| false))),
                space_lf1,
            ),
            parse_pattern,
            seq::terminated(
                branch::alt((
                    map(seq::preceded(space_lf1, parse_pattern), Some),
                    success(None),
                )),
                seq::tuple((space_lf0, tag("="), space_lf0)),
            ),
            seq::terminated(parse_expr, seq::tuple((space_lf1, tag("in"), space_lf1))),
            parse_expr,
        )),
    );
    let (s, (recursive, bind, par, bind_expr, next_expr)) = p(s)?;
    Ok((
        s,
        Expr::Let(Let {
            recursive,
            bind,
            bind_expr: Box::new(match par {
                None => bind_expr,
                Some(par) => Expr::Function(Function {
                    bind: par,
                    expr: Box::new(bind_expr),
                }),
            }),
            next_expr: Box::new(next_expr),
        }),
    ))
}

fn parse_tuple_expr(s: &str) -> IResult<&str, Expr> {
    let sep_p = seq::tuple((space_lf0, tag(","), space_lf0));
    let mut p = context(
        "Tuple",
        map(
            seq::tuple((
                tag("("),
                space_lf0,
                multi::separated_list0(sep_p, parse_expr),
                space_lf0,
                tag(")"),
            )),
            |(_, _, exprs, _, _)| {
                if exprs.len() == 1 {
                    exprs.get(0).unwrap().clone()
                } else {
                    Expr::Tuple(Tuple { exprs })
                }
            },
        ),
    );
    p(s)
}
// pub struct MatchCase {
//     pub pattern: Pattern,
//     pub expr: Box<Expr>,
// }

fn parse_match_expr(s: &str) -> IResult<&str, Expr> {
    let case_p = map(
        seq::tuple((
            parse_pattern,
            seq::tuple((space_lf0, tag("->"), space_lf0)),
            parse_expr,
        )),
        |(pattern, _, expr)| MatchCase {
            pattern,
            expr: Box::new(expr),
        },
    );
    let mut p = seq::tuple((
        seq::tuple((tag("match"), space_lf1)),
        parse_expr,
        seq::tuple((space_lf1, tag("with"), space_lf1)),
        multi::separated_list1(seq::tuple((space_lf0, tag(","), space_lf0)), case_p),
    ));
    let (s, (_, expr, _, cases)) = p(s)?;
    Ok((
        s,
        Expr::Match(Match {
            expr: Box::new(expr),
            cases,
        }),
    ))
}

fn parse_type_constr_expr(s: &str) -> IResult<&str, Expr> {
    let mut p = map(parse_custom_type, |x| Expr::Symbol(Symbol(x.0)));
    p(s)
}
fn parse_expr(s: &str) -> IResult<&str, Expr> {
    let mut p = context(
        "Expr",
        branch::alt((
            parse_tuple_expr,
            parse_literal_expr,
            parse_func_expr,
            parse_let_expr,
            parse_if_else_expr,
            parse_match_expr,
            parse_sym_expr,
            parse_type_constr_expr,
        )),
    );

    // this can be siplified with nom::multi...

    // handle function applications
    let (s, first_expr) = p(s)?;
    let mut p = seq::preceded(space_lf1, p);
    let mut exprs = vec![first_expr];
    let mut s = s;
    loop {
        let (next_s, expr) = match p(s) {
            Ok(x) => x,
            Err(_) => break,
        };
        s = next_s;
        exprs.push(expr);
    }
    let mut expr = exprs.get(0).unwrap().clone();
    if exprs.len() == 1 {
        Ok((s, expr))
    } else {
        for i in 1..exprs.len() {
            expr = Expr::Appl(Appl {
                func: Box::new(expr),
                arg: Box::new(exprs.get(i).unwrap().clone()),
            });
        }
        Ok((s, expr))
    }
}

pub fn parse(s: &str) -> Result<Expr, String> {
    match parse_expr(s.trim()) {
        Ok((_, e)) => Ok(e),
        Err(e) => Err(format!("{}", e)),
    }
}

fn parse_let_statement(s: &str) -> IResult<&str, Statement> {
    let mut p = context(
        "LetStatement",
        seq::tuple((
            branch::alt((map(tag("rec"), |_| true), map(tag("let"), |_| false))),
            space_lf1,
            parse_sym,
            branch::alt((
                map(seq::preceded(space_lf1, parse_pattern), Some),
                success(None),
            )),
            seq::tuple((space_lf0, tag("="), space_lf0)),
            parse_expr,
        )),
    );
    let (s, (recursive, _, sym, par, _, expr)) = p(s)?;
    let stmt = LetStatement {
        recursive,
        bind: sym,
        expr: match par {
            None => expr,
            Some(par) => Expr::Function(Function {
                bind: par,
                expr: Box::new(expr),
            }),
        },
    };
    Ok((s, Statement::Let(stmt)))
}

fn parse_custom_type(s: &str) -> IResult<&str, CustomType> {
    use std::iter::FromIterator;
    let mut p = map(
        seq::tuple((
            character::one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ"),
            map(
                multi::many0(character::one_of(
                    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789",
                )),
                String::from_iter,
            ),
        )),
        |(first, second): (char, String)| CustomType(format!("{}{}", first, second)),
    );
    p(s)
}
fn parse_variant_definition(s: &str) -> IResult<&str, VariantDefinition> {
    let mut p = map(parse_custom_type, |t| VariantDefinition {
        constr: t,
        expr: None,
    });
    p(s)
}
fn parse_variant(s: &str) -> IResult<&str, Variant> {
    let mut p = map(parse_custom_type, |t| Variant {
        constr: t,
        value: None,
    });
    p(s)
}

fn parse_custom_type_statement(s: &str) -> IResult<&str, Statement> {
    let mut p = seq::tuple((
        seq::tuple((tag("type"), space_lf1)),
        parse_custom_type,
        seq::tuple((space_lf0, tag("="), space_lf0)),
        multi::separated_list1(
            seq::tuple((space_lf0, tag("|"), space_lf0)),
            parse_variant_definition,
        ),
    ));
    let (s, (_, name, _, variants)) = p(s)?;
    let ty = CustomTypeDefinition { name, variants };
    Ok((s, Statement::Type(ty)))
}

pub fn parse_module(s: &str) -> Result<Module, String> {
    let mut p = map(
        seq::tuple((
            space_lf0,
            multi::separated_list1(
                space_lf1,
                branch::alt((parse_let_statement, parse_custom_type_statement)),
            ),
            space_lf0,
        )),
        |(_, statements, _)| Module { statements },
    );
    match p(s) {
        Ok((_, e)) => Ok(e),
        Err(e) => Err(format!("{}", e)),
    }
}
