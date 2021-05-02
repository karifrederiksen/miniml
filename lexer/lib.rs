use logos::{Lexer, Logos};

pub type Span = core::ops::Range<u32>;

fn span(lex: &mut Lexer<Token>) -> Span {
    let span = lex.span();
    core::ops::Range {
        start: span.start as u32,
        end: span.end as u32,
    }
}

fn float(lex: &mut Lexer<Token>) -> Option<Box<(Span, f64)>> {
    let slice: &str = lex.slice();
    let f: f64 = slice.parse().ok()?;
    Some(Box::new((span(lex), f)))
}
fn int(lex: &mut Lexer<Token>) -> Option<Box<(Span, i64)>> {
    let slice: &str = lex.slice();
    let i: i64 = slice.parse().ok()?;
    Some(Box::new((span(lex), i)))
}
fn string(lex: &mut Lexer<Token>) -> Box<(Span, String)> {
    let slice: &str = lex.slice();
    let s: String = slice.to_owned();
    Box::new((span(lex), s))
}

#[derive(Logos, Debug, PartialEq)]
pub enum Token {
    #[token("Int", span)]
    TypeInt(Span),
    #[token("Bool", span)]
    TypeBool(Span),
    #[token("True", span)]
    ConstrTrue(Span),
    #[token("False", span)]
    ConstrFalse(Span),
    #[token("let", span)]
    Let(Span),
    #[token("rec", span)]
    Rec(Span),
    #[token("in", span)]
    In(Span),
    #[token("then", span)]
    Then(Span),
    #[token("else", span)]
    Else(Span),
    #[token("fn", span)]
    Fn(Span),
    #[token("match", span)]
    Match(Span),
    #[token("with", span)]
    With(Span),
    #[token("type", span)]
    Type(Span),
    #[token("\\", span)]
    Backslash(Span),
    #[token("=", span)]
    Equals(Span),
    #[token(",", span)]
    Comma(Span),
    #[token(":", span)]
    SemiColon(Span),
    #[token("|", span)]
    VerticalBar(Span),
    #[token("->", span)]
    ArrowSkinny(Span),
    #[token("=>", span)]
    ArrowFat(Span),
    #[token("(", span)]
    LParens(Span),
    #[token(")", span)]
    RParens(Span),
    #[regex(" +", span)]
    Space(Span),
    #[regex("\n+", span)]
    Newline(Span),
    #[regex("[a-z_][a-z0-9_]+", string)]
    SymbolLower(Box<(Span, String)>),
    #[regex("[A-Z][a-z0-9]+", string)]
    SymbolUpper(Box<(Span, String)>),
    #[regex(r"-?[0-9]+\.[0-9]+", float)]
    LiteralFloat(Box<(Span, f64)>),
    #[regex("-?[0-9]+", int)]
    LiteralInt(Box<(Span, i64)>),

    #[error]
    #[regex(r"[\t\r\f]+", logos::skip)]
    Error,
}

impl Token {
    pub fn span(&self) -> Span {
        match self {
            Token::Error => Span { start: 0, end: 0 },
            Token::SymbolLower(x) | Token::SymbolUpper(x) => x.0.clone(),
            Token::LiteralFloat(x) => x.0.clone(),
            Token::LiteralInt(x) => x.0.clone(),
            Token::TypeInt(x) => x.clone(),
            Token::TypeBool(x) => x.clone(),
            Token::ConstrTrue(x) => x.clone(),
            Token::ConstrFalse(x) => x.clone(),
            Token::Let(x) => x.clone(),
            Token::Rec(x) => x.clone(),
            Token::In(x) => x.clone(),
            Token::Then(x) => x.clone(),
            Token::Else(x) => x.clone(),
            Token::Fn(x) => x.clone(),
            Token::Match(x) => x.clone(),
            Token::With(x) => x.clone(),
            Token::Type(x) => x.clone(),
            Token::Backslash(x) => x.clone(),
            Token::Equals(x) => x.clone(),
            Token::Comma(x) => x.clone(),
            Token::SemiColon(x) => x.clone(),
            Token::VerticalBar(x) => x.clone(),
            Token::ArrowSkinny(x) => x.clone(),
            Token::ArrowFat(x) => x.clone(),
            Token::LParens(x) => x.clone(),
            Token::RParens(x) => x.clone(),
            Token::Space(x) => x.clone(),
            Token::Newline(x) => x.clone(),
        }
    }
}

pub fn parse(s: &str) -> Vec<Token> {
    let t: Lexer<Token> = Token::lexer(s);
    let t: Vec<Token> = t.collect();
    t
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test() {}
}
