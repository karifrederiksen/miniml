use logos::{Lexer, Logos};
use prelude::{Span, Symbol};

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
fn symbol(lex: &mut Lexer<Token>) -> Box<(Span, Symbol)> {
    let slice: &str = lex.slice();
    let s: String = slice.to_owned();
    Box::new((span(lex), Symbol::from(s)))
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
    #[token("if", span)]
    If(Span),
    #[token("then", span)]
    Then(Span),
    #[token("else", span)]
    Else(Span),
    #[token("match", span)]
    Match(Span),
    #[token("type", span)]
    Type(Span),
    #[token("\\", span)]
    Backslash(Span),
    #[token("=", span)]
    Equals(Span),
    #[token(",", span)]
    Comma(Span),
    #[token(":", span)]
    Colon(Span),
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
    #[regex("\n", span)]
    Newline(Span),
    #[regex("[a-z_][a-z0-9_]*", symbol)]
    SymbolLower(Box<(Span, Symbol)>),
    #[regex("[A-Z][a-z0-9]*", symbol)]
    SymbolUpper(Box<(Span, Symbol)>),
    #[regex(r"-?[0-9]+\.[0-9]+", float)]
    LiteralFloat(Box<(Span, f64)>),
    #[regex("-?[0-9]+", int)]
    LiteralInt(Box<(Span, i64)>),
    #[regex("#.*\n", string)]
    Comment(Box<(Span, String)>),

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
            Token::If(x) => x.clone(),
            Token::Then(x) => x.clone(),
            Token::Else(x) => x.clone(),
            Token::Match(x) => x.clone(),
            Token::Type(x) => x.clone(),
            Token::Backslash(x) => x.clone(),
            Token::Equals(x) => x.clone(),
            Token::Comma(x) => x.clone(),
            Token::Colon(x) => x.clone(),
            Token::VerticalBar(x) => x.clone(),
            Token::ArrowSkinny(x) => x.clone(),
            Token::ArrowFat(x) => x.clone(),
            Token::LParens(x) => x.clone(),
            Token::RParens(x) => x.clone(),
            Token::Space(x) => x.clone(),
            Token::Newline(x) => x.clone(),
            Token::Comment(x) => x.0.clone(),
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            Token::Error => "".to_owned(),
            Token::SymbolLower(box (_, x)) | Token::SymbolUpper(box (_, x)) => x.0.clone(),
            Token::LiteralFloat(box (_, x)) => format!("{}", &x),
            Token::LiteralInt(box (_, x)) => format!("{}", &x),
            Token::TypeInt(_) => "Int".to_owned(),
            Token::TypeBool(_) => "Bool".to_owned(),
            Token::ConstrTrue(_) => "True".to_owned(),
            Token::ConstrFalse(_) => "False".to_owned(),
            Token::Let(_) => "let".to_owned(),
            Token::Rec(_) => "rec".to_owned(),
            Token::In(_) => "in".to_owned(),
            Token::If(_) => "if".to_owned(),
            Token::Then(_) => "then".to_owned(),
            Token::Else(_) => "else".to_owned(),
            Token::Match(_) => "match".to_owned(),
            Token::Type(_) => "type".to_owned(),
            Token::Backslash(_) => "\\".to_owned(),
            Token::Equals(_) => "=".to_owned(),
            Token::Comma(_) => ",".to_owned(),
            Token::Colon(_) => ":".to_owned(),
            Token::VerticalBar(_) => "|".to_owned(),
            Token::ArrowSkinny(_) => "->".to_owned(),
            Token::ArrowFat(_) => "=>".to_owned(),
            Token::LParens(_) => "(".to_owned(),
            Token::RParens(_) => ")".to_owned(),
            Token::Space(x) => " ".repeat((x.end - x.start) as usize).to_owned(),
            Token::Newline(_) => "\n".to_owned(),
            Token::Comment(x) => x.1.to_string(),
        }
    }
}

pub fn lex(s: &str) -> Vec<Token> {
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
