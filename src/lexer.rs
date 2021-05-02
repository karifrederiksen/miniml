use logos::{Lexer, Logos};

fn float(lex: &mut Lexer<Token>) -> Option<f64> {
    let slice: &str = lex.slice();
    let n: f64 = slice.parse().ok()?;
    Some(n)
}
fn int(lex: &mut Lexer<Token>) -> Option<i64> {
    let slice: &str = lex.slice();
    let n: i64 = slice.parse().ok()?;
    Some(n)
}
fn string(lex: &mut Lexer<Token>) -> Option<String> {
    let slice: &str = lex.slice();
    let n: String = slice.to_owned();
    Some(n)
}

#[derive(Logos, Debug, PartialEq)]
pub enum Token {
    #[token("Int")]
    TypeInt,
    #[token("Bool")]
    TypeBool,
    #[token("True")]
    ConstrTrue,
    #[token("False")]
    ConstrFalse,
    #[token("let")]
    Let,
    #[token("rec")]
    Rec,
    #[token("in")]
    In,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("fn")]
    Fn,
    #[token("match")]
    Match,
    #[token("with")]
    With,
    #[token("type")]
    Type,
    #[token("\\")]
    Backslash,
    #[token("=")]
    Equals,
    #[token(",")]
    Comma,
    #[token(":")]
    SemiColon,
    #[token("|")]
    VerticalBar,
    #[token("->")]
    ArrowSkinny,
    #[token("=>")]
    ArrowFat,
    #[token("(")]
    LParens,
    #[token(")")]
    RParens,
    #[regex(" +")]
    Space,
    #[regex("\n+")]
    Newline,
    #[regex("[a-z_][a-z0-9_]+", string)]
    SymbolLower(String),
    #[regex("[A-Z][a-z0-9]+", string)]
    SymbolUpper(String),
    #[regex(r"-?[0-9]+\.[0-9]+", float)]
    LiteralFloat(f64),
    #[regex("-?[0-9]+", int)]
    LiteralInt(i64),

    #[error]
    #[regex(r"[\t\r\f]+", logos::skip)]
    Error,
}

pub fn parse(s: &str) -> Lexer<Token> {
    Token::lexer(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test() {}
}
