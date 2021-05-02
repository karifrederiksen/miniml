use std::fmt;

#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Symbol(pub String);

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Symbol {
    pub fn is_camelcase(&self) -> bool {
        self.0.chars().next().unwrap().is_uppercase()
    }
}

pub fn sym<S: Into<String>>(x: S) -> Symbol {
    Symbol(x.into())
}

pub fn u32_to_ascii(n: u32) -> String {
    let mut s = String::new();
    let mut n = n;
    while n > 0 {
        let c = (96 + (n % 26)) as u8;
        s.push(c as char);
        n = n / 26;
    }
    s.chars().rev().collect()
}
