use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Symbol(pub String);

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Symbol {
    pub fn is_camelcase(&self) -> bool {
        self.0.chars().next().unwrap().is_uppercase()
    }

    pub fn from<S: Into<String>>(x: S) -> Self {
        Self(x.into())
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

pub type Span = core::ops::Range<u32>;

#[derive(Debug, Clone)]
pub struct Sourced<A> {
    pub val: A,
    pub source: Span,
}

impl<A: PartialEq> PartialEq for Sourced<A> {
    fn eq(&self, other: &Self) -> bool {
        self.val == other.val
    }
}

impl<A: PartialEq> Eq for Sourced<A> {}

impl<A: PartialOrd> PartialOrd for Sourced<A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.val.partial_cmp(&other.val)
    }
}

impl<A: Ord> Ord for Sourced<A> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.val.cmp(&other.val)
    }
}

impl<A: Hash> Hash for Sourced<A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.val.hash(state);
    }
}
