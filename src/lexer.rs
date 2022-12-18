pub enum Token {
    Colon,
    ColonEq,
    Dot,
    Comma,
    Pi,
    Lambda,
    Plus,
    Natural(String),
    Ident(Box<Ident>),
    Delimited(Vec<Token>),
}

pub fn lex(input: &str, reporter: &mut impl Reporter) -> Vec<Token> {
    let (tokens, rest) = lex_inner(input, 0, reporter);
    assert_eq!(rest, "");
    tokens
}

fn lex_inner<'input>(
    input: &'input str,
    depth: usize,
    reporter: &mut impl Reporter,
) -> (Vec<Token>, &'input str) {
    let mut tokens = Vec::new();
    let mut input = input.chars();

    while let Some(c) = input.next() {
        tokens.push(match c {
            ':' => Token::Colon,
            '≔' => Token::ColonEq,
            '.' => Token::Dot,
            ',' => Token::Comma,
            'Π' => Token::Pi,
            'λ' => Token::Lambda,
            '+' => Token::Plus,
            '(' => {
                let (tokens, rest) = lex_inner(input.as_str(), depth + 1, reporter);
                input = rest.chars();
                Token::Delimited(tokens)
            }
            ')' if depth != 0 => return (tokens, input.as_str()),
            ')' => {
                reporter.report("unexpected closing bracket");
                continue;
            }
            c if is_xid_start(c) => {
                let rest = input.as_str();
                let i = rest.find(|c| !is_xid_continue(c)).unwrap_or(rest.len());
                let (ident_continue, rest) = rest.split_at(i);
                input = rest.chars();

                let mut ident = String::with_capacity(c.len_utf8() + ident_continue.len());
                ident.push(c);
                ident.push_str(ident_continue);
                Token::Ident(Ident::new_box(ident.into_boxed_str()).unwrap())
            }
            '0'..='9' => {
                let rest = input.as_str();
                let i = rest
                    .find(|c: char| !c.is_ascii_digit())
                    .unwrap_or(rest.len());
                let (int_continue, rest) = rest.split_at(i);
                input = rest.chars();

                let mut ident = String::with_capacity(1 + int_continue.len());
                ident.push(c);
                ident.push_str(int_continue);
                Token::Natural(ident)
            }
            ' ' | '\t' | '\n' => continue,
            _ => {
                reporter.report(format_args!("unexpected character {c:?}"));
                continue;
            }
        });
    }

    if depth != 0 {
        reporter.report("missing closing bracket");
    }

    (tokens, "")
}

#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Ident {
    inner: str,
}

impl Ident {
    fn is_valid(s: &str) -> bool {
        let mut chars = s.chars();
        chars.next().map_or(false, is_xid_start) && chars.all(is_xid_continue)
    }

    pub unsafe fn new_box_unchecked(s: Box<str>) -> Box<Self> {
        unsafe { mem::transmute(s) }
    }

    pub fn new_box(s: Box<str>) -> Option<Box<Self>> {
        Self::is_valid(&s).then(|| unsafe { Self::new_box_unchecked(s) })
    }

    pub fn as_str(&self) -> &str {
        &self.inner
    }
}

impl ToOwned for Ident {
    type Owned = Box<Self>;
    fn to_owned(&self) -> Self::Owned {
        unsafe { Self::new_box_unchecked(self.inner.into()) }
    }
}

use crate::reporter::Reporter;
use std::mem;
use unicode_ident::is_xid_continue;
use unicode_ident::is_xid_start;
