pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

pub enum TokenKind {
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
    let (tokens, rest) = lex_inner(input, 0, 0, reporter);
    assert_eq!(rest, "");
    tokens
}

fn lex_inner<'input>(
    original_input: &'input str,
    depth: usize,
    offset: usize,
    reporter: &mut impl Reporter,
) -> (Vec<Token>, &'input str) {
    let mut tokens = Vec::new();
    let mut input = original_input.chars();

    loop {
        let span_start = string_offset(input.as_str(), original_input) + offset;

        let Some(c) = input.next() else { break };

        let kind = match c {
            ':' if input.as_str().starts_with('=') => {
                input.next();
                TokenKind::ColonEq
            }
            ':' => TokenKind::Colon,
            '.' => TokenKind::Dot,
            ',' => TokenKind::Comma,
            'Π' => TokenKind::Pi,
            'λ' => TokenKind::Lambda,
            '+' => TokenKind::Plus,
            '(' => {
                let (tokens, rest) = lex_inner(input.as_str(), depth + 1, span_start, reporter);
                input = rest.chars();
                TokenKind::Delimited(tokens)
            }
            ')' if depth != 0 => return (tokens, input.as_str()),
            ')' => {
                reporter.error("unexpected closing bracket");
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
                TokenKind::Ident(Ident::new_box(ident.into_boxed_str()).unwrap())
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
                TokenKind::Natural(ident)
            }
            ' ' | '\t' | '\n' => continue,
            _ => {
                reporter.error(format_args!("unexpected character {c:?}"));
                continue;
            }
        };

        let span = Span {
            start: span_start,
            end: string_offset(input.as_str(), original_input) + offset,
        };

        tokens.push(Token { kind, span });
    }

    if depth != 0 {
        reporter.error("missing closing bracket");
    }

    (tokens, input.as_str())
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

fn string_offset(s: &str, base: &str) -> usize {
    (s as *const str as *const () as usize) - (base as *const str as *const () as usize)
}

use crate::reporter::Reporter;
use crate::reporter::Span;
use std::mem;
use unicode_ident::is_xid_continue;
use unicode_ident::is_xid_start;
