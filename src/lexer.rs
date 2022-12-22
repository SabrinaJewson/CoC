#[derive(Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.kind, f)
    }
}

#[derive(Debug, PartialEq)]
pub enum TokenKind {
    Colon,
    ColonEq,
    Dot,
    Comma,
    Pi,
    Lambda,
    Plus,
    Bar,
    Natural(String),
    Ident(Rc<Ident>),
    Delimited(Vec<Token>),
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Colon => f.write_str(":"),
            Self::ColonEq => f.write_str(":="),
            Self::Dot => f.write_str("."),
            Self::Comma => f.write_str(","),
            Self::Pi => f.write_str("Π"),
            Self::Lambda => f.write_str("λ"),
            Self::Plus => f.write_str("+"),
            Self::Bar => f.write_str("|"),
            Self::Natural(n) => Display::fmt(n, f),
            Self::Ident(i) => Display::fmt(i.as_str(), f),
            Self::Delimited(tokens) => {
                f.write_str("(")?;
                for (i, token) in tokens.iter().enumerate() {
                    if i != 0 {
                        f.write_str(" ")?;
                    }
                    Display::fmt(token, f)?;
                }
                f.write_str(")")
            }
        }
    }
}

pub fn lex(input: &str, reporter: &mut Reporter) -> Vec<Token> {
    let (tokens, rest) = lex_inner(input, 0, 0, reporter);
    assert_eq!(rest, "");
    tokens
}

fn lex_inner<'input>(
    original_input: &'input str,
    depth: usize,
    offset: usize,
    reporter: &mut Reporter,
) -> (Vec<Token>, &'input str) {
    let mut tokens = Vec::new();
    let mut input = original_input.chars();

    loop {
        let span_start = string_offset(input.as_str(), original_input) + offset;

        if depth != 0 && input.as_str().starts_with(')') {
            return (tokens, input.as_str());
        }

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
            '|' => TokenKind::Bar,
            '(' => {
                let (tokens, rest) = lex_inner(input.as_str(), depth + 1, span_start + 1, reporter);
                input = rest.chars();
                match input.next() {
                    Some(')') => {}
                    Some(_) => unreachable!(),
                    None => {
                        let span = Span {
                            start: span_start,
                            end: span_start + 1,
                        };
                        reporter.error(span, "missing closing bracket");
                        break;
                    }
                }
                TokenKind::Delimited(tokens)
            }
            c if is_xid_start(c) => {
                let rest = input.as_str();
                let i = rest.find(|c| !is_xid_continue(c)).unwrap_or(rest.len());
                let (ident_continue, rest) = rest.split_at(i);
                input = rest.chars();

                let mut ident = String::with_capacity(c.len_utf8() + ident_continue.len());
                ident.push(c);
                ident.push_str(ident_continue);
                TokenKind::Ident(Ident::new(&ident).unwrap())
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
            // Line comment
            '-' if input.as_str().starts_with('-') => {
                let lines = input.as_str();
                let (_, rest) = lines.split_once('\n').unwrap_or((lines, ""));
                input = rest.chars();
                continue;
            }
            ' ' | '\t' | '\n' => continue,
            _ => {
                let span = Span {
                    start: span_start,
                    end: span_start + c.len_utf8(),
                };
                reporter.error(span, format_args!("unexpected character {c:?}"));
                continue;
            }
        };

        let span = Span {
            start: span_start,
            end: string_offset(input.as_str(), original_input) + offset,
        };

        tokens.push(Token { kind, span });
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

    pub unsafe fn new_rc_unchecked(s: Rc<str>) -> Rc<Self> {
        unsafe { mem::transmute(s) }
    }

    pub fn new(s: &str) -> Option<Rc<Self>> {
        Self::is_valid(s).then(|| unsafe { Self::new_rc_unchecked(s.into()) })
    }

    pub fn as_str(&self) -> &str {
        &self.inner
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

fn string_offset(s: &str, base: &str) -> usize {
    (s as *const str as *const () as usize) - (base as *const str as *const () as usize)
}

use crate::reporter::Reporter;
use crate::reporter::Span;
use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::mem;
use std::rc::Rc;
use unicode_ident::is_xid_continue;
use unicode_ident::is_xid_start;
