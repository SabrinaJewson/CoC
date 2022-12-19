pub struct Source {
    pub items: Vec<Item>,
}

pub enum Item {
    Definition(Definition),
}

pub struct Definition {
    pub ident: Ident,
    pub r#type: Term,
    pub body: Option<Term>,
    pub span: Span,
}

pub struct Ident {
    pub name: Box<lexer::Ident>,
    pub span: Span,
}

pub struct Term {
    pub kind: TermKind,
    pub span: Span,
}

pub enum TermKind {
    Sort {
        level: UniverseLevel,
    },
    Variable(Box<lexer::Ident>),
    Abstraction {
        token: AbstractionToken,
        variable: Ident,
        r#type: Box<Term>,
        body: Box<Term>,
    },
    Application {
        left: Box<Term>,
        right: Box<Term>,
    },
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AbstractionToken {
    Pi,
    Lambda,
}

impl Debug for AbstractionToken {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Pi => "Π",
            Self::Lambda => "λ",
        })
    }
}

pub struct UniverseLevel {
    pub kind: UniverseLevelKind,
    pub span: Span,
}

pub enum UniverseLevelKind {
    Lit(UniverseLevelLit),
    Variable(Box<lexer::Ident>),
    Addition {
        left: Box<UniverseLevel>,
        right: UniverseLevelLit,
    },
    Max {
        i: bool,
        left: Box<UniverseLevel>,
        right: Box<UniverseLevel>,
    },
}

#[derive(Clone, Copy)]
pub struct UniverseLevelLit {
    pub value: u32,
    pub span: Span,
}

impl PartialEq for UniverseLevelLit {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl Display for UniverseLevelLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.value, f)
    }
}

pub fn parse(tokens: impl IntoIterator<Item = Token>, reporter: &mut impl Reporter) -> Source {
    let mut tokens = tokens.into_iter().peekable();

    let mut items = Vec::new();

    while let Some(token) = tokens.next() {
        let start_span = token.span;
        let TokenKind::Ident(keyword) = token.kind else {
            reporter.error("Expected identifier");
            continue;
        };
        items.push(match keyword.as_str() {
            kw::DEFINITION | kw::CONSTANT => {
                let Some(ident) = tokens.next().and_then(ident_token) else {
                    reporter.error("expected identifier");
                    continue;
                };
                let Some(Token { kind: TokenKind::Colon, .. }) = tokens.next() else {
                    reporter.error("expected colon");
                    continue;
                };
                let Some(r#type) = parse_term(&mut tokens, reporter) else { continue };

                let body = match keyword.as_str() {
                    kw::DEFINITION => {
                        let Some(Token { kind: TokenKind::ColonEq, .. }) = tokens.next() else {
                            reporter.error("expected colon equals");
                            continue;
                        };
                        let Some(term) = parse_term(&mut tokens, reporter) else { continue };
                        Some(term)
                    }
                    kw::CONSTANT => None,
                    _ => unreachable!(),
                };

                let Some(Token { kind: TokenKind::Dot, span: end_span }) = tokens.next() else {
                    reporter.error("expected dot");
                    continue;
                };

                Item::Definition(Definition {
                    span: start_span.join(end_span),
                    ident,
                    r#type,
                    body,
                })
            }
            _ => {
                reporter.error(format_args!("unknown item {}", keyword.as_str()));
                continue;
            }
        });
    }

    Source { items }
}

mod kw {
    pub const DEFINITION: &str = "def";
    pub const CONSTANT: &str = "constant";
}

fn parse_term<I>(tokens: &mut Peekable<I>, reporter: &mut impl Reporter) -> Option<Term>
where
    I: Iterator<Item = Token>,
{
    let mut accumulator: Option<Term> = None;

    while let Some(peeked) = tokens.peek() {
        macro_rules! not_term {
            () => {
                TokenKind::Colon
                    | TokenKind::ColonEq
                    | TokenKind::Dot
                    | TokenKind::Comma
                    | TokenKind::Plus
                    | TokenKind::Natural(_)
            };
        }

        if let not_term!() = peeked.kind {
            break;
        }

        let token = tokens.next().unwrap();
        let start_span = token.span;
        let term = match token.kind {
            TokenKind::Ident(ident) if ident.as_str() == "Sort" => {
                let Some(level) = parse_universe_level(tokens, reporter) else {
                    continue;
                };
                Term {
                    span: start_span.join(level.span),
                    kind: TermKind::Sort { level },
                }
            }
            TokenKind::Ident(ident) => Term {
                kind: TermKind::Variable(ident),
                span: start_span,
            },
            token @ (TokenKind::Lambda | TokenKind::Pi) => {
                let Some(variable) = tokens.next().and_then(ident_token) else {
                    reporter.error("expected identifier");
                    return None;
                };
                let Some(Token { kind: TokenKind::Colon, .. }) = tokens.next() else {
                    reporter.error("expected colon");
                    return None;
                };
                let r#type = Box::new(parse_term(tokens, reporter)?);
                let Some(Token { kind: TokenKind::Comma, .. }) = tokens.next() else {
                    reporter.error("expected comma");
                    return None;
                };
                let body = Box::new(parse_term(tokens, reporter)?);
                Term {
                    span: start_span.join(body.span),
                    kind: TermKind::Abstraction {
                        token: match token {
                            TokenKind::Pi => AbstractionToken::Pi,
                            TokenKind::Lambda => AbstractionToken::Lambda,
                            _ => unreachable!(),
                        },
                        variable,
                        r#type,
                        body,
                    },
                }
            }
            TokenKind::Delimited(tokens) => {
                let mut tokens = tokens.into_iter().peekable();
                let term = parse_term(&mut tokens, reporter)?;
                if tokens.next().is_some() {
                    reporter.error("trailing tokens");
                    return None;
                }
                term
            }
            not_term!() => unreachable!(),
        };

        accumulator = Some(if let Some(left) = accumulator {
            Term {
                span: left.span.join(term.span),
                kind: TermKind::Application {
                    left: Box::new(left),
                    right: Box::new(term),
                },
            }
        } else {
            term
        });
    }

    if accumulator.is_none() {
        reporter.error("expected term");
    }

    accumulator
}

fn parse_universe_level<I: Iterator<Item = Token>>(
    tokens: &mut Peekable<I>,
    reporter: &mut impl Reporter,
) -> Option<UniverseLevel> {
    let Some(token) = tokens.next() else {
        reporter.error("expected universe level");
        return None;
    };

    let start_span = token.span;

    let mut accumulator = match token.kind {
        TokenKind::Natural(n) => {
            let lit = parse_universe_level_lit(&n, start_span, reporter)?;
            UniverseLevel {
                kind: UniverseLevelKind::Lit(lit),
                span: start_span,
            }
        }
        TokenKind::Ident(ident) if ["max", "imax"].contains(&ident.as_str()) => {
            let i = ident.as_str() == "imax";
            let left = Box::new(parse_universe_level(tokens, reporter)?);
            let right = Box::new(parse_universe_level(tokens, reporter)?);
            UniverseLevel {
                span: start_span.join(right.span),
                kind: UniverseLevelKind::Max { i, left, right },
            }
        }
        TokenKind::Ident(ident) => UniverseLevel {
            kind: UniverseLevelKind::Variable(ident),
            span: start_span,
        },
        TokenKind::Delimited(tokens) => {
            let mut tokens = tokens.into_iter().peekable();
            let level = parse_universe_level(&mut tokens, reporter)?;
            if tokens.next().is_some() {
                reporter.error("trailing tokens");
                return None;
            }
            level
        }
        _ => {
            reporter.error("expected universe level");
            return None;
        }
    };

    while tokens
        .peek()
        .map_or(false, |t| matches!(t.kind, TokenKind::Plus))
    {
        tokens.next();
        let Some(Token { kind: TokenKind::Natural(n), span }) = tokens.next() else {
            reporter.error("expected natural after `+`");
            return None;
        };
        let lit = parse_universe_level_lit(&n, span, reporter)?;
        accumulator = UniverseLevel {
            span: accumulator.span.join(span),
            kind: UniverseLevelKind::Addition {
                left: Box::new(accumulator),
                right: lit,
            },
        };
    }

    Some(accumulator)
}

fn parse_universe_level_lit(
    nat: &str,
    span: Span,
    reporter: &mut impl Reporter,
) -> Option<UniverseLevelLit> {
    let Ok(value) = nat.parse::<u32>() else {
        reporter.error("universe level too high");
        return None;
    };
    Some(UniverseLevelLit { value, span })
}

fn ident_token(token: lexer::Token) -> Option<Ident> {
    match token.kind {
        TokenKind::Ident(name) => Some(Ident {
            name,
            span: token.span,
        }),
        _ => None,
    }
}

use crate::lexer;
use crate::lexer::Token;
use crate::lexer::TokenKind;
use crate::reporter::Reporter;
use crate::reporter::Span;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::iter::Peekable;
