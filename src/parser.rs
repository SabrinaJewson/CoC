pub struct Source {
    pub items: Vec<Item>,
}

pub enum Item {
    Definition(Definition),
}

pub struct Definition {
    pub ident: Box<Ident>,
    pub r#type: Term,
    pub body: Option<Term>,
}

pub enum Term {
    Sort {
        level: UniverseLevel,
    },
    Variable(Box<Ident>),
    Abstraction {
        kind: AbstractionKind,
        variable: Box<Ident>,
        r#type: Box<Term>,
        body: Box<Term>,
    },
    Application {
        left: Box<Term>,
        right: Box<Term>,
    },
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AbstractionKind {
    Pi,
    Lambda,
}

impl Debug for AbstractionKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Pi => "Π",
            Self::Lambda => "λ",
        })
    }
}

pub enum UniverseLevel {
    Number(u32),
    Variable(Box<Ident>),
    Addition {
        left: Box<UniverseLevel>,
        right: u32,
    },
    Max {
        i: bool,
        left: Box<UniverseLevel>,
        right: Box<UniverseLevel>,
    },
}

pub fn parse(tokens: impl IntoIterator<Item = Token>, reporter: &mut impl Reporter) -> Source {
    let mut tokens = tokens.into_iter().peekable();

    let mut items = Vec::new();

    while let Some(token) = tokens.next() {
        let TokenKind::Ident(keyword) = token.kind else {
            reporter.error("Expected identifier");
            continue;
        };
        items.push(match keyword.as_str() {
            "def" | "const" => {
                let Some(Token { kind: TokenKind::Ident(ident), .. }) = tokens.next() else {
                    reporter.error("expected identifier");
                    continue;
                };
                let Some(Token { kind: TokenKind::Colon, .. }) = tokens.next() else {
                    reporter.error("expected colon");
                    continue;
                };
                let Some(r#type) = parse_term(&mut tokens, reporter) else { continue };

                let body = if keyword.as_str() == "def" {
                    let Some(Token { kind: TokenKind::ColonEq, .. }) = tokens.next() else {
                        reporter.error("expected colon equals");
                        continue;
                    };
                    let Some(term) = parse_term(&mut tokens, reporter) else { continue };
                    Some(term)
                } else {
                    None
                };

                let Some(Token { kind: TokenKind::Dot, .. }) = tokens.next() else {
                    reporter.error("expected dot");
                    continue;
                };
                Item::Definition(Definition {
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

fn parse_term<I>(tokens: &mut Peekable<I>, reporter: &mut impl Reporter) -> Option<Term>
where
    I: Iterator<Item = Token>,
{
    let mut accumulator = None;

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

        let term = match tokens.next().unwrap().kind {
            TokenKind::Ident(ident) if ident.as_str() == "Sort" => {
                let Some(level) = parse_universe_level(tokens, reporter) else {
                    continue;
                };
                Term::Sort { level }
            }
            TokenKind::Ident(ident) => Term::Variable(ident),
            token @ (TokenKind::Lambda | TokenKind::Pi) => {
                let Some(Token { kind: TokenKind::Ident(variable), .. }) = tokens.next() else {
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
                Term::Abstraction {
                    kind: match token {
                        TokenKind::Pi => AbstractionKind::Pi,
                        TokenKind::Lambda => AbstractionKind::Lambda,
                        _ => unreachable!(),
                    },
                    variable,
                    r#type,
                    body,
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
            Term::Application {
                left: Box::new(left),
                right: Box::new(term),
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

    let mut accumulator = match token.kind {
        TokenKind::Natural(n) => {
            let Ok(n) = n.parse::<u32>() else {
                reporter.error("universe level too high");
                return None;
            };
            UniverseLevel::Number(n)
        }
        TokenKind::Ident(ident) if ["max", "imax"].contains(&ident.as_str()) => {
            let i = ident.as_str() == "imax";
            let left = Box::new(parse_universe_level(tokens, reporter)?);
            let right = Box::new(parse_universe_level(tokens, reporter)?);
            UniverseLevel::Max { i, left, right }
        }
        TokenKind::Ident(ident) => UniverseLevel::Variable(ident),
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
        let Some(Token { kind: TokenKind::Natural(n), .. }) = tokens.next() else {
            reporter.error("expected natural after `+`");
            return None;
        };
        let Ok(n) = n.parse::<u32>() else {
            reporter.error("universe level too high");
            return None;
        };
        accumulator = UniverseLevel::Addition {
            left: Box::new(accumulator),
            right: n,
        };
    }

    Some(accumulator)
}

use crate::lexer::Ident;
use crate::lexer::Token;
use crate::lexer::TokenKind;
use crate::reporter::Reporter;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::iter::Peekable;
