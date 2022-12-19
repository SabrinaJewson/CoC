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
        let Token::Ident(keyword) = token else {
            reporter.report("Expected identifier");
            continue;
        };
        items.push(match keyword.as_str() {
            "def" | "const" => {
                let Some(Token::Ident(ident)) = tokens.next() else {
                    reporter.report("expected identifier");
                    continue;
                };
                let Some(Token::Colon) = tokens.next() else {
                    reporter.report("expected colon");
                    continue;
                };
                let Some(r#type) = parse_term(&mut tokens, reporter) else { continue };

                let body = if keyword.as_str() == "def" {
                    let Some(Token::ColonEq) = tokens.next() else {
                        reporter.report("expected colon equals");
                        continue;
                    };
                    let Some(term) = parse_term(&mut tokens, reporter) else { continue };
                    Some(term)
                } else {
                    None
                };

                let Some(Token::Dot) = tokens.next() else {
                    reporter.report("expected dot");
                    continue;
                };
                Item::Definition(Definition {
                    ident,
                    r#type,
                    body,
                })
            }
            _ => {
                reporter.report(format_args!("unknown item {}", keyword.as_str()));
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
                Token::Colon
                    | Token::ColonEq
                    | Token::Dot
                    | Token::Comma
                    | Token::Plus
                    | Token::Natural(_)
            };
        }

        if let not_term!() = peeked {
            break;
        }

        let term = match tokens.next().unwrap() {
            Token::Ident(ident) if ident.as_str() == "Sort" => {
                let Some(level) = parse_universe_level(tokens, reporter) else {
                    continue;
                };
                Term::Sort { level }
            }
            Token::Ident(ident) => Term::Variable(ident),
            token @ (Token::Lambda | Token::Pi) => {
                let Some(Token::Ident(variable)) = tokens.next() else {
                    reporter.report("expected identifier");
                    return None;
                };
                let Some(Token::Colon) = tokens.next() else {
                    reporter.report("expected colon");
                    return None;
                };
                let r#type = Box::new(parse_term(tokens, reporter)?);
                let Some(Token::Comma) = tokens.next() else {
                    reporter.report("expected comma");
                    return None;
                };
                let body = Box::new(parse_term(tokens, reporter)?);
                Term::Abstraction {
                    kind: match token {
                        Token::Pi => AbstractionKind::Pi,
                        Token::Lambda => AbstractionKind::Lambda,
                        _ => unreachable!(),
                    },
                    variable,
                    r#type,
                    body,
                }
            }
            Token::Delimited(tokens) => {
                let mut tokens = tokens.into_iter().peekable();
                let term = parse_term(&mut tokens, reporter)?;
                if tokens.next().is_some() {
                    reporter.report("trailing tokens");
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
        reporter.report("expected term");
    }

    accumulator
}

fn parse_universe_level<I: Iterator<Item = Token>>(
    tokens: &mut Peekable<I>,
    reporter: &mut impl Reporter,
) -> Option<UniverseLevel> {
    let mut accumulator = match tokens.next() {
        Some(Token::Natural(n)) => {
            let Ok(n) = n.parse::<u32>() else {
                reporter.report("universe level too high");
                return None;
            };
            UniverseLevel::Number(n)
        }
        Some(Token::Ident(ident)) if ["max", "imax"].contains(&ident.as_str()) => {
            let i = ident.as_str() == "imax";
            let left = Box::new(parse_universe_level(tokens, reporter)?);
            let right = Box::new(parse_universe_level(tokens, reporter)?);
            UniverseLevel::Max { i, left, right }
        }
        Some(Token::Ident(ident)) => UniverseLevel::Variable(ident),
        Some(Token::Delimited(tokens)) => {
            let mut tokens = tokens.into_iter().peekable();
            let level = parse_universe_level(&mut tokens, reporter)?;
            if tokens.next().is_some() {
                reporter.report("trailing tokens");
                return None;
            }
            level
        }
        _ => {
            reporter.report("expected universe level");
            return None;
        }
    };

    while let Some(Token::Plus) = tokens.peek() {
        tokens.next();
        let Some(Token::Natural(n)) = tokens.next() else {
            reporter.report("expected natural after `+`");
            return None;
        };
        let Ok(n) = n.parse::<u32>() else {
            reporter.report("universe level too high");
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
use crate::reporter::Reporter;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::iter::Peekable;
