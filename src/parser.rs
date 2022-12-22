pub struct Source {
    pub items: Vec<Item>,
}

pub enum Item {
    Definition(Definition),
    Inductive(Inductive),
}

pub struct Definition {
    pub ident: Ident,
    pub r#type: Term,
    pub body: Option<Term>,
    pub span: Span,
}

pub struct Inductive {
    pub ident: Ident,
    pub params: Vec<ParamGroup>,
    pub sort: Term,
    pub constructors: Vec<Constructor>,
    pub span: Span,
}

pub struct ParamGroup {
    pub idents: Vec<Ident>,
    pub r#type: Term,
}

pub struct Constructor {
    pub ident: Ident,
    pub r#type: Term,
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
    Error,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AbstractionToken {
    Pi,
    Lambda,
}

impl Display for AbstractionToken {
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
        /// `None` indicates an error
        right: Option<UniverseLevelLit>,
    },
    Max {
        i: bool,
        left: Box<UniverseLevel>,
        right: Box<UniverseLevel>,
    },
    Error,
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

pub struct Ident {
    pub name: Box<lexer::Ident>,
    pub span: Span,
}

pub fn parse(tokens: impl IntoIterator<Item = Token>, reporter: &mut Reporter) -> Source {
    let mut tokens = tokens.into_iter().peekable();

    let mut items = Vec::new();

    while tokens.peek().is_some() {
        let Some(item) = parse_item(&mut tokens, reporter) else { break };
        items.push(item);
    }

    Source { items }
}

fn parse_item(
    tokens: &mut Peekable<impl Iterator<Item = Token>>,
    reporter: &mut Reporter,
) -> Option<Item> {
    let keyword_token = tokens.next().unwrap();

    let start_span = keyword_token.span;
    let TokenKind::Ident(keyword) = keyword_token.kind else {
        reporter.error(keyword_token.span, "expected command name");
        return None;
    };
    Some(match keyword.as_str() {
        kw::DEFINITION | kw::CONSTANT => {
            let ident = parse_ident(tokens, start_span, reporter)?;

            let colon_span = parse_exact(
                tokens,
                TokenKind::Colon,
                start_span.join(ident.span),
                reporter,
            )?;

            let r#type = parse_term(tokens, start_span.join(colon_span), reporter)?;

            let body = match keyword.as_str() {
                kw::DEFINITION => {
                    let colon_eq_span = parse_exact(
                        tokens,
                        TokenKind::ColonEq,
                        start_span.join(r#type.span),
                        reporter,
                    )?;
                    let term = parse_term(tokens, start_span.join(colon_eq_span), reporter)?;
                    Some(term)
                }
                kw::CONSTANT => None,
                _ => unreachable!(),
            };

            let current_span = start_span.join(body.as_ref().map_or(r#type.span, |t| t.span));
            let dot_span = parse_exact(tokens, TokenKind::Dot, current_span, reporter)?;

            Item::Definition(Definition {
                span: start_span.join(dot_span),
                ident,
                r#type,
                body,
            })
        }
        kw::INDUCTIVE => {
            let ident = parse_ident(tokens, start_span, reporter)?;

            let mut params = Vec::new();
            while let Some(token) = tokens.next_if(|t| matches!(t.kind, TokenKind::Delimited(_))) {
                let TokenKind::Delimited(tokens) = token.kind else { unreachable!() };
                let param_group = with_delimited(tokens, reporter, |tokens, reporter| {
                    parse_param_group(tokens, token.span, reporter)
                });
                if let Some(param_group) = param_group {
                    params.push(param_group);
                }
            }

            let current_span = start_span.join(params.last().map_or(ident.span, |p| p.r#type.span));
            let colon_span = parse_exact(tokens, TokenKind::Colon, current_span, reporter)?;

            let sort = parse_term(tokens, start_span.join(colon_span), reporter)?;

            let mut constructors = Vec::new();
            while let Some(bar_token) = tokens.next_if(|t| t.kind == TokenKind::Bar) {
                let ident = parse_ident(tokens, bar_token.span, reporter)?;
                let colon_span = parse_exact(tokens, TokenKind::Colon, ident.span, reporter)?;
                let r#type = parse_term(tokens, ident.span.join(colon_span), reporter)?;
                constructors.push(Constructor { ident, r#type });
            }

            let current_span =
                start_span.join(constructors.last().map_or(sort.span, |c| c.r#type.span));
            let dot_span = parse_exact(tokens, TokenKind::Dot, current_span, reporter)?;

            Item::Inductive(Inductive {
                ident,
                params,
                sort,
                constructors,
                span: start_span.join(dot_span),
            })
        }
        _ => {
            reporter.error(
                start_span,
                format_args!("unknown item {}", keyword.as_str()),
            );
            return None;
        }
    })
}

mod kw {
    pub const DEFINITION: &str = "def";
    pub const CONSTANT: &str = "constant";
    pub const INDUCTIVE: &str = "inductive";
}

fn parse_param_group(
    tokens: &mut Peekable<impl Iterator<Item = Token>>,
    fallback_span: Span,
    reporter: &mut Reporter,
) -> Option<ParamGroup> {
    let first_ident = parse_ident(tokens, fallback_span, reporter)?;

    let mut idents = vec![first_ident];
    while let Some(token) = tokens.next_if(|t| matches!(t.kind, TokenKind::Ident(_))) {
        let TokenKind::Ident(name) = token.kind else { unreachable!() };
        let span = token.span;
        idents.push(Ident { name, span });
    }

    let colon_span = parse_exact(tokens, TokenKind::Colon, fallback_span, reporter)?;

    let r#type = parse_term(tokens, colon_span, reporter)?;

    Some(ParamGroup { idents, r#type })
}

fn parse_term(
    tokens: &mut Peekable<impl Iterator<Item = Token>>,
    fallback_span: Span,
    reporter: &mut Reporter,
) -> Option<Term> {
    let mut accumulator: Option<Term> = None;

    while let Some(peeked) = tokens.peek() {
        macro_rules! not_term {
            () => {
                TokenKind::Colon
                    | TokenKind::ColonEq
                    | TokenKind::Dot
                    | TokenKind::Comma
                    | TokenKind::Plus
                    | TokenKind::Bar
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
                let level = parse_universe_level(tokens, start_span, reporter);
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
                let variable = parse_ident(tokens, start_span, reporter)?;

                let colon_span = parse_exact(
                    tokens,
                    TokenKind::Colon,
                    start_span.join(variable.span),
                    reporter,
                )?;

                let r#type = parse_term(tokens, start_span.join(colon_span), reporter)?;
                let r#type = Box::new(r#type);

                let comma_span = parse_exact(
                    tokens,
                    TokenKind::Comma,
                    start_span.join(r#type.span),
                    reporter,
                )?;

                let body = parse_term(tokens, start_span.join(comma_span), reporter)?;
                let body = Box::new(body);
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
            TokenKind::Delimited(tokens) => with_delimited(tokens, reporter, |tokens, reporter| {
                parse_term(tokens, start_span, reporter)
            })
            .unwrap_or(Term {
                kind: TermKind::Error,
                span: start_span,
            }),
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
        reporter.error(fallback_span, "expected term");
    }

    accumulator
}

fn parse_universe_level<I: Iterator<Item = Token>>(
    tokens: &mut Peekable<I>,
    fallback_span: Span,
    reporter: &mut Reporter,
) -> UniverseLevel {
    let Some(token) = tokens.next() else {
        reporter.error(fallback_span, "expected universe level");
        return UniverseLevel {
            kind: UniverseLevelKind::Error,
            span: fallback_span,
        };
    };

    let start_span = token.span;

    let mut accumulator = match token.kind {
        TokenKind::Natural(n) => {
            let kind = match parse_universe_level_lit(&n, start_span, reporter) {
                Some(lit) => UniverseLevelKind::Lit(lit),
                None => UniverseLevelKind::Error,
            };
            UniverseLevel {
                kind,
                span: start_span,
            }
        }
        TokenKind::Ident(ident) if ["max", "imax"].contains(&ident.as_str()) => {
            let i = ident.as_str() == "imax";
            let left = parse_universe_level(tokens, start_span, reporter);
            let right = parse_universe_level(tokens, start_span.join(left.span), reporter);
            let left = Box::new(left);
            let right = Box::new(right);
            UniverseLevel {
                span: start_span.join(right.span),
                kind: UniverseLevelKind::Max { i, left, right },
            }
        }
        TokenKind::Ident(ident) => UniverseLevel {
            kind: UniverseLevelKind::Variable(ident),
            span: start_span,
        },
        TokenKind::Delimited(tokens) => with_delimited(tokens, reporter, |tokens, reporter| {
            Some(parse_universe_level(tokens, start_span, reporter))
        })
        .unwrap(),
        _ => {
            reporter.error(start_span, "expected universe level");
            UniverseLevel {
                kind: UniverseLevelKind::Error,
                span: start_span,
            }
        }
    };

    while tokens
        .peek()
        .map_or(false, |t| matches!(t.kind, TokenKind::Plus))
    {
        let plus_token = tokens.next().unwrap();

        let lit = match tokens.peek() {
            Some(token) => {
                let span = token.span;
                match &token.kind {
                    TokenKind::Natural(_) => {
                        let TokenKind::Natural(n) = tokens.next().unwrap().kind
                            else { unreachable!() };
                        parse_universe_level_lit(&n, span, reporter)
                    }
                    _ => None,
                }
            }
            None => None,
        };
        accumulator = UniverseLevel {
            span: accumulator
                .span
                .join(lit.map_or(plus_token.span, |lit| lit.span)),
            kind: UniverseLevelKind::Addition {
                left: Box::new(accumulator),
                right: lit,
            },
        };
    }

    accumulator
}

fn with_delimited<O>(
    tokens: Vec<Token>,
    reporter: &mut Reporter,
    f: impl FnOnce(&mut Peekable<vec::IntoIter<Token>>, &mut Reporter) -> Option<O>,
) -> Option<O> {
    let mut tokens = tokens.into_iter().peekable();
    let out = f(&mut tokens, reporter)?;
    if let Some(span) = tokens.map(|t| t.span).reduce(Span::join) {
        reporter.error(span, "trailing tokens");
    }
    Some(out)
}

fn parse_universe_level_lit(
    nat: &str,
    span: Span,
    reporter: &mut Reporter,
) -> Option<UniverseLevelLit> {
    let Ok(value) = nat.parse::<u32>() else {
        reporter.error(span, "universe level too high");
        return None;
    };
    Some(UniverseLevelLit { value, span })
}

fn parse_exact(
    tokens: &mut Peekable<impl Iterator<Item = Token>>,
    exact: TokenKind,
    fallback_span: Span,
    reporter: &mut Reporter,
) -> Option<Span> {
    match tokens.next() {
        Some(token) if token.kind == exact => Some(token.span),
        Some(token) => {
            reporter.error(
                token.span,
                format_args!("expected `{exact}`, found `{token}`"),
            );
            None
        }
        None => {
            reporter.error(
                fallback_span,
                format_args!("unexpected EOF, expected `{exact}`"),
            );
            None
        }
    }
}

fn parse_ident(
    tokens: &mut Peekable<impl Iterator<Item = Token>>,
    fallback_span: Span,
    reporter: &mut Reporter,
) -> Option<Ident> {
    let Some(token) = tokens.next() else {
        reporter.error(fallback_span, "unexpected EOF, expected identifier");
        return None;
    };
    let span = token.span;
    Some(match token.kind {
        TokenKind::Ident(name) => Ident { name, span },
        _ => {
            reporter.error(span, format_args!("expected identifier, found `{token}`"));
            return None;
        }
    })
}

use crate::lexer;
use crate::lexer::Token;
use crate::lexer::TokenKind;
use crate::reporter::Reporter;
use crate::reporter::Span;
use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::iter::Peekable;
use std::vec;
