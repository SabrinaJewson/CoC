pub struct Definition {
    pub r#type: Term,
    pub body: Option<Term>,
}

#[derive(Clone)]
pub struct Term {
    pub span: Span,
    pub kind: TermKind,
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Debug for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.kind, f)
    }
}

#[derive(Clone, PartialEq)]
pub enum TermKind {
    Sort {
        level: UniverseLevel,
    },
    Variable(Variable),
    Abstraction {
        token: AbstractionToken,
        r#type: Box<Term>,
        body: Box<Term>,
    },
    Application {
        left: Box<Term>,
        right: Box<Term>,
    },
    Error,
}

impl Debug for TermKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sort { level } => write!(f, "Sort {level:?}"),
            Self::Variable(v) => write!(f, "{}", v.0),
            Self::Abstraction {
                token,
                r#type,
                body,
            } => write!(f, "({token:?} {type:?}, {body:?})"),
            Self::Application { left, right } => write!(f, "({left:?} {right:?})"),
            Self::Error => f.write_str("[error]"),
        }
    }
}

#[derive(Clone)]
pub struct UniverseLevel {
    pub kind: UniverseLevelKind,
    pub span: Span,
}

impl Debug for UniverseLevel {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.kind, f)
    }
}

impl PartialEq for UniverseLevel {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

#[derive(Clone, PartialEq)]
pub enum UniverseLevelKind {
    Lit(UniverseLevelLit),
    Variable(UniverseVariable),
    Addition {
        left: Box<UniverseLevel>,
        right: Option<UniverseLevelLit>,
    },
    Max {
        i: bool,
        left: Box<UniverseLevel>,
        right: Box<UniverseLevel>,
    },
    Error,
}

impl Debug for UniverseLevelKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lit(lit) => write!(f, "{lit}"),
            Self::Variable(variable) => match *variable {},
            Self::Addition {
                left,
                right: Some(right),
            } => write!(f, "({left:?} + {right})"),
            Self::Addition { left, right: None } => write!(f, "({left:?} + [error])"),
            Self::Max { i, left, right } => {
                let max = if *i { "imax" } else { "max" };
                write!(f, "({max} {left:?} {right:?})")
            }
            Self::Error => f.write_str("[error]"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Variable(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UniverseVariable {}

pub fn resolve(items: Vec<parser::Item>, reporter: &mut impl Reporter) -> Vec<Definition> {
    let mut variables = Vec::new();
    let mut definitions = Vec::new();

    for item in items {
        definitions.push(match item {
            parser::Item::Definition(def) => {
                let Some(r#type) = resolve_term(&mut variables, def.r#type, reporter)
                    else { continue };
                let body = match def.body {
                    Some(body) => {
                        let Some(body) = resolve_term(&mut variables, body, reporter)
                            else { continue };
                        Some(body)
                    }
                    None => None,
                };
                variables.push(def.ident.name);
                Definition { r#type, body }
            }
        });
    }

    definitions
}

fn resolve_term(
    variables: &mut Vec<Box<lexer::Ident>>,
    term: parser::Term,
    reporter: &mut impl Reporter,
) -> Option<Term> {
    let kind = match term.kind {
        parser::TermKind::Sort { level } => TermKind::Sort {
            level: resolve_universe_level(level, reporter)?,
        },
        parser::TermKind::Variable(v) => {
            let index = variables.iter().rev().position(|local| *local == v);
            let Some(index) = index else {
                reporter.error(term.span, format_args!("unknown variable {}", v.as_str()));
                return None;
            };

            TermKind::Variable(Variable(index))
        }
        parser::TermKind::Abstraction {
            token,
            variable,
            r#type,
            body,
        } => {
            let r#type = Box::new(resolve_term(variables, *r#type, reporter)?);

            variables.push(variable.name);
            let body = Box::new(resolve_term(variables, *body, reporter)?);
            variables.pop();

            TermKind::Abstraction {
                token,
                r#type,
                body,
            }
        }
        parser::TermKind::Application { left, right } => {
            let left = Box::new(resolve_term(variables, *left, reporter)?);
            let right = Box::new(resolve_term(variables, *right, reporter)?);
            TermKind::Application { left, right }
        }
        parser::TermKind::Error => TermKind::Error,
    };
    let span = term.span;
    Some(Term { kind, span })
}

fn resolve_universe_level(
    level: parser::UniverseLevel,
    reporter: &mut impl Reporter,
) -> Option<UniverseLevel> {
    let kind = match level.kind {
        parser::UniverseLevelKind::Lit(n) => UniverseLevelKind::Lit(n),
        parser::UniverseLevelKind::Variable(v) => {
            reporter.error(
                level.span,
                format_args!("unknown universe variable {}", v.as_str()),
            );
            return None;
        }
        parser::UniverseLevelKind::Addition { left, right } => UniverseLevelKind::Addition {
            left: Box::new(resolve_universe_level(*left, reporter)?),
            right,
        },
        parser::UniverseLevelKind::Max { i, left, right } => UniverseLevelKind::Max {
            i,
            left: Box::new(resolve_universe_level(*left, reporter)?),
            right: Box::new(resolve_universe_level(*right, reporter)?),
        },
        parser::UniverseLevelKind::Error => UniverseLevelKind::Error,
    };
    let span = level.span;
    Some(UniverseLevel { kind, span })
}

pub fn replace(term: Term, with: &Term) -> Term {
    replace_inner(term, with, 0)
}

fn replace_inner(term: Term, with: &Term, depth: usize) -> Term {
    let kind = match term.kind {
        // The substitution itself
        TermKind::Variable(v) if v.0 == depth => return increase_free(with, depth),
        // Decrease free variables indices
        TermKind::Variable(v) if v.0 > depth => TermKind::Variable(Variable(v.0 - 1)),
        TermKind::Abstraction {
            token,
            r#type,
            body,
        } => {
            let r#type = Box::new(replace_inner(*r#type, with, depth));
            let body = Box::new(replace_inner(*body, with, depth + 1));
            TermKind::Abstraction {
                token,
                r#type,
                body,
            }
        }
        TermKind::Application { left, right } => {
            let left = Box::new(replace_inner(*left, with, depth));
            let right = Box::new(replace_inner(*right, with, depth));
            TermKind::Application { left, right }
        }
        _ => term.kind,
    };
    let span = term.span;
    Term { kind, span }
}

pub fn increase_free(term: &Term, by: usize) -> Term {
    increase_free_inner(term, by, 0)
}

fn increase_free_inner(term: &Term, by: usize, lowest_free: usize) -> Term {
    let kind = match &term.kind {
        TermKind::Variable(v) if v.0 >= lowest_free => TermKind::Variable(Variable(v.0 + by)),
        TermKind::Abstraction {
            token,
            r#type,
            body,
        } => {
            let &token = token;
            let r#type = Box::new(increase_free_inner(r#type, by, lowest_free));
            let body = Box::new(increase_free_inner(body, by, lowest_free + 1));
            TermKind::Abstraction {
                token,
                r#type,
                body,
            }
        }
        TermKind::Application { left, right } => {
            let left = Box::new(increase_free_inner(left, by, lowest_free));
            let right = Box::new(increase_free_inner(right, by, lowest_free));
            TermKind::Application { left, right }
        }
        _ => term.kind.clone(),
    };
    let span = term.span;
    Term { span, kind }
}

use crate::lexer;
use crate::parser;
use crate::parser::AbstractionToken;
use crate::parser::UniverseLevelLit;
use crate::reporter::Reporter;
use crate::reporter::Span;
use core::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
