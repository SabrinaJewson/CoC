pub struct Definition {
    pub r#type: Term,
    pub body: Option<Term>,
}

#[derive(Clone, PartialEq, Eq)]
pub enum Term {
    Sort { level: UniverseLevel },
    Variable(Variable),
    Abstraction { r#type: Box<Term>, body: Box<Term> },
    Pi { r#type: Box<Term>, body: Box<Term> },
    Application { left: Box<Term>, right: Box<Term> },
}

impl Debug for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sort { level } => write!(f, "Sort {level:?}"),
            Self::Variable(v) => write!(f, "{}", v.0),
            Self::Abstraction { r#type, body } => write!(f, "(λ {type:?}, {body:?})"),
            Self::Pi { r#type, body } => write!(f, "(Π {type:?}, {body:?})"),
            Self::Application { left, right } => write!(f, "({left:?} {right:?})"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UniverseLevel {
    Number(u32),
    Variable(UniverseVariable),
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
                variables.push(def.ident);
                Definition { r#type, body }
            }
        });
    }

    definitions
}

fn resolve_term(
    variables: &mut Vec<Box<Ident>>,
    term: parser::Term,
    reporter: &mut impl Reporter,
) -> Option<Term> {
    Some(match term {
        parser::Term::Sort { level } => Term::Sort {
            level: resolve_universe_level(level, reporter)?,
        },
        parser::Term::Variable(v) => {
            let index = variables.iter().rev().position(|local| *local == v);
            let Some(index) = index else {
                reporter.report(format_args!("unknown variable {}", v.as_str()));
                return None;
            };

            Term::Variable(Variable(index))
        }
        parser::Term::Abstraction {
            variable,
            r#type,
            body,
        } => {
            let r#type = Box::new(resolve_term(variables, *r#type, reporter)?);

            variables.push(variable);
            let body = Box::new(resolve_term(variables, *body, reporter)?);
            variables.pop();

            Term::Abstraction { r#type, body }
        }
        parser::Term::Pi {
            variable,
            r#type,
            body,
        } => {
            let r#type = Box::new(resolve_term(variables, *r#type, reporter)?);

            variables.push(variable);
            let body = Box::new(resolve_term(variables, *body, reporter)?);
            variables.pop();

            Term::Pi { r#type, body }
        }
        parser::Term::Application { left, right } => {
            let left = Box::new(resolve_term(variables, *left, reporter)?);
            let right = Box::new(resolve_term(variables, *right, reporter)?);
            Term::Application { left, right }
        }
    })
}

fn resolve_universe_level(
    level: parser::UniverseLevel,
    reporter: &mut impl Reporter,
) -> Option<UniverseLevel> {
    Some(match level {
        parser::UniverseLevel::Number(n) => UniverseLevel::Number(n),
        parser::UniverseLevel::Variable(v) => {
            reporter.report(format_args!("unknown universe variable {}", v.as_str()));
            return None;
        }
        parser::UniverseLevel::Addition { left, right } => UniverseLevel::Addition {
            left: Box::new(resolve_universe_level(*left, reporter)?),
            right,
        },
        parser::UniverseLevel::Max { i, left, right } => UniverseLevel::Max {
            i,
            left: Box::new(resolve_universe_level(*left, reporter)?),
            right: Box::new(resolve_universe_level(*right, reporter)?),
        },
    })
}

pub fn replace(term: &Term, with: &Term) -> Term {
    replace_inner(term, with, 0)
}

fn replace_inner(term: &Term, with: &Term, depth: usize) -> Term {
    match term {
        Term::Variable(v) if v.0 == depth => increase_free(with, depth),
        Term::Variable(v) if v.0 > depth => Term::Variable(Variable(v.0 - 1)),
        Term::Abstraction { r#type, body } => {
            let r#type = Box::new(replace_inner(r#type, with, depth));
            let body = Box::new(replace_inner(body, with, depth + 1));
            Term::Abstraction { r#type, body }
        }
        Term::Pi { r#type, body } => {
            let r#type = Box::new(replace_inner(r#type, with, depth));
            let body = Box::new(replace_inner(body, with, depth + 1));
            Term::Pi { r#type, body }
        }
        Term::Application { left, right } => {
            let left = Box::new(replace_inner(left, with, depth));
            let right = Box::new(replace_inner(right, with, depth));
            Term::Application { left, right }
        }
        _ => term.clone(),
    }
}

pub fn increase_free(term: &Term, by: usize) -> Term {
    increase_free_inner(term, by, 0)
}

fn increase_free_inner(term: &Term, by: usize, lowest_free: usize) -> Term {
    match term {
        Term::Variable(v) if v.0 >= lowest_free => Term::Variable(Variable(v.0 + by)),
        Term::Abstraction { r#type, body } => {
            let r#type = Box::new(increase_free_inner(r#type, by, lowest_free));
            let body = Box::new(increase_free_inner(body, by, lowest_free + 1));
            Term::Abstraction { r#type, body }
        }
        Term::Pi { r#type, body } => {
            let r#type = Box::new(increase_free_inner(r#type, by, lowest_free));
            let body = Box::new(increase_free_inner(body, by, lowest_free + 1));
            Term::Pi { r#type, body }
        }
        Term::Application { left, right } => {
            let left = Box::new(increase_free_inner(left, by, lowest_free));
            let right = Box::new(increase_free_inner(right, by, lowest_free));
            Term::Application { left, right }
        }
        _ => term.clone(),
    }
}

use crate::lexer::Ident;
use crate::parser;
use crate::reporter::Reporter;
use core::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
