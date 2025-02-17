pub enum Item {
    Definition(Definition),
    Inductive(Inductive),
}

pub struct Definition {
    pub name: Ident,
    pub r#type: Term,
    pub body: Option<Term>,
}

pub struct Inductive {
    pub name: Ident,
    pub params: Vec<(Ident, Term)>,
    pub sort: Term,
    pub constructors: Vec<(Ident, Term)>,
    pub recursor_name: Ident,
}

#[derive(Clone)]
pub struct Term {
    pub span: Span,
    pub kind: TermKind,
}

impl Term {
    /// Call a function on every free variable of this term.
    pub fn with_free(&mut self, mut f: impl FnMut(usize) -> TermKind) {
        let mut to_process = vec![(self, Variable(0))];
        while let Some((term, lowest_free)) = to_process.pop() {
            // This is split into its own `match` to work around Polonius
            match &term.kind {
                // Only modify free variables
                TermKind::Variable(v) if *v >= lowest_free => {
                    term.kind = f(v.0 - lowest_free.0);
                    term.increase_free(lowest_free.0);
                    continue;
                }
                _ => {}
            }

            match &mut term.kind {
                // Do not modify bound variables
                TermKind::Variable(_) => {}
                TermKind::Abstraction { r#type, body, .. } => {
                    to_process.push((r#type, lowest_free));
                    to_process.push((body, Variable(lowest_free.0 + 1)));
                }
                TermKind::Application { left, right } => {
                    to_process.push((left, lowest_free));
                    to_process.push((right, lowest_free));
                }
                // Sorts and errors do not contain variables
                TermKind::Sort { .. } | TermKind::Error => {}
            }
        }
    }

    /// Increase the values of all free variables in the given expression.
    pub fn increase_free(&mut self, by: usize) {
        self.increase_free_from(by, Variable(0));
    }

    /// Increase the values of all free variables in the given expression.
    pub fn increase_free_from(&mut self, by: usize, lowest_free: Variable) {
        let mut to_process = vec![(self, lowest_free)];
        while let Some((term, lowest_free)) = to_process.pop() {
            match &mut term.kind {
                // Do not modify bound variables
                TermKind::Variable(v) if *v < lowest_free => {}
                // Add to free variables
                TermKind::Variable(v) => v.0 += by,
                TermKind::Abstraction { r#type, body, .. } => {
                    to_process.push((r#type, lowest_free));
                    to_process.push((body, Variable(lowest_free.0 + 1)));
                }
                TermKind::Application { left, right } => {
                    to_process.push((left, lowest_free));
                    to_process.push((right, lowest_free));
                }
                // Sorts and errors do not contain variables
                TermKind::Sort { .. } | TermKind::Error => {}
            }
        }
    }

    /// Replace the lowest free variable in the given term with the replacement.
    pub fn replace(&mut self, with: &Term) {
        self.with_free(|v| {
            if v == 0 {
                with.kind.clone()
            } else {
                TermKind::Variable(Variable(v - 1))
            }
        })
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Term {
    pub fn display<'this, 'context>(
        &'this self,
        context: &'context mut Context,
    ) -> TermDisplay<'this, 'context> {
        TermDisplay { term: self, context: Cell::new(Some(context)) }
    }
}

pub struct TermDisplay<'term, 'variables> {
    term: &'term Term,
    context: Cell<Option<&'variables mut Context>>,
}

impl Display for TermDisplay<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let context = self.context.take().expect("`Display` on `TermDisplay` called more than once");

        match &self.term.kind {
            TermKind::Sort { level } => write!(f, "Sort {level:?}"),
            TermKind::Variable(v) => Display::fmt(&context.get(*v).name, f),
            TermKind::Abstraction {
                token,
                variable,
                r#type,
                body,
            } => {
                write!(f, "{token} {variable} ")
                write!(
                    f,
                    "{token} {variable} : {}, {}",
                    r#type.display(self.source),
                    body.display(self.source)
                )
            }
            TermKind::Application { left, right } => {
                let mut left = left;
                let mut chain = vec![right];
                while let TermKind::Application {
                    left: new_left,
                    right,
                } = &left.kind
                {
                    chain.push(right);
                    left = new_left;
                }
                if let TermKind::Variable(_) | TermKind::Error = &left.kind {
                    write!(f, "{}", left.display(self.source))?;
                } else {
                    write!(f, "({})", left.display(self.source))?;
                };
                for item in chain.into_iter().rev() {
                    if let TermKind::Variable(_) | TermKind::Error = &item.kind {
                        write!(f, " {}", item.display(self.source))?;
                    } else {
                        write!(f, " ({})", item.display(self.source))?;
                    }
                }
                Ok(())
            }
            TermKind::Error => f.write_str("[error]"),
        }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Variable(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UniverseVariable {}

pub fn resolve(parser_items: Vec<parser::Item>, reporter: &mut Reporter) -> Vec<Item> {
    let mut variables = Vec::new();
    let mut items = Vec::new();

    for item in parser_items {
        items.push(match item {
            parser::Item::Definition(def) => {
                let Some(r#type) = resolve_term(&mut variables, &def.r#type, reporter)
                    else { continue };

                let body = match def.body {
                    Some(body) => {
                        let Some(body) = resolve_term(&mut variables, &body, reporter)
                            else { continue };
                        Some(body)
                    }
                    None => None,
                };

                variables.push(def.ident.clone());

                Item::Definition(Definition {
                    name: def.ident,
                    r#type,
                    body,
                })
            }
            parser::Item::Inductive(inductive) => {
                let mut params = Vec::new();
                for param_group in inductive.params {
                    for ident in param_group.idents {
                        let Some(r#type) =
                            resolve_term(&mut variables, &param_group.r#type, reporter)
                            else { break };
                        params.push((ident.clone(), r#type));
                        variables.push(ident);
                    }
                }

                let Some(sort) = resolve_term(&mut variables, &inductive.sort, reporter)
                    else { continue };

                // Bring the type name in scope for the constructors
                let ident_index = variables.len();
                variables.push(inductive.ident);

                let mut constructors = Vec::new();
                let mut constructor_idents = Vec::new();
                for constructor in inductive.constructors {
                    let Some(r#type) = resolve_term(&mut variables, &constructor.r#type, reporter)
                        else { continue };

                    let ident = &variables[ident_index];
                    let ident = Ident {
                        span: constructor.ident.span,
                        name: lexer::Ident::new(&format!("{ident}_{}", constructor.ident.name))
                            .unwrap(),
                    };

                    constructors.push((ident.clone(), r#type));
                    constructor_idents.push(ident);
                }

                // Take the type name and parameters out of scope
                let name = variables.pop().unwrap();
                variables.truncate(variables.len() - params.len());

                // Add the type name, constructors and recursor to the global scope
                let recursor_name = Ident {
                    name: lexer::Ident::new(&format!("{name}_rec")).unwrap(),
                    span: name.span,
                };
                variables.push(name.clone());
                variables.extend(constructor_idents);
                variables.push(recursor_name.clone());

                Item::Inductive(Inductive {
                    name,
                    params,
                    sort,
                    constructors,
                    recursor_name,
                })
            }
        });
    }

    items
}

fn resolve_term(
    variables: &mut Vec<Ident>,
    term: &parser::Term,
    reporter: &mut Reporter,
) -> Option<Term> {
    let kind = match &term.kind {
        parser::TermKind::Sort { level } => TermKind::Sort {
            level: resolve_universe_level(level, reporter)?,
        },
        parser::TermKind::Variable(v) => {
            let index = variables.iter().rev().position(|local| local.name == *v);
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
            let r#type = Box::new(resolve_term(variables, r#type, reporter)?);

            variables.push(variable.clone());
            let body = Box::new(resolve_term(variables, body, reporter)?);
            variables.pop();

            TermKind::Abstraction {
                token: *token,
                variable: variable.clone(),
                r#type,
                body,
            }
        }
        parser::TermKind::Application { left, right } => {
            let left = Box::new(resolve_term(variables, left, reporter)?);
            let right = Box::new(resolve_term(variables, right, reporter)?);
            TermKind::Application { left, right }
        }
        parser::TermKind::Error => TermKind::Error,
    };
    let span = term.span;
    Some(Term { kind, span })
}

fn resolve_universe_level(
    level: &parser::UniverseLevel,
    reporter: &mut Reporter,
) -> Option<UniverseLevel> {
    let kind = match &level.kind {
        parser::UniverseLevelKind::Lit(n) => UniverseLevelKind::Lit(*n),
        parser::UniverseLevelKind::Variable(v) => {
            reporter.error(
                level.span,
                format_args!("unknown universe variable {}", v.as_str()),
            );
            return None;
        }
        parser::UniverseLevelKind::Addition { left, right } => UniverseLevelKind::Addition {
            left: Box::new(resolve_universe_level(left, reporter)?),
            right: *right,
        },
        parser::UniverseLevelKind::Max { i, left, right } => UniverseLevelKind::Max {
            i: *i,
            left: Box::new(resolve_universe_level(left, reporter)?),
            right: Box::new(resolve_universe_level(right, reporter)?),
        },
        parser::UniverseLevelKind::Error => UniverseLevelKind::Error,
    };
    let span = level.span;
    Some(UniverseLevel { kind, span })
}

use crate::lexer;
use crate::parser;
use crate::parser::AbstractionToken;
use crate::parser::Ident;
use crate::parser::UniverseLevelLit;
use crate::reporter::Reporter;
use crate::reporter::Span;
use core::fmt;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use crate::kernel::BoundVariable;
use std::cell::Cell;
use crate::kernel::Context;

