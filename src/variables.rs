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

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Term {
    pub fn display<'this, 'context>(
        &'this self,
        context: &'context Context,
    ) -> TermDisplay<'this, 'context> {
        TermDisplay {
            term: self,
            context,
        }
    }
}

pub struct TermDisplay<'term, 'context> {
    term: &'term Term,
    context: &'context Context,
}

impl Display for TermDisplay<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        display_term(self.context, &mut Vec::new(), false, self.term, f)
    }
}

fn display_term<'term>(
    context: &Context,
    variables: &mut Vec<&'term Ident>,
    brackets: bool,
    term: &'term Term,
    f: &mut Formatter<'_>,
) -> fmt::Result {
    let needs_brackets = brackets && !matches!(term.kind, TermKind::Variable(_) | TermKind::Error);

    if needs_brackets {
        f.write_str("(")?;
    }

    match &term.kind {
        TermKind::Sort { level } => write!(f, "Sort {level:?}")?,
        // TODO: We don’t currently implement α-conversion to remove collisions, meaning error
        // messages can sometimes not make sense in rare cases
        TermKind::Variable(v) => {
            if let Some(v) = v.0.checked_sub(variables.len()) {
                Display::fmt(&context.get(Variable(v)).name, f)?;
            } else {
                Display::fmt(&variables[variables.len() - 1 - v.0], f)?;
            }
        }
        TermKind::Abstraction {
            token,
            variable,
            r#type,
            body,
        } => {
            write!(f, "{token} {variable} : ")?;
            display_term(context, variables, false, r#type, f)?;
            f.write_str(", ")?;
            variables.push(variable);
            display_term(context, variables, false, body, f)?;
            variables.pop().unwrap();
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
            display_term(context, variables, true, left, f)?;
            for item in chain.into_iter().rev() {
                f.write_str(" ")?;
                display_term(context, variables, true, item, f)?;
            }
        }
        TermKind::Error => f.write_str("[error]")?,
    }

    if needs_brackets {
        f.write_str(")")?;
    }

    Ok(())
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

impl TermKind {
    /// Replace the lowest free variable in the given term with the replacement.
    pub fn replace(&mut self, with: &Term) {
        self.substitute_free(|v| {
            if v == 0 {
                with.kind.clone()
            } else {
                TermKind::Variable(Variable(v - 1))
            }
        })
    }

    /// Increase the values of free variables above a given threshold in the given expression.
    pub fn increase_free(&mut self, by: usize) {
        self.substitute_free_with_depth(|v, depth| TermKind::Variable(Variable(v + by + depth)))
    }

    /// Substitute every free variable of this term.
    pub fn substitute_free(&mut self, mut f: impl FnMut(usize) -> TermKind) {
        self.substitute_free_with_depth(|v, depth| {
            let mut term = f(v);
            term.increase_free(depth);
            term
        });
    }

    /// Substitute every free variable of this term. The second parameter to the closure is the
    /// depth at which the substitution is occuring.
    pub fn substitute_free_with_depth(&mut self, mut f: impl FnMut(usize, usize) -> TermKind) {
        let mut to_process = vec![(self, Variable(0))];
        while let Some((term, lowest_free)) = to_process.pop() {
            // This is split into its own `match` to work around Polonius
            match term {
                // Only modify free variables
                TermKind::Variable(v) if *v >= lowest_free => {
                    *term = f(v.0 - lowest_free.0, lowest_free.0);
                    continue;
                }
                _ => {}
            }

            match term {
                // Do not modify bound variables
                TermKind::Variable(_) => {}
                TermKind::Abstraction { r#type, body, .. } => {
                    to_process.push((&mut r#type.kind, lowest_free));
                    to_process.push((&mut body.kind, Variable(lowest_free.0 + 1)));
                }
                TermKind::Application { left, right } => {
                    to_process.push((&mut left.kind, lowest_free));
                    to_process.push((&mut right.kind, lowest_free));
                }
                // Sorts and errors do not contain variables
                TermKind::Sort { .. } | TermKind::Error => {}
            }
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

use crate::kernel::Context;
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
