pub fn typecheck(items: Vec<Item>, reporter: &mut impl Reporter) {
    let mut variables = Vec::new();

    for item in items {
        match item {
            Item::Definition(item) => {
                let (type_type, r#type) = type_of(&mut variables, item.r#type, reporter);
                let TermKind::Sort { .. } = type_type.kind else {
                    reporter.error(r#type.span, "definition type is not a type");
                    continue;
                };

                let body = item.body.map(|body| {
                    let (got_type, body) = type_of(&mut variables, body, reporter);
                    if got_type != r#type {
                        reporter.error(
                            body.span,
                            format_args!(
                                "type mismatch of definition:\n expected: {:?}\n      got: {:?}",
                                r#type, got_type,
                            ),
                        );
                    }
                    body
                });
                variables.push((r#type, body));
            }
            Item::Inductive(_item) => todo!(),
        }
    }
}

fn type_of(
    variables: &mut Vec<(Term, Option<Term>)>,
    mut term: Term,
    reporter: &mut impl Reporter,
) -> (Term, Term) {
    let r#type: Term;

    match term.kind {
        TermKind::Sort { level } => {
            let level = reduce_universe_level(&level, reporter);

            let raised_level = UniverseLevel {
                kind: UniverseLevelKind::Addition {
                    left: Box::new(level.clone()),
                    right: Some(UniverseLevelLit {
                        value: 1,
                        span: level.span,
                    }),
                },
                span: level.span,
            };
            r#type = Term {
                kind: TermKind::Sort {
                    level: reduce_universe_level(&raised_level, reporter),
                },
                span: Span::none(),
            };

            term.kind = TermKind::Sort { level };
        }
        TermKind::Variable(v) => {
            let pull_by = v.0 + 1;
            let (original_type, value) = &variables[variables.len() - pull_by];
            let type_term = variables::increase_free(original_type, pull_by);
            r#type = Term {
                kind: type_term.kind,
                span: type_term.span,
            };
            // TODO: Is this enough to δ-reduce?
            if let Some(value) = value {
                term = variables::increase_free(value, pull_by);
            }
        }
        TermKind::Abstraction {
            token,
            r#type: param_type,
            body,
        } => {
            let (mut param_type_type, mut param_type) = type_of(variables, *param_type, reporter);

            let param_level = match param_type_type.kind {
                TermKind::Sort { level } => level,
                kind => {
                    reporter.error(
                        param_type.span,
                        format_args!("{token:?} parameter is not a type"),
                    );

                    // Guess that the user meant to write the _type_ of the term they wrote
                    // e.g. convert (λ x : 5, x) to (λ x : nat, x)
                    let assumed_type = Term {
                        kind,
                        span: param_type.span,
                    };
                    (param_type_type, param_type) = type_of(variables, assumed_type, reporter);
                    let TermKind::Sort { level } = param_type_type.kind else { unreachable!() };
                    level
                }
            };

            variables.push((param_type, None));
            let (mut body_type, mut body) = type_of(variables, *body, reporter);
            let param_type = Box::new(variables.pop().unwrap().0);

            match token {
                // The type of the Π type is Sort imax u v
                AbstractionToken::Pi => {
                    let body_level = match body_type.kind {
                        TermKind::Sort { level } => level,
                        kind => {
                            reporter.error(body.span, "Π body is not a type");

                            // Guess that the user meant to write the _type_ of the term they wrote.
                            // e.g. convert (Π x : nat, 6) to (Π x : nat, nat)
                            let assumed_type = Term {
                                kind,
                                span: body.span,
                            };
                            (body_type, body) = type_of(variables, assumed_type, reporter);
                            let TermKind::Sort { level } = body_type.kind else { unreachable!() };
                            level
                        }
                    };

                    let level = UniverseLevel {
                        kind: UniverseLevelKind::Max {
                            i: true,
                            left: Box::new(param_level),
                            right: Box::new(body_level),
                        },
                        span: Span::none(),
                    };

                    r#type = Term {
                        kind: TermKind::Sort {
                            level: reduce_universe_level(&level, reporter),
                        },
                        span: Span::none(),
                    };
                }
                // The type of the λ type is the Π type
                AbstractionToken::Lambda => {
                    r#type = Term {
                        kind: TermKind::Abstraction {
                            token: AbstractionToken::Pi,
                            r#type: param_type.clone(),
                            // TODO: Are the de bruijn indices correct here?
                            body: Box::new(body_type),
                        },
                        span: Span::none(),
                    };
                }
            }

            term.kind = TermKind::Abstraction {
                token,
                r#type: param_type,
                body: Box::new(body),
            };
        }
        TermKind::Application { left, right } => {
            let (left_type, left) = type_of(variables, *left, reporter);
            let (right_type, right) = type_of(variables, *right, reporter);

            let TermKind::Abstraction { token: AbstractionToken::Pi, r#type: param_type, body: ret_type } = left_type.kind else {
                reporter.error(left.span, "left hand side of application is not a function");
                // Recover by ignoring the application
                return (left_type, left);
            };

            if *param_type != right_type {
                reporter.error(right.span, format_args!(
                    "function application type mismatch on {:?} of {:?}\n expected: {:?}\n      got: {:?}",
                    left, right,
                    param_type, right_type
                ));
            }

            let unreduced_type = variables::replace(*ret_type, &right);
            (_, r#type) = type_of(variables, unreduced_type, reporter);

            // TODO: recursive replacing; is this right?
            if let TermKind::Abstraction {
                token: AbstractionToken::Lambda,
                r#type,
                body,
            } = left.kind
            {
                assert_eq!(*r#type, *param_type);
                let unreduced = variables::replace(*body, &right);
                (_, term) = type_of(variables, unreduced, reporter);
            } else {
                let left = Box::new(left);
                let right = Box::new(right);
                term.kind = TermKind::Application { left, right };
            };
        }
        TermKind::Error => {
            r#type = Term {
                kind: TermKind::Error,
                span: Span::none(),
            }
        }
    }

    (r#type, term)
}

fn reduce_universe_level(level: &UniverseLevel, reporter: &mut impl Reporter) -> UniverseLevel {
    let kind = match &level.kind {
        UniverseLevelKind::Lit(n) => UniverseLevelKind::Lit(*n),
        UniverseLevelKind::Variable(v) => match *v {},
        UniverseLevelKind::Addition {
            left,
            right: Some(right),
        } => {
            match reduce_universe_level(left, reporter).kind {
                UniverseLevelKind::Lit(left) => {
                    let lit = add_universe_level_lit(left, *right, reporter);
                    UniverseLevelKind::Lit(lit)
                }
                UniverseLevelKind::Variable(v) => match v {},
                UniverseLevelKind::Addition {
                    left,
                    right: Some(right_2),
                } => {
                    let right = Some(add_universe_level_lit(*right, right_2, reporter));
                    UniverseLevelKind::Addition { left, right }
                }
                UniverseLevelKind::Max { .. } => todo!(),
                // Propagate the errors
                UniverseLevelKind::Error
                | UniverseLevelKind::Addition {
                    left: _,
                    right: None,
                } => UniverseLevelKind::Error,
            }
        }
        // Propagate the errors
        UniverseLevelKind::Addition {
            left: _,
            right: None,
        } => UniverseLevelKind::Error,
        UniverseLevelKind::Max { i, left, right } => {
            let left = reduce_universe_level(left, reporter);
            let right = reduce_universe_level(right, reporter);
            match (left.kind, right.kind) {
                (
                    UniverseLevelKind::Lit(_),
                    lit @ UniverseLevelKind::Lit(UniverseLevelLit { value: 0, .. }),
                ) if *i => lit,
                (UniverseLevelKind::Lit(left), UniverseLevelKind::Lit(right)) => {
                    UniverseLevelKind::Lit(UniverseLevelLit {
                        value: u32::max(left.value, right.value),
                        span: left.span.join(right.span),
                    })
                }
                _ => todo!(),
            }
        }
        UniverseLevelKind::Error => UniverseLevelKind::Error,
    };
    let span = level.span;
    UniverseLevel { kind, span }
}

fn add_universe_level_lit(
    left: UniverseLevelLit,
    right: UniverseLevelLit,
    reporter: &mut impl Reporter,
) -> UniverseLevelLit {
    let span = left.span.join(right.span);
    let value = left.value.checked_add(right.value).unwrap_or_else(|| {
        reporter.error(span, "universe too large");
        u32::MAX
    });
    UniverseLevelLit { value, span }
}

use crate::parser::AbstractionToken;
use crate::parser::UniverseLevelLit;
use crate::reporter::Reporter;
use crate::reporter::Span;
use crate::variables;
use crate::variables::Item;
use crate::variables::Term;
use crate::variables::TermKind;
use crate::variables::UniverseLevel;
use crate::variables::UniverseLevelKind;
