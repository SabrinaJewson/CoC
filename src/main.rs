fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let file = fs::read_to_string(&args.input)
        .with_context(|| format!("failed to read `{}`", args.input.display()))?;

    let mut reporter = CliReporter;

    let tokens = lexer::lex(&file, &mut reporter);
    let source = parser::parse(tokens, &mut reporter);
    let definitions = variables::resolve(source.items, &mut reporter);

    let mut variables = Vec::new();
    for definition in definitions {
        let (type_type, r#type) = type_of(&mut variables, definition.r#type, &mut reporter);
        let Term::Sort { .. } = type_type else {
            reporter.report("definition type is not a type");
            continue;
        };

        let body = definition.body.map(|body| {
            let (got_type, body) = type_of(&mut variables, body, &mut reporter);
            if got_type != r#type {
                reporter.report(format_args!(
                    "type mismatch of definition:\n expected: {:?}\n      got: {:?}",
                    r#type, got_type,
                ));
            }
            body
        });
        variables.push((r#type, body));
    }

    Ok(())
}

fn type_of(
    variables: &mut Vec<(Term, Option<Term>)>,
    term: Term,
    reporter: &mut impl Reporter,
) -> (Term, Term) {
    let r#type: Term;
    let reduced: Term;

    match term {
        Term::Sort { level } => {
            let level = reduce_universe_level(&level, reporter);
            let raised_level = UniverseLevel::Addition {
                left: Box::new(level.clone()),
                right: 1,
            };
            r#type = Term::Sort {
                level: reduce_universe_level(&raised_level, reporter),
            };
            reduced = Term::Sort { level };
        }
        Term::Variable(v) => {
            let pull_by = v.0 + 1;
            let (original_type, value) = &variables[variables.len() - pull_by];
            r#type = variables::increase_free(original_type, pull_by);
            // TODO: Is this enough to δ-reduce?
            reduced = if let Some(value) = value {
                variables::increase_free(value, pull_by)
            } else {
                Term::Variable(v)
            };
        }
        Term::Abstraction {
            kind,
            r#type: param_type,
            body,
        } => {
            let (mut param_type_type, mut param_type) = type_of(variables, *param_type, reporter);

            let param_level = match param_type_type {
                Term::Sort { level } => level,
                r#type => {
                    reporter.report(format_args!("{kind:?} parameter is not a type"));

                    // Guess that the user meant to write the _type_ of the term they wrote
                    // e.g. convert (λ x : 5, x) to (λ x : nat, x)
                    (param_type_type, param_type) = type_of(variables, r#type, reporter);
                    let Term::Sort { level } = param_type_type else { unreachable!() };
                    level
                }
            };

            variables.push((param_type, None));
            let (mut body_type, mut body) = type_of(variables, *body, reporter);
            let param_type = Box::new(variables.pop().unwrap().0);

            match kind {
                // The type of the Π type is Sort imax u v
                AbstractionKind::Pi => {
                    let body_level = match body_type {
                        Term::Sort { level } => level,
                        r#type => {
                            reporter.report("Π body is not a type");

                            // Again, guess that the user meant to write the _type_ of the term they
                            // wrote.
                            // e.g. convert (Π x : nat, 6) to (Π x : nat, nat)
                            (body_type, body) = type_of(variables, r#type, reporter);
                            let Term::Sort { level } = body_type else { unreachable!() };
                            level
                        }
                    };

                    let level = UniverseLevel::Max {
                        i: true,
                        left: Box::new(param_level),
                        right: Box::new(body_level),
                    };

                    r#type = Term::Sort {
                        level: reduce_universe_level(&level, reporter),
                    };
                }
                // The type of the λ type is the Π type
                AbstractionKind::Lambda => {
                    r#type = Term::Abstraction {
                        kind: AbstractionKind::Pi,
                        r#type: param_type.clone(),
                        // TODO: Are the de bruijn indices correct here?
                        body: Box::new(body_type),
                    };
                }
            }

            reduced = Term::Abstraction {
                kind,
                r#type: param_type,
                body: Box::new(body),
            };
        }
        Term::Application { left, right } => {
            let (left_type, left) = type_of(variables, *left, reporter);
            let (right_type, right) = type_of(variables, *right, reporter);

            let Term::Abstraction { kind: AbstractionKind::Pi, r#type: param_type, body: ret_type } = &left_type else {
                reporter.report("left hand side of application is not a function");
                // Recover by ignoring the application
                return (left_type, left);
            };

            if **param_type != right_type {
                reporter.report(format_args!(
                    "function application type mismatch on {:?} of {:?}\n expected: {:?}\n      got: {:?}",
                    left, right,
                    param_type, right_type
                ));
            }

            let unreduced_type = variables::replace(ret_type, &right);
            (_, r#type) = type_of(variables, unreduced_type, reporter);

            // TODO: recursive replacing; is this right?
            reduced = if let Term::Abstraction {
                kind: AbstractionKind::Lambda,
                r#type,
                body,
            } = left
            {
                assert_eq!(*r#type, **param_type);
                let unreduced = variables::replace(&body, &right);
                type_of(variables, unreduced, reporter).1
            } else {
                let left = Box::new(left);
                let right = Box::new(right);
                Term::Application { left, right }
            };
        }
    }

    (r#type, reduced)
}

fn reduce_universe_level(level: &UniverseLevel, reporter: &mut impl Reporter) -> UniverseLevel {
    match level {
        UniverseLevel::Number(n) => UniverseLevel::Number(*n),
        UniverseLevel::Variable(v) => match *v {},
        UniverseLevel::Addition { left, right } => match reduce_universe_level(left, reporter) {
            UniverseLevel::Number(left) => {
                let sum = left.checked_add(*right).unwrap_or_else(|| {
                    reporter.report("universe too large");
                    u32::MAX
                });
                UniverseLevel::Number(sum)
            }
            UniverseLevel::Variable(v) => match v {},
            UniverseLevel::Addition {
                left,
                right: right_2,
            } => {
                let right = right.checked_add(right_2).unwrap_or_else(|| {
                    reporter.report("universe too large");
                    u32::MAX
                });
                UniverseLevel::Addition { left, right }
            }
            UniverseLevel::Max { .. } => todo!(),
        },
        UniverseLevel::Max { i, left, right } => {
            match (
                reduce_universe_level(left, reporter),
                reduce_universe_level(right, reporter),
            ) {
                (UniverseLevel::Number(_), UniverseLevel::Number(0)) if *i => {
                    UniverseLevel::Number(0)
                }
                (UniverseLevel::Number(left), UniverseLevel::Number(right)) => {
                    UniverseLevel::Number(u32::max(left, right))
                }
                _ => todo!(),
            }
        }
    }
}

struct CliReporter;
impl Reporter for CliReporter {
    fn report(&mut self, error: impl Display) {
        eprintln!("error: {error}");
    }
}

#[derive(clap::Parser)]
struct Args {
    input: PathBuf,
}

mod lexer;
mod parser;
mod reporter;
mod variables;

use anyhow::Context as _;
use clap::Parser as _;
use parser::AbstractionKind;
use reporter::Reporter;
use std::fmt::Display;
use std::fs;
use std::path::PathBuf;
use variables::Term;
use variables::UniverseLevel;
