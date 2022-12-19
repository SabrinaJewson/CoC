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
            r#type: param_type,
            body,
        } => {
            let (param_type_type, param_type) = type_of(variables, *param_type, reporter);

            if !matches!(param_type_type, Term::Sort { .. }) {
                reporter.report("λ parameter is not a type");
            }

            variables.push((param_type, None));
            let (body_type, body) = type_of(variables, *body, reporter);
            let param_type = Box::new(variables.pop().unwrap().0);

            r#type = Term::Pi {
                r#type: param_type.clone(),
                // TODO: Are the de bruijn indices correct here?
                body: Box::new(body_type),
            };

            reduced = Term::Abstraction {
                r#type: param_type,
                body: Box::new(body),
            };
        }
        Term::Pi {
            r#type: param_type,
            body,
        } => {
            let (input_type_type, input_type) = type_of(variables, *param_type, reporter);

            let Term::Sort { level: input_level } = input_type_type else {
                reporter.report("Π parameter is not a type");
                todo!()
            };

            variables.push((input_type, None));
            let (body_type, body) = type_of(variables, *body, reporter);
            let input_type = Box::new(variables.pop().unwrap().0);

            let Term::Sort { level: body_level } = body_type else {
                reporter.report("Π body is not a type");
                todo!()
            };

            let level = UniverseLevel::Max {
                i: true,
                left: Box::new(input_level),
                right: Box::new(body_level),
            };

            r#type = Term::Sort {
                level: reduce_universe_level(&level, reporter),
            };

            reduced = Term::Pi {
                r#type: input_type,
                body: Box::new(body),
            };
        }
        Term::Application { left, right } => {
            let (left_type, left) = type_of(variables, *left, reporter);
            let (right_type, right) = type_of(variables, *right, reporter);

            let Term::Pi { r#type: param_type, body: ret_type } = &left_type else {
                reporter.report("left hand side of application is not a function");
                todo!()
            };

            if **param_type != right_type {
                reporter.report(format_args!(
                    "function application type mismatch on {:?} of {:?}\n expected: {:?}\n      got: {:?}",
                    left, right,
                    param_type, right_type
                ));
                todo!()
            }

            let unreduced_type = variables::replace(ret_type, &right);
            (_, r#type) = type_of(variables, unreduced_type, reporter);

            // TODO: recursive replacing; is this right?
            reduced = if let Term::Abstraction { r#type, body } = left {
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
                let Some(sum) = left.checked_add(*right) else {
                        reporter.report("universe too large");
                        todo!();
                    };
                UniverseLevel::Number(sum)
            }
            UniverseLevel::Variable(v) => match v {},
            UniverseLevel::Addition {
                left,
                right: right_2,
            } => {
                let Some(right) = right.checked_add(right_2) else {
                        reporter.report("universe too large");
                        todo!();
                    };
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
use reporter::Reporter;
use std::fmt::Display;
use std::fs;
use std::path::PathBuf;
use variables::Term;
use variables::UniverseLevel;
