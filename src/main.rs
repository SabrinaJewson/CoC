fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let file = fs::read_to_string(&args.input)
        .with_context(|| format!("failed to read `{}`", args.input.display()))?;

    let mut reporter = CliReporter;

    let tokens = lexer::lex(&file, &mut reporter);
    let source = parser::parse(tokens, &mut reporter);
    let definitions = variables::resolve(source.items, &mut reporter);
    kernel::typecheck(definitions, &mut reporter);

    Ok(())
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

mod kernel;
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
