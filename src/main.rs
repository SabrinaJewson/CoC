fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("failed to read `{}`", args.input))?;

    let mut reporter = Reporter::new(&args.input, &source);

    let tokens = lexer::lex(&source, &mut reporter);
    let source = parser::parse(tokens, &mut reporter);
    let definitions = variables::resolve(source.items, &mut reporter);
    kernel::typecheck(definitions, &mut reporter);

    Ok(())
}

#[derive(clap::Parser)]
struct Args {
    input: String,
}

mod kernel;
mod lexer;
mod parser;
mod reporter;
mod variables;

use anyhow::Context as _;
use clap::Parser as _;
use reporter::Reporter;
use std::fs;
