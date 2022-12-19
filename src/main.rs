fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("failed to read `{}`", args.input))?;

    let mut reporter = CliReporter::new(&args.input, &source);

    let tokens = lexer::lex(&source, &mut reporter);
    let source = parser::parse(tokens, &mut reporter);
    let definitions = variables::resolve(source.items, &mut reporter);
    kernel::typecheck(definitions, &mut reporter);

    Ok(())
}

use cli_reporter::CliReporter;
mod cli_reporter {
    pub struct CliReporter<'source> {
        cache: (&'source str, Source),
        source: &'source str,
    }
    impl<'source> CliReporter<'source> {
        pub fn new(path: &'source str, source: &'source str) -> Self {
            Self {
                cache: (path, ariadne::Source::from(&source)),
                source,
            }
        }
    }
    impl Reporter for CliReporter<'_> {
        fn error(&mut self, span: Span, error: impl Display) {
            let start = self
                .source
                .char_indices()
                .position(|(i, _)| i == span.start)
                .unwrap();
            let end = self
                .source
                .char_indices()
                .position(|(i, _)| i == span.end)
                .unwrap();

            let _ = Report::build(ariadne::ReportKind::Error, self.cache.0, 0)
                .with_message(&error)
                .with_label(Label::new((self.cache.0, start..end)).with_message(&error))
                .finish()
                .eprint(&mut self.cache);
        }
    }

    use crate::reporter::Reporter;
    use crate::reporter::Span;
    use ariadne::Label;
    use ariadne::Report;
    use ariadne::Source;
    use std::fmt::Display;
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
use std::fs;
