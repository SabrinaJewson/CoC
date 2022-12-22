pub struct Reporter {
    cache: (String, Source),
    source: String,
}

impl Reporter {
    pub fn new(path: &str, source: &str) -> Self {
        Self {
            cache: (path.to_owned(), ariadne::Source::from(&source)),
            source: source.to_owned(),
        }
    }

    pub fn source(&self) -> &str {
        &self.source
    }

    fn to_char(&self, i: usize) -> usize {
        self.source
            .char_indices()
            .position(|(j, _)| j == i)
            .expect("span out of range")
    }

    pub fn error(&mut self, span: Span, error: impl Display) {
        let range = if !span.is_none() {
            self.to_char(span.start)..self.to_char(span.end)
        } else {
            0..self.source.len()
        };

        let _ = Report::build(ariadne::ReportKind::Error, &self.cache.0, range.start)
            .with_message(&error)
            // TODO: remove clone
            .with_label(Label::new((self.cache.0.clone(), range)).with_message(&error))
            .finish()
            .eprint(&mut self.cache);
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn none() -> Self {
        Self {
            start: usize::MAX,
            end: usize::MAX,
        }
    }

    pub fn is_none(self) -> bool {
        let c = self.start == usize::MAX;
        if c {
            assert_eq!(self.end, usize::MAX);
        }
        c
    }

    pub fn join(self, other: Self) -> Self {
        assert!(!self.is_none());
        assert!(!other.is_none());
        Self {
            start: usize::min(self.start, other.start),
            end: usize::max(self.end, other.end),
        }
    }
}

impl PartialEq for Span {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for Span {}

use ariadne::Label;
use ariadne::Report;
use ariadne::Source;
use std::fmt::Display;
