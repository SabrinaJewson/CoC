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

pub trait Reporter {
    fn error(&mut self, span: Span, error: impl Display);
}

use std::fmt::Display;
