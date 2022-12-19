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

    pub fn join(self, other: Self) -> Self {
        Self {
            start: usize::min(self.start, other.start),
            end: usize::min(self.end, other.end),
        }
    }
}

pub trait Reporter {
    fn error(&mut self, error: impl Display);
}

use std::fmt::Display;
