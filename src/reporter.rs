#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

pub trait Reporter {
    fn report(&mut self, error: impl Display);
}

use std::fmt::Display;
