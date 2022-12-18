
pub trait Reporter {
    fn report(&mut self, error: impl Display);
}

use std::fmt::Display;
