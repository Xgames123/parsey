/// A trait that represent a type that can be used to search a string for a match.
/// This trait is implemented for types like:
/// - char
/// - str
/// - FnMut(char) -> bool,
pub trait Searcher {
    /// The length which should be skipped when consuming this searcher.
    /// The length will be ceiled to to first char boundery
    fn len(&self) -> usize {
        1
    }

    /// Returns true if this searcher matches at the start of the string.
    /// The amount of which is considered should in most cases be the same as the len returned by
    /// the Searcher::len function
    fn matches_start(&mut self, str: &str) -> bool;
}

impl<F: FnMut(char) -> bool> Searcher for F {
    fn matches_start(&mut self, str: &str) -> bool {
        let Some(char) = str.chars().next() else {
            return false;
        };
        self(char)
    }
}

impl<'a> Searcher for &'a str {
    fn len(&self) -> usize {
        str::len(&self)
    }
    fn matches_start(&mut self, str: &str) -> bool {
        str.starts_with(*self)
    }
}
impl Searcher for char {
    fn matches_start(&mut self, str: &str) -> bool {
        str.chars().next() == Some(*self)
    }
}
