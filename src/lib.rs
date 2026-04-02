mod parsey;
mod span;
pub use parsey::*;
pub use span::*;

pub type ParseResult<T, E> = Result<Option<T>, E>;

pub trait Parse<E>: Sized {
    fn parse(parser: &mut Parsey) -> ParseResult<Self, E>;
}

pub trait Searcher {
    /// The length of which should be skipped when consuming this searcher.
    /// The length will be ceiled to to first char boundery
    fn len(&self) -> usize {
        1
    }

    // Does the searcher match at the start of the string
    fn matches_start(&self, str: &str) -> bool;
}

impl<F: Fn(char) -> bool> Searcher for F {
    fn matches_start(&self, str: &str) -> bool {
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
    fn matches_start(&self, str: &str) -> bool {
        str.starts_with(self)
    }
}
impl Searcher for char {
    fn matches_start(&self, str: &str) -> bool {
        str.chars().next() == Some(*self)
    }
}

#[macro_export]
macro_rules! parse_any {
    ($parsey:expr$(=>$type:ty)?, $($parser:expr),*) => {
        {
            let result$(: $type)? = if false {
                unreachable!();
            }
            $( else if let result = $parser($parsey) && result != Ok(None) {
                result.map_err(|e|e.into()).map(|v|v.map(|v|v.into()))
            } )*
            else {
                Ok(None)
            };
            result
        }

    };
}
