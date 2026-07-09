mod parsey;
mod span;
mod spanned;

pub use parsey::*;
pub use span::*;
pub use spanned::*;

pub type ParseResult<T, E> = Result<Option<T>, E>;

pub trait Parse<E>: Sized {
    fn parse(parser: &mut Parsey) -> ParseResult<Self, E>;
}

/// A trait that represent a type that can be used to search a string for a match.
/// This trait is implemented for types like:
/// - char
/// - str
/// - FnMut(char) -> bool,
pub trait Searcher {
    /// The length of which should be skipped when consuming this searcher.
    /// The length will be ceiled to to first char boundery
    fn len(&self) -> usize {
        1
    }

    // Does the searcher match at the start of the string
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

/// Tries parsers in order until one returns Ok(Some) or Err.
///
///```rust
/// use parsey::Parsey;
///
/// #[derive(Debug, PartialEq)]
/// enum Token {Number, String}
/// fn parse_number<'c>(parser: &mut Parsey<'c>) -> Result<Option<Token>, ()> {
///     let num = parser.take_until_or_end(|c: char|!c.is_digit(10));
///         dbg!(num.str());
///     if num.str().len() > 0 {
///         Ok(Some(Token::Number))
///     } else {
///         Ok(None)
///     }
/// }
///
///fn parse_string<'c>(parser: &mut Parsey<'c>) -> Result<Option<Token>, ()> {
///     let stri = parser.take_until_or_end(|c: char|!c.is_alphabetic());
///         dbg!(stri.str());
///     if stri.str().len() > 0 {
///         Ok(Some(Token::String))
///     } else {
///         Ok(None)
///     }
///}
///
///let mut parser = Parsey::new("123,abc");
///let result: Result<Option<Token>, ()> = parsey::parse_any!(&mut parser, parse_number, parse_string);
///assert_eq!(result.unwrap().unwrap(), Token::Number);
///```
#[macro_export]
macro_rules! parse_any {
    ($parsey:expr$(=>$type:ty)?, $($parser:expr),*) => {
        {
            let result$(: $type)? = if false {
                unreachable!();
            }
            $( else if let result = $parser($parsey) && let Ok(Some(_)) | Err(_) = result {
                result.map_err(|e|e.into()).map(|v|v.map(|v|v.into()))
            } )*
            else {
                Ok(None)
            };
            result
        }

    };
}
