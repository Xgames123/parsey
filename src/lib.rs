mod parsey;
mod span;
pub use parsey::*;
pub use span::*;

pub trait ParseAnyResult<'c, O, E> {
    fn parse_any_result(self, parser: &mut Parsey<'c>) -> Result<Option<O>, E>;
    fn parse_any_result_sandboxed(self, parser: &mut Parsey<'c>) -> Result<Option<O>, E>;
}
pub trait ParseAny<'c, O> {
    fn parse_any(self, parser: &mut Parsey<'c>) -> Option<O>;
    fn parse_any_sandboxed(self, parser: &mut Parsey<'c>) -> Option<O>;
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

macro_rules! impl_parse_any {
    ($($f:ident),*) => {

        #[allow(unused_parens)]
        impl<
            'c,
            O,
        $(
            $f: FnOnce(&mut Parsey<'c>) -> Option<O>
        ),*
        > ParseAny<'c, O> for ($($f),*)
        {

            /// Try the functions in order and return the result of the first one that returns
            /// Some. (Errors are forwarded)
            /// Parsers are sandboxed and thus only applied when they are Some()
            #[allow(nonstandard_style)]
            fn parse_any_sandboxed(self, parser: &mut Parsey<'c>) -> Option<O> {
            let ($($f),*) = self;

        $(
                if let Some(value) = parser.sandbox($f) {
                    return Some(value);
                }
        )*
                None
            }

            /// Try the functions in order and return the result of the first one that returns
            /// Some. (Errors are forwarded)
            #[allow(nonstandard_style)]
            fn parse_any(self, parser: &mut Parsey<'c>) -> Option<O> {
            let ($($f),*) = self;

        $(
                if let Some(value) = $f(parser) {
                    return Some(value);
                }
        )*
                None
            }
        }

        #[allow(unused_parens)]
        impl<
            'c,
            O,
            E,
        $(
            $f: FnOnce(&mut Parsey<'c>) -> Result<Option<O>, E>
        ),*
        > ParseAnyResult<'c, O, E> for ($($f),*)
        {

            /// Try the functions in order and return the result of the first one that returns
            /// Some. (Errors are forwarded)
            /// Parsers are sandboxed and thus only applied when they are Ok(Some())
            #[allow(nonstandard_style)]
            fn parse_any_result_sandboxed(self, parser: &mut Parsey<'c>) -> Result<Option<O>, E> {
            let ($($f),*) = self;

        $(
                if let Some(value) = parser.sandbox_result($f)? {
                    return Ok(Some(value));
                }
        )*
                Ok(None)
            }

            /// Try the functions in order and return the result of the first one that returns
            /// Some. (Errors are forwarded)
            #[allow(nonstandard_style)]
            fn parse_any_result(self, parser: &mut Parsey<'c>) -> Result<Option<O>, E> {
            let ($($f),*) = self;

        $(
                if let Some(value) = parser.sandbox_result($f)? {
                    return Ok(Some(value));
                }
        )*
                Ok(None)
            }
        }
    };
}

impl_parse_any!(F);
impl_parse_any!(F0, F1);
impl_parse_any!(F0, F1, F2);
impl_parse_any!(F0, F1, F2, F3);
