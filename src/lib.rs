use std::{convert::Infallible, ops::Range};

use miette::SourceSpan;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Span(Range<usize>);
impl Span {
    pub fn from_str(str: &str) -> Self {
        Self(0..str.len())
    }

    pub fn split(&mut self, index: usize) -> (Self, Self) {
        let index = self.0.start + index;
        ((self.0.start..index).into(), (index..self.0.end).into())
    }
}

impl From<Range<usize>> for Span {
    fn from(value: Range<usize>) -> Self {
        Self(value)
    }
}

impl Into<SourceSpan> for Span {
    fn into(self) -> SourceSpan {
        (self.0.start, self.0.end - self.0.start).into()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parsey<'a> {
    code: &'a str,
    span: Span,
}
impl<'a> Parsey<'a> {
    pub fn new(code: &'a str) -> Self {
        Self {
            code,
            span: Span::from_str(code),
        }
    }

    pub fn str(&self) -> &'a str {
        &self.code[self.span.0.start..self.span.0.end]
    }
    pub fn span(&self) -> Span {
        self.span.clone()
    }

    pub fn take(&mut self, size: usize) -> Self {
        let (left, right) = self.span.split(size);
        self.span = right;
        Self {
            code: self.code,
            span: left,
        }
    }
    pub fn peek_char(&mut self) -> Option<char> {
        self.str().chars().next()
    }

    pub fn tag(&mut self, tag: &str) -> Option<Self> {
        if self.str().starts_with(tag) {
            Some(self.take(tag.len()))
        } else {
            None
        }
    }

    pub fn take_until(&mut self, f: impl Fn(char) -> bool) -> Option<(char, Self)> {
        for (i, char) in self.str().char_indices() {
            if f(char) {
                return Some((char, self.take(i)));
            }
        }
        None
    }

    pub fn take_until_inclusive(&mut self, f: impl Fn(char) -> bool) -> Option<(char, Self)> {
        for (i, char) in self.str().char_indices() {
            if f(char) {
                return Some((char, self.take(i + 1)));
            }
        }
        None
    }

    pub fn take_until_or_end(&mut self, f: impl Fn(char) -> bool) -> (char, Self) {
        self.take_until(f)
            .unwrap_or_else(|| ('\0', self.take(self.str().len())))
    }

    pub fn take_until_or_end_inclusive(&mut self, f: impl Fn(char) -> bool) -> (char, Self) {
        self.take_until_inclusive(f)
            .unwrap_or_else(|| ('\0', self.take(self.str().len())))
    }

    pub fn take_until_tag_inclusive(&mut self, tag: &str) -> Option<Self> {
        for i in 0..self.str().len() {
            if (self.str()[i..]).starts_with(tag) {
                return Some(self.take(i + tag.len()));
            }
        }
        None
    }

    pub fn duplicate(&self) -> Self {
        self.clone()
    }

    ///Tries a function. If it returns Some apply the result to self else throw away all work the
    ///function has done. (Forwards inner error)
    pub fn sandbox_result<O, E>(
        &mut self,
        f: impl FnOnce(&mut Parsey<'a>) -> Result<Option<O>, E>,
    ) -> Result<Option<O>, E> {
        let mut duplicated = self.duplicate();
        let result = f(&mut duplicated)?;
        if let Some(r) = result {
            *self = duplicated;
            Ok(Some(r))
        } else {
            Ok(None)
        }
    }
    ///Tries a function. If it returns Some apply the result to self else throw away all work the
    ///function has done.
    pub fn sandbox<O>(&mut self, f: impl FnOnce(&mut Parsey<'a>) -> Option<O>) -> Option<O> {
        self.sandbox_result::<O, Infallible>(|p| Ok(f(p))).unwrap()
    }

    pub fn end(&self) -> bool {
        self.str().len() == 0
    }
}

pub trait ParseAnyResult<'c, O, E> {
    fn parse_any_result(self, parser: &mut Parsey<'c>) -> Result<Option<O>, E>;
}
pub trait ParseAny<'c, O> {
    fn parse_any(self, parser: &mut Parsey<'c>) -> Option<O>;
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
            #[allow(nonstandard_style)]
            fn parse_any(self, parser: &mut Parsey<'c>) -> Option<O> {
            let ($($f),*) = self;

        $(
                if let Some(value) = parser.sandbox($f) {
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

#[cfg(test)]
mod test {
    use crate::Parsey;

    #[test]
    fn split() {
        let mut ci = Parsey::new("abcd");
        assert_eq!(
            ci.take(1),
            Parsey {
                code: "abcd",
                span: (0..1).into()
            }
        );
        assert_eq!(
            ci,
            Parsey {
                code: "abcd",
                span: (1..4).into()
            }
        );

        assert_eq!(
            ci.take(1),
            Parsey {
                code: "abcd",
                span: (1..2).into()
            }
        );
        assert_eq!(
            ci,
            Parsey {
                code: "abcd",
                span: (2..4).into()
            }
        );
    }

    #[test]
    fn take_until() {
        let mut ci = Parsey::new("abcd");
        assert_eq!(
            ci.take_until(|c| c == 'c'),
            Some((
                'c',
                Parsey {
                    code: "abcd",
                    span: (0..2).into()
                }
            ))
        );

        assert_eq!(ci.str(), "cd");

        assert_eq!(
            ci,
            Parsey {
                code: "abcd",
                span: (2..4).into(),
            }
        );
    }

    #[test]
    fn take_until_newline() {
        let mut ci = Parsey::new("abcd\n");
        assert_eq!(
            ci.take_until_or_end(|c| c == '\n'),
            (
                '\n',
                Parsey {
                    code: "abcd\n",
                    span: (0..4).into()
                }
            )
        );

        assert_eq!(
            ci,
            Parsey {
                code: "abcd\n",
                span: (4..5).into(),
            }
        );

        assert_eq!(ci.str(), "\n");
    }

    #[test]
    fn skip_whitespace() {
        let mut ci = Parsey::new(" \nabcd");
        ci.take_until_or_end(|c| !c.is_whitespace());
        assert_eq!(ci.str(), "abcd");

        let mut ci = Parsey::new("\n\n");
        ci.take_until_or_end(|c| !c.is_whitespace());
        assert_eq!(ci.str(), "");
    }

    #[test]
    fn end() {
        let mut ci = Parsey::new("a\nb\nc\n");
        ci.take_until_or_end(|c| c == '\n');
        ci.take(1);
        ci.take_until_or_end(|c| c == '\n');
        ci.take(1);
        ci.take_until_or_end(|c| c == '\n');
        ci.take(1);
        assert!(ci.end());
    }
}
