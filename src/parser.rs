use std::convert::Infallible;

use crate::{Searcher, Span};

/// Allows you to consumes a str in steps using basic operations. like take_n take_until
/// 'c is the lifetime of the string slice this parser operates on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parser<'c> {
    code: &'c str,
    span: Span,
}
impl<'c> Parser<'c> {
    pub fn new(code: &'c str) -> Self {
        Self {
            code,
            span: Span::from_str(code),
        }
    }

    /// Returns the string slice this parser can see.
    pub fn str(&self) -> &'c str {
        &self.code[self.span.start()..self.span.end()]
    }
    /// Returns the span of the string slice this parses can see.
    pub fn span(&self) -> Span {
        self.span.clone()
    }

    /// Returns the first character of the string slice of the parser. or None if the slice has length 0
    pub fn peek_char(&mut self) -> Option<char> {
        self.str().chars().next()
    }

    /// Takes the first n **bytes** and splits it into a new parser and returns it.
    pub fn take_n(&mut self, n: usize) -> Self {
        let size = self.str().ceil_char_boundary(n);
        let (left, right) = self.span.split(size);
        self.span = right;
        Self {
            code: self.code,
            span: left,
        }
    }

    /// If the provided searcher matches [`Searcher`] take it one time else return `None`.
    ///
    /// ```rust
    /// use starryparse::Parser;
    ///
    /// let mut parser = Parser::new("11123456");
    /// assert_eq!(parser.take('1').unwrap().str(), "1")
    /// ```
    pub fn take(&mut self, mut searcher: impl Searcher) -> Option<Self> {
        if searcher.matches_start(self.str()) {
            Some(self.take_n(searcher.len()))
        } else {
            None
        }
    }

    /// Take until the searcher matches.
    ///
    /// ```rust
    /// use starryparse::Parser;
    ///
    /// let mut parser = Parser::new("123456");
    /// assert_eq!(parser.take_until('3').unwrap().str(), "12")
    /// ```
    pub fn take_until(&mut self, mut searcher: impl Searcher) -> Option<Self> {
        for (i, _) in self.str().char_indices() {
            if searcher.matches_start(&self.str()[i..]) {
                return Some(self.take_n(i));
            }
        }
        None
    }

    /// Take until the searcher matches with the matched part included.
    ///
    /// ```rust
    /// use starryparse::Parser;
    ///
    /// let mut parser = Parser::new("123456");
    /// assert_eq!(parser.take_until_inclusive('3').unwrap().str(), "123")
    /// ```
    pub fn take_until_inclusive(&mut self, mut searcher: impl Searcher) -> Option<Self> {
        for (i, _) in self.str().char_indices() {
            if searcher.matches_start(&self.str()[i..]) {
                return Some(self.take_n(i + searcher.len()));
            }
        }
        None
    }

    // Takes until the until searcher matches.
    // If meanwhile the without searchers matches. The operation is aborted and nothing will be consumed and None will be returned.
    pub fn take_until_without(
        &mut self,
        mut until: impl Searcher,
        mut without: impl Searcher,
    ) -> Option<Self> {
        for (i, _) in self.str().char_indices() {
            let str = &self.str()[i..];
            if without.matches_start(str) {
                return None;
            }
            if until.matches_start(str) {
                return Some(self.take_n(i));
            }
        }
        None
    }

    pub fn take_until_without_inclusive(
        &mut self,
        mut until: impl Searcher,
        mut without: impl Searcher,
    ) -> Option<Self> {
        for (i, _) in self.str().char_indices() {
            let str = &self.str()[i..];
            if without.matches_start(str) {
                return None;
            }
            if until.matches_start(str) {
                return Some(self.take_n(i + until.len()));
            }
        }
        None
    }

    /// This creates a copy of the parser with the same input string. (same as cloning the parser).
    pub fn fork(&self) -> Self {
        self.clone()
    }

    ///Tries a function. If it returns Some apply the result to self else throw away all work the
    ///function has done. (Forwards inner error)
    pub fn sandbox_result<O, E>(
        &mut self,
        f: impl FnOnce(&mut Parser<'c>) -> Result<Option<O>, E>,
    ) -> Result<Option<O>, E> {
        let mut duplicated = self.fork();
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
    pub fn sandbox<O>(&mut self, f: impl FnOnce(&mut Parser<'c>) -> Option<O>) -> Option<O> {
        self.sandbox_result::<O, Infallible>(|p| Ok(f(p))).unwrap()
    }

    /// Has this parser reached the end of the input string
    pub fn end(&self) -> bool {
        self.str().len() == 0
    }
}

// shorthand's
impl<'c> Parser<'c> {
    /// Same as [`Self::take_until`] but instead of returning `None` it takes the entire input string.
    pub fn take_until_or_end(&mut self, searcher: impl Searcher) -> Self {
        match self.take_until(searcher) {
            Some(v) => v,
            None => self.take_n(self.str().len()),
        }
    }

    /// Same as [`Self::take_until_without`] but instead of returning `None` it takes the entire input string.
    pub fn take_until_without_or_end(
        &mut self,
        until: impl Searcher,
        without: impl Searcher,
    ) -> Self {
        match self.take_until_without(until, without) {
            Some(v) => v,
            None => self.take_n(self.str().len()),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::Parser;

    #[test]
    fn split() {
        let mut ci = Parser::new("abcd");
        assert_eq!(
            ci.take_n(1),
            Parser {
                code: "abcd",
                span: (0..1).into()
            }
        );
        assert_eq!(
            ci,
            Parser {
                code: "abcd",
                span: (1..4).into()
            }
        );

        assert_eq!(
            ci.take_n(1),
            Parser {
                code: "abcd",
                span: (1..2).into()
            }
        );
        assert_eq!(
            ci,
            Parser {
                code: "abcd",
                span: (2..4).into()
            }
        );
    }

    #[test]
    fn take() {
        let mut parser = Parser::new("**lala");
        assert_eq!(parser.take("**").map(|v| v.str()), Some("**"));
        assert_eq!(parser.str(), "lala");
    }

    #[test]
    fn take_until() {
        let mut ci = Parser::new("abcd");
        assert_eq!(ci.take_until(|c| c == 'c').map(|p| p.str()), Some("ab"));

        assert_eq!(ci.str(), "cd");

        assert_eq!(
            ci,
            Parser {
                code: "abcd",
                span: (2..4).into(),
            }
        );

        let mut ci = Parser::new("abcd");
        assert_eq!(ci.take_until('c').map(|p| p.str()), Some("ab"));

        assert_eq!(ci.str(), "cd");

        assert_eq!(
            ci,
            Parser {
                code: "abcd",
                span: (2..4).into(),
            }
        );
    }

    #[test]
    fn take_until_inclusive() {
        let mut ci = Parser::new("abcd");
        assert_eq!(
            ci.take_until_inclusive(|c| c == 'c').map(|p| p.str()),
            Some("abc")
        );
        assert_eq!(ci.str(), "d");

        let mut ci = Parser::new("abĉd");
        assert_eq!(
            ci.take_until_inclusive(|c| c == 'ĉ').map(|p| p.str()),
            Some("abĉ")
        );
        assert_eq!(ci.str(), "d");
    }

    #[test]
    fn take_until_tag() {
        let mut ci = Parser::new("words abcd");
        assert_eq!(ci.take_until(" abc").map(|p| p.str()), Some("words"));
        assert_eq!(ci.str(), " abcd");
    }

    #[test]
    fn take_until_tag_inclusive() {
        let mut ci = Parser::new("words abcd");
        assert_eq!(
            ci.take_until_inclusive(" abc").map(|p| p.str()),
            Some("words abc")
        );
        assert_eq!(ci.str(), "d");
    }

    #[test]
    fn take_until_special_chars() {
        let mut ci = Parser::new("éabcd");
        assert_eq!(ci.take_until(|c| c == 'c').map(|p| p.str()), Some("éab"));

        assert_eq!(ci.str(), "cd");

        let mut ci = Parser::new("abcédf");
        assert_eq!(ci.take_until(|c| c == 'é').map(|p| p.str()), Some("abc"));

        assert_eq!(ci.str(), "édf");

        let mut ci = Parser::new("abcédf");
        assert_eq!(ci.take_until('é').map(|p| p.str()), Some("abc"));

        assert_eq!(ci.str(), "édf");

        let mut ci = Parser::new("abcéchïcken_df");
        assert_eq!(ci.take_until("chïcken").map(|p| p.str()), Some("abcé"));

        assert_eq!(ci.str(), "chïcken_df");
    }

    #[test]
    fn take_until_without() {
        let mut ci = Parser::new("abcd");
        assert_eq!(
            ci.take_until_without(|c| c == 'c', |_| false)
                .map(|p| p.str()),
            Some("ab")
        );

        assert_eq!(ci.str(), "cd");

        assert_eq!(
            ci,
            Parser {
                code: "abcd",
                span: (2..4).into(),
            }
        );

        let mut ci = Parser::new("hello world");
        assert_eq!(
            ci.take_until_without("world", '\n').map(|p| p.str()),
            Some("hello ")
        );

        assert_eq!(ci.str(), "world");

        let mut ci = Parser::new("hello\nworld");
        assert_eq!(ci.take_until_without("world", '\n').map(|p| p.str()), None);

        assert_eq!(ci.str(), "hello\nworld");
    }

    #[test]
    fn take_until_without_abort() {
        let mut ci = Parser::new("abwcd");
        assert_eq!(
            ci.take_until_without(|c| c == 'c', 'w').map(|p| p.str()),
            None
        );
    }

    #[test]
    fn take_until_newline() {
        let mut ci = Parser::new("abcd\n");
        assert_eq!(
            ci.take_until_or_end('\n'),
            Parser {
                code: "abcd\n",
                span: (0..4).into()
            }
        );

        assert_eq!(
            ci,
            Parser {
                code: "abcd\n",
                span: (4..5).into(),
            }
        );

        assert_eq!(ci.str(), "\n");
    }

    #[test]
    fn skip_whitespace() {
        let mut ci = Parser::new(" \nabcd");
        ci.take_until_or_end(|c: char| !c.is_whitespace());
        assert_eq!(ci.str(), "abcd");

        let mut ci = Parser::new("\n\n");
        ci.take_until_or_end(|c: char| !c.is_whitespace());
        assert_eq!(ci.str(), "");
    }

    #[test]
    fn end() {
        let mut ci = Parser::new("a\nb\nc\n");
        ci.take_until_or_end(|c| c == '\n');
        ci.take_n(1);
        ci.take_until_or_end(|c| c == '\n');
        ci.take_n(1);
        ci.take_until_or_end(|c| c == '\n');
        ci.take_n(1);
        assert!(ci.end());
    }
}
