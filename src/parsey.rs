use std::convert::Infallible;

use crate::{Searcher, Span};

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
        &self.code[self.span.start()..self.span.end()]
    }
    pub fn span(&self) -> Span {
        self.span.clone()
    }

    pub fn peek_char(&mut self) -> Option<char> {
        self.str().chars().next()
    }

    pub fn take_n(&mut self, size: usize) -> Self {
        let size = self.str().ceil_char_boundary(size);
        let (left, right) = self.span.split(size);
        self.span = right;
        Self {
            code: self.code,
            span: left,
        }
    }

    pub fn take(&mut self, searcher: impl Searcher) -> Option<Self> {
        if searcher.matches_start(self.str()) {
            Some(self.take_n(searcher.len()))
        } else {
            None
        }
    }

    pub fn take_until(&mut self, searcher: impl Searcher) -> Option<Self> {
        for (i, _) in self.str().char_indices() {
            if searcher.matches_start(&self.str()[i..]) {
                return Some(self.take_n(i));
            }
        }
        None
    }

    pub fn take_until_inclusive(&mut self, searcher: impl Searcher) -> Option<Self> {
        for (i, _) in self.str().char_indices() {
            if searcher.matches_start(&self.str()[i..]) {
                return Some(self.take_n(i + searcher.len()));
            }
        }
        None
    }

    // Takes until the until function returns true.
    // When the without function returns true the operation is aborted, None is returned and nothing is consumed.
    pub fn take_until_without(
        &mut self,
        until: impl Searcher,
        without: impl Searcher,
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
        until: impl Searcher,
        without: impl Searcher,
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

    pub fn fork(&self) -> Self {
        self.clone()
    }

    ///Tries a function. If it returns Some apply the result to self else throw away all work the
    ///function has done. (Forwards inner error)
    pub fn sandbox_result<O, E>(
        &mut self,
        f: impl FnOnce(&mut Parsey<'a>) -> Result<Option<O>, E>,
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
    pub fn sandbox<O>(&mut self, f: impl FnOnce(&mut Parsey<'a>) -> Option<O>) -> Option<O> {
        self.sandbox_result::<O, Infallible>(|p| Ok(f(p))).unwrap()
    }

    pub fn end(&self) -> bool {
        self.str().len() == 0
    }
}

// shorthand's
impl<'a> Parsey<'a> {
    pub fn take_until_or_end(&mut self, searcher: impl Searcher) -> Self {
        match self.take_until(searcher) {
            Some(v) => v,
            None => self.take_n(self.str().len()),
        }
    }

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
    use crate::Parsey;

    #[test]
    fn split() {
        let mut ci = Parsey::new("abcd");
        assert_eq!(
            ci.take_n(1),
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
            ci.take_n(1),
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
    fn take() {
        let mut parser = Parsey::new("**lala");
        assert_eq!(parser.take("**").map(|v| v.str()), Some("**"));
        assert_eq!(parser.str(), "lala");
    }

    #[test]
    fn take_until() {
        let mut ci = Parsey::new("abcd");
        assert_eq!(ci.take_until(|c| c == 'c').map(|p| p.str()), Some("ab"));

        assert_eq!(ci.str(), "cd");

        assert_eq!(
            ci,
            Parsey {
                code: "abcd",
                span: (2..4).into(),
            }
        );

        let mut ci = Parsey::new("abcd");
        assert_eq!(ci.take_until('c').map(|p| p.str()), Some("ab"));

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
    fn take_until_inclusive() {
        let mut ci = Parsey::new("abcd");
        assert_eq!(
            ci.take_until_inclusive(|c| c == 'c').map(|p| p.str()),
            Some("abc")
        );
        assert_eq!(ci.str(), "d");

        let mut ci = Parsey::new("abĉd");
        assert_eq!(
            ci.take_until_inclusive(|c| c == 'ĉ').map(|p| p.str()),
            Some("abĉ")
        );
        assert_eq!(ci.str(), "d");
    }

    #[test]
    fn take_until_tag() {
        let mut ci = Parsey::new("words abcd");
        assert_eq!(ci.take_until(" abc").map(|p| p.str()), Some("words"));
        assert_eq!(ci.str(), " abcd");
    }

    #[test]
    fn take_until_tag_inclusive() {
        let mut ci = Parsey::new("words abcd");
        assert_eq!(
            ci.take_until_inclusive(" abc").map(|p| p.str()),
            Some("words abc")
        );
        assert_eq!(ci.str(), "d");
    }

    #[test]
    fn take_until_special_chars() {
        let mut ci = Parsey::new("éabcd");
        assert_eq!(ci.take_until(|c| c == 'c').map(|p| p.str()), Some("éab"));

        assert_eq!(ci.str(), "cd");

        let mut ci = Parsey::new("abcédf");
        assert_eq!(ci.take_until(|c| c == 'é').map(|p| p.str()), Some("abc"));

        assert_eq!(ci.str(), "édf");

        let mut ci = Parsey::new("abcédf");
        assert_eq!(ci.take_until('é').map(|p| p.str()), Some("abc"));

        assert_eq!(ci.str(), "édf");

        let mut ci = Parsey::new("abcéchïcken_df");
        assert_eq!(ci.take_until("chïcken").map(|p| p.str()), Some("abcé"));

        assert_eq!(ci.str(), "chïcken_df");
    }

    #[test]
    fn take_until_without() {
        let mut ci = Parsey::new("abcd");
        assert_eq!(
            ci.take_until_without(|c| c == 'c', |_| false)
                .map(|p| p.str()),
            Some("ab")
        );

        assert_eq!(ci.str(), "cd");

        assert_eq!(
            ci,
            Parsey {
                code: "abcd",
                span: (2..4).into(),
            }
        );

        let mut ci = Parsey::new("hello world");
        assert_eq!(
            ci.take_until_without("world", '\n').map(|p| p.str()),
            Some("hello ")
        );

        assert_eq!(ci.str(), "world");

        let mut ci = Parsey::new("hello\nworld");
        assert_eq!(ci.take_until_without("world", '\n').map(|p| p.str()), None);

        assert_eq!(ci.str(), "hello\nworld");
    }

    #[test]
    fn take_until_without_abort() {
        let mut ci = Parsey::new("abwcd");
        assert_eq!(
            ci.take_until_without(|c| c == 'c', 'w').map(|p| p.str()),
            None
        );
    }

    #[test]
    fn take_until_newline() {
        let mut ci = Parsey::new("abcd\n");
        assert_eq!(
            ci.take_until_or_end('\n'),
            Parsey {
                code: "abcd\n",
                span: (0..4).into()
            }
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
        ci.take_until_or_end(|c: char| !c.is_whitespace());
        assert_eq!(ci.str(), "abcd");

        let mut ci = Parsey::new("\n\n");
        ci.take_until_or_end(|c: char| !c.is_whitespace());
        assert_eq!(ci.str(), "");
    }

    #[test]
    fn end() {
        let mut ci = Parsey::new("a\nb\nc\n");
        ci.take_until_or_end(|c| c == '\n');
        ci.take_n(1);
        ci.take_until_or_end(|c| c == '\n');
        ci.take_n(1);
        ci.take_until_or_end(|c| c == '\n');
        ci.take_n(1);
        assert!(ci.end());
    }
}
