use std::ops::Range;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Span(Range<usize>);
impl Span {
    pub fn from_str(str: &str) -> Self {
        Self(0..str.len())
    }

    pub fn start(&self) -> usize {
        self.0.start
    }
    pub fn end(&self) -> usize {
        self.0.end
    }
    pub fn len(&self) -> usize {
        self.0.end - self.0.start
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

#[cfg(feature = "miette")]
impl Into<miette::SourceSpan> for Span {
    fn into(self) -> miette::SourceSpan {
        (self.start(), self.len()).into()
    }
}
impl Into<Range<usize>> for Span {
    fn into(self) -> Range<usize> {
        self.0
    }
}
