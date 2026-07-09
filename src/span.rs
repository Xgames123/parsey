use std::ops::Range;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    start: usize,
    end: usize,
}
impl Span {
    pub fn from_str(str: &str) -> Self {
        Self {
            start: 0,
            end: str.len(),
        }
    }

    pub fn start(&self) -> usize {
        self.start
    }
    pub fn end(&self) -> usize {
        self.end
    }
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    pub fn split(&mut self, index: usize) -> (Self, Self) {
        let index = self.start + index;
        ((self.start..index).into(), (index..self.end).into())
    }
}

impl From<Range<usize>> for Span {
    fn from(value: Range<usize>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
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
        self.start..self.end
    }
}
