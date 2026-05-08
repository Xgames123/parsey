use std::ops::Deref;

use crate::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T> {
    pub span: Span,
    pub inner: T,
}
impl<T> Spanned<T> {
    pub fn null_span(inner: T) -> Self {
        Self {
            span: (0..0).into(),
            inner,
        }
    }
    pub fn new(inner: T, span: impl Into<Span>) -> Self {
        Self {
            span: span.into(),
            inner,
        }
    }
}
impl<T> Deref for Spanned<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}
