use std::ops::Deref;

use crate::Span;

/// Wraps a type and associates a [`Span`] with it
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T> {
    pub span: Span,
    pub inner: T,
}
impl<T> Spanned<T> {
    /// Creates a instance with a null span (a span ranging from 0 to 0)
    pub fn null_span(inner: T) -> Self {
        Self {
            span: Span::NULL,
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

impl<T> From<T> for Spanned<T> {
    fn from(value: T) -> Self {
        Self::null_span(value)
    }
}
