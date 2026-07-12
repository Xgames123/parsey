#![doc = include_str!("../README.md")]
mod parse_any;
mod parser;
mod searcher;
mod span;
mod spanned;

pub use {parser::*, searcher::*, span::*, spanned::*};

/// The result of a parse operation.
/// - `Ok(None)`: The provided input is not of the right type.
/// - `Err()`: The provided input is of the right type but it could not be parsed.
/// - `Ok(Some())`: The parse operation has succeeded.
///
/// # Example
/// a parse_number function should return:
/// - `Err`: On an input like this: '10a5'
/// - `Ok(Some(Number))`: On an input like '393.5'
/// - `Ok(None)`: On an input like 'variable'
pub type ParseResult<T, E> = Result<Option<T>, E>;
