/// Tries parsers in order until one returns Ok(Some) or Err.
///
/// Provided parse functions can return can return a [`crate::ParseResult`] with a
/// type and error that can be converted to the output type.
///
///```rust
/// use starryparse::{Parser, ParseResult, parse_any};
///
/// #[derive(Debug, PartialEq)]
/// enum Token {Number, String}
/// fn parse_number<'c>(parser: &mut Parser<'c>) -> ParseResult<Token, ()> {
///     let num = parser.take_until_or_end(|c: char|!c.is_digit(10));
///     if num.str().len() > 0 {
///         Ok(Some(Token::Number))
///     } else {
///         Ok(None)
///     }
/// }
///
///fn parse_string<'c>(parser: &mut Parser<'c>) -> ParseResult<Token, ()> {
///     let stri = parser.take_until_or_end(|c: char|!c.is_alphabetic());
///     if stri.str().len() > 0 {
///         Ok(Some(Token::String))
///     } else {
///         Ok(None)
///     }
///}
///
///let mut parser = Parser::new("123,abc");
///let result: ParseResult<Token, ()> = parse_any!(&mut parser, parse_number, parse_string);
///assert_eq!(result.unwrap().unwrap(), Token::Number);
///```
#[macro_export]
macro_rules! parse_any {
    ($parser:expr$(=>$type:ty)?, $($parse_func:expr),*) => {
        {
            let result$(: $type)? = if false {
                unreachable!();
            }
            $( else if let result = $parser($parser) && let Ok(Some(_)) | Err(_) = result {
                result.map_err(|e|e.into()).map(|v|v.map(|v|v.into()))
            } )*
            else {
                Ok(None)
            };
            result
        }

    };
}
