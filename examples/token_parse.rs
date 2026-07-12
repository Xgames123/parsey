use parsey::{ParseResult, Parsey, Spanned, parse_any};

#[derive(Debug, PartialEq)]
enum Err {
    StringHasNoEnd,
}

#[derive(Debug, PartialEq)]
struct VarRef {
    var: String,
}

#[derive(Debug, PartialEq)]
enum Token {
    String(String),
    VarRef(VarRef),
}
impl From<VarRef> for Token {
    fn from(value: VarRef) -> Self {
        Token::VarRef(value)
    }
}
impl From<String> for Token {
    fn from(value: String) -> Self {
        Token::String(value)
    }
}

fn parse_string<'c>(parser: &mut Parsey<'c>) -> ParseResult<String, Spanned<Err>> {
    if let None = parser.take('"') {
        return Ok(None); // If the first char is not a " we don't consider this a string
    }

    let string = parser.take_until('"').ok_or_else(|| {
        // Approximate where the string should end to get better quality spans.
        let aproximated_string = parser.take_until_or_end(['\n', ',', ')']);
        // In this case we pass the entire span for the error.
        // You can do more processing to guess what the user meant for better span and error
        // quality.
        Spanned::new(Err::StringHasNoEnd, aproximated_string.span())
    })?;

    Ok(Some(string.str().into()))
}

fn is_valid_ident_char(char: char) -> bool {
    char.is_ascii_alphanumeric() || ['_', '-'].contains(&char)
}

fn parse_var<'c>(parser: &mut Parsey<'c>) -> ParseResult<VarRef, Spanned<Err>> {
    // If the first char is not a valid ident char this is not an identifier.
    if let None = parser.fork().take(is_valid_ident_char) {
        return Ok(None);
    }
    let ident = parser.take_until_or_end(|char: char| !is_valid_ident_char(char));

    Ok(Some(VarRef {
        var: ident.str().into(),
    }))
}

fn parse_token<'c>(parser: &mut Parsey<'c>) -> ParseResult<Token, Spanned<Err>> {
    parse_any!(parser, parse_string, parse_var)
}

fn main() {
    assert_eq!(
        parse_token(&mut Parsey::new("my_var")).unwrap().unwrap(),
        Token::VarRef(VarRef {
            var: "my_var".into()
        })
    );

    assert_eq!(
        parse_token(&mut Parsey::new("\"my string\""))
            .unwrap()
            .unwrap(),
        Token::String("my string".into())
    );
}
