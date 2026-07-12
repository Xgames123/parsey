# starryparse

A light weight zero copy parsing library for rust focused on text parsing and span recovery.

## Features

- `miette`: When enabled allows the [`crate::Span`] type to be converted to a `miette::SourceSpan`

## Roadmap

- [ ] Improve documentation and examples

## Example

```rust
use starryparse::{Parser, Spanned, ParseResult};

#[derive(Debug, PartialEq)]
enum Err {
    StringHasNoEnd,
}

fn parse_string<'c>(parser: &mut Parser<'c>) -> ParseResult<String, Spanned<Err>> {
    if let None = parser.take('"') {
        return Ok(None); // If the first char is not a " we don't consider this a string
    }

    // In this case we pass the entire span for the error.
    // You can do more processing to guess what the user meant for better span and error
    // quality.
    let string = parser
        .take_until('"')
        .ok_or(Spanned::new(Err::StringHasNoEnd, parser.span()))?;

    Ok(Some(string.str().into()))
}

assert_eq!(
    parse_string(&mut Parser::new("\"my string\""))
        .unwrap()
        .unwrap(),
    "my string".to_string()
);
```

See examples dir for more examples.

For starryparse in action look at [config_parser](https://github.com/Xgames123/config_parser)

## Licence

Copyright 2026 S.v.E.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

[http://www.apache.org/licenses/LICENSE-2.0](http://www.apache.org/licenses/LICENSE-2.0)

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
