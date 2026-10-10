use crate::space::{ParDataParser, Space};
use mork_expr::{Tag, item_byte};
use mork_frontend::bytestring_parser::Parser;

/// Selector segment in the singular JSONPath subset that MORK's JSON loader
/// can encode as a direct expression path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JsonPathSegment {
    /// Object member selector, equivalent to `.name` or `['name']`.
    Member(String),
    /// Non-negative zero-based array index selector.
    Index(usize),
}

/// Parse or compile error for the deliberately small singular JSONPath subset.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JsonPathQueryError {
    /// The query string was empty.
    Empty,
    /// The query did not start with the root identifier `$`.
    MissingRoot,
    /// The parser reached the end while reading a segment.
    UnexpectedEnd { offset: usize },
    /// A member selector was empty.
    EmptyMember { offset: usize },
    /// A shorthand member selector contained an unsupported character.
    InvalidMemberShorthand { offset: usize },
    /// A bracketed member selector did not have a closing quote/bracket.
    UnterminatedMember { offset: usize },
    /// An index selector was empty or not a non-negative decimal integer.
    InvalidIndex { offset: usize },
    /// The selector is outside the supported singular subset.
    UnsupportedSelector { offset: usize },
}

/// Parses the supported singular JSONPath subset:
///
/// ```text
/// $                  root
/// .name              member shorthand
/// ['name'] / ["name"] bracketed member name without escapes
/// [0]                non-negative array index
/// ```
///
/// Filters, wildcards, slices, recursive descent, unions, negative indexes,
/// and escaped bracketed strings are intentionally rejected here. This maps
/// exact child selectors onto the expression paths produced by
/// `Space::load_json`.
pub fn parse_singular_json_path(query: &str) -> Result<Vec<JsonPathSegment>, JsonPathQueryError> {
    if query.is_empty() {
        return Err(JsonPathQueryError::Empty);
    }
    if !query.starts_with('$') {
        return Err(JsonPathQueryError::MissingRoot);
    }

    let mut offset = 1usize;
    let mut segments = Vec::new();
    while offset < query.len() {
        let byte = query.as_bytes()[offset];
        match byte {
            b'.' => {
                offset = parse_member_shorthand(query, offset, &mut segments)?;
            }
            b'[' => {
                offset = parse_bracketed_selector(query, offset, &mut segments)?;
            }
            _ => {
                return Err(JsonPathQueryError::UnsupportedSelector { offset });
            }
        }
    }

    Ok(segments)
}

impl Space {
    /// Compiles a supported singular JSONPath into the MORK expression pattern
    /// that captures the selected value as user slot 0.
    ///
    /// The returned bytes encode the equivalent of the selected JSON path. For
    /// example, `$.profile.scores[1]` becomes:
    ///
    /// ```text
    /// (profile (scores (1 $)))
    /// ```
    pub fn singular_json_path_value_pattern(
        &self,
        query: &str,
    ) -> Result<Vec<u8>, JsonPathQueryError> {
        let segments = parse_singular_json_path(query)?;
        Ok(self.json_path_value_pattern_from_segments(&segments))
    }

    /// Builds the encoded value-capturing expression pattern for parsed JSON
    /// path segments.
    pub fn json_path_value_pattern_from_segments(&self, segments: &[JsonPathSegment]) -> Vec<u8> {
        let table = self.sym_table();
        let mut parser = ParDataParser::new(&table);
        let mut out = Vec::new();
        append_path_pattern(&mut parser, segments, &mut out);
        out
    }
}

fn parse_member_shorthand(
    query: &str,
    dot_offset: usize,
    segments: &mut Vec<JsonPathSegment>,
) -> Result<usize, JsonPathQueryError> {
    let member_start = dot_offset + 1;
    if member_start >= query.len() {
        return Err(JsonPathQueryError::UnexpectedEnd { offset: dot_offset });
    }

    let mut end = member_start;
    for (relative, ch) in query[member_start..].char_indices() {
        if ch == '.' || ch == '[' {
            break;
        }
        if !(ch == '_' || ch.is_ascii_alphanumeric()) {
            return Err(JsonPathQueryError::InvalidMemberShorthand {
                offset: member_start + relative,
            });
        }
        end = member_start + relative + ch.len_utf8();
    }

    if end == member_start {
        return Err(JsonPathQueryError::EmptyMember {
            offset: member_start,
        });
    }

    segments.push(JsonPathSegment::Member(
        query[member_start..end].to_string(),
    ));
    Ok(end)
}

fn parse_bracketed_selector(
    query: &str,
    bracket_offset: usize,
    segments: &mut Vec<JsonPathSegment>,
) -> Result<usize, JsonPathQueryError> {
    let selector_start = bracket_offset + 1;
    let Some(&first) = query.as_bytes().get(selector_start) else {
        return Err(JsonPathQueryError::UnexpectedEnd {
            offset: bracket_offset,
        });
    };

    match first {
        b'\'' | b'"' => parse_quoted_member(query, selector_start, segments),
        b'0'..=b'9' => parse_index(query, selector_start, segments),
        _ => Err(JsonPathQueryError::UnsupportedSelector {
            offset: selector_start,
        }),
    }
}

fn parse_quoted_member(
    query: &str,
    quote_offset: usize,
    segments: &mut Vec<JsonPathSegment>,
) -> Result<usize, JsonPathQueryError> {
    let quote = query.as_bytes()[quote_offset];
    let member_start = quote_offset + 1;
    let mut cursor = member_start;

    while cursor < query.len() {
        let byte = query.as_bytes()[cursor];
        if byte == b'\\' {
            return Err(JsonPathQueryError::UnsupportedSelector { offset: cursor });
        }
        if byte == quote {
            let member = &query[member_start..cursor];
            let close_bracket = cursor + 1;
            if query.as_bytes().get(close_bracket) != Some(&b']') {
                return Err(JsonPathQueryError::UnterminatedMember {
                    offset: quote_offset,
                });
            }
            if member.is_empty() {
                return Err(JsonPathQueryError::EmptyMember {
                    offset: member_start,
                });
            }
            segments.push(JsonPathSegment::Member(member.to_string()));
            return Ok(close_bracket + 1);
        }
        cursor += 1;
    }

    Err(JsonPathQueryError::UnterminatedMember {
        offset: quote_offset,
    })
}

fn parse_index(
    query: &str,
    index_start: usize,
    segments: &mut Vec<JsonPathSegment>,
) -> Result<usize, JsonPathQueryError> {
    let mut cursor = index_start;
    while cursor < query.len() && query.as_bytes()[cursor].is_ascii_digit() {
        cursor += 1;
    }
    if cursor == index_start {
        return Err(JsonPathQueryError::InvalidIndex {
            offset: index_start,
        });
    }
    if query.as_bytes().get(cursor) != Some(&b']') {
        return Err(JsonPathQueryError::InvalidIndex {
            offset: index_start,
        });
    }

    let index = query[index_start..cursor].parse::<usize>().map_err(|_| {
        JsonPathQueryError::InvalidIndex {
            offset: index_start,
        }
    })?;
    segments.push(JsonPathSegment::Index(index));
    Ok(cursor + 1)
}

fn append_path_pattern(
    parser: &mut ParDataParser<'_>,
    segments: &[JsonPathSegment],
    out: &mut Vec<u8>,
) {
    let Some((head, tail)) = segments.split_first() else {
        out.push(item_byte(Tag::NewVar));
        return;
    };

    out.push(item_byte(Tag::Arity(2)));
    match head {
        JsonPathSegment::Member(member) => {
            append_symbol(parser, member.as_bytes(), out);
        }
        JsonPathSegment::Index(index) => {
            append_symbol(parser, index.to_string().as_bytes(), out);
        }
    }
    append_path_pattern(parser, tail, out);
}

fn append_symbol(parser: &mut ParDataParser<'_>, bytes: &[u8], out: &mut Vec<u8>) {
    let token = parser.tokenizer(bytes);
    out.push(item_byte(Tag::SymbolSize(token.len() as u8)));
    out.extend_from_slice(token);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_singular_json_path_accepts_member_and_index_selectors() {
        assert_eq!(
            parse_singular_json_path("$.profile['scores'][1]").unwrap(),
            vec![
                JsonPathSegment::Member("profile".to_string()),
                JsonPathSegment::Member("scores".to_string()),
                JsonPathSegment::Index(1),
            ]
        );
    }

    #[test]
    fn parse_singular_json_path_rejects_unsupported_selectors() {
        assert_eq!(
            parse_singular_json_path("$.items[*]"),
            Err(JsonPathQueryError::UnsupportedSelector { offset: 8 })
        );
        assert_eq!(
            parse_singular_json_path("$.items[-1]"),
            Err(JsonPathQueryError::UnsupportedSelector { offset: 8 })
        );
    }
}
