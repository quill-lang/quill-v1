//! Converts each line of an input into a list of tokens.

use std::iter::Peekable;

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, Severity},
    location::{Location, Range, SourceFileIdentifier},
};
use quill_source_file::PackageFileSystem;

#[derive(Debug, PartialEq, Eq)]
pub enum TokenType {
    Assign,
    Type,
    Arrow,
    Underscore,
    Dot,

    LeftParenthesis,
    RightParenthesis,

    Let,

    Identifier(String),
}

#[derive(Debug)]
pub struct Token {
    pub token_type: TokenType,
    pub range: Range,
}

/// This function is asynchronous since it may read the file from disk.
pub async fn lex(
    fs: &PackageFileSystem,
    source_file: &SourceFileIdentifier,
) -> DiagnosticResult<Vec<Vec<Token>>> {
    fs.with_source_file(source_file, |source| match source {
        Ok(source) => source
            .get_contents()
            .lines()
            .enumerate()
            .map(|(line_number, line)| lex_line(source_file, line_number as u32, line))
            .collect(),
        Err(_) => DiagnosticResult::fail(ErrorMessage::new(
            "could not read file".to_string(),
            Severity::Error,
            Diagnostic::in_file(source_file.clone()),
        )),
    })
    .await
}

/// Returns the leading whitespace and then the list of tokens on this line.
fn lex_line(
    source_file: &SourceFileIdentifier,
    line_number: u32,
    line: &str,
) -> DiagnosticResult<Vec<Token>> {
    let mut chars = line
        .chars()
        .enumerate()
        .map(|(i, c)| (i as u32, c))
        .peekable();
    let mut tokens = Vec::new();

    // Consume leading whitespace.
    consume_whitespace(line_number, &mut chars);

    while let Some(&(col, _)) = chars.peek() {
        let token = lex_token(source_file, line_number, &mut chars);
        let should_break = token.failed();
        tokens.push(token);
        if should_break {
            break;
        }

        // Check that we actually consumed a character inside `lex_token`.
        if let Some(&(col2, _)) = chars.peek() {
            if col2 == col {
                panic!("no characters were consumed by `lex_token`, but it returned a success, at col {} of line \"{}\"", col, line);
            }
        }
        consume_whitespace(line_number, &mut chars);
    }

    DiagnosticResult::sequence(tokens)
}

/// This function parses a single token from the input stream.
/// It must consume at least one character from `chars` if it did not return a `DiagnosticResult::fail`,
/// otherwise we'll end up in an infinite loop.
/// In order to parse correctly, tokens must be separated from each other, or they will be grouped into a single token.
/// Therefore, symbolic tokens e.g. '+' are separated from alphanumeric tokens e.g. 'append' automatically.
/// Putting two symbolic tokens next to each other requires spacing.
fn lex_token(
    source_file: &SourceFileIdentifier,
    line: u32,
    chars: &mut Peekable<impl Iterator<Item = (u32, char)>>,
) -> DiagnosticResult<Token> {
    let (col, ch) = *chars.peek().unwrap();

    if ch.is_control() {
        return DiagnosticResult::fail(ErrorMessage::new(
            String::from("unexpected control character"),
            Severity::Error,
            Diagnostic::at_location(source_file.clone(), Location { line, col }),
        ));
    }

    match ch {
        '(' => {
            chars.next();
            DiagnosticResult::ok(Token {
                token_type: TokenType::LeftParenthesis,
                range: Location { line, col }.into(),
            })
        }
        ')' => {
            chars.next();
            DiagnosticResult::ok(Token {
                token_type: TokenType::RightParenthesis,
                range: Location { line, col }.into(),
            })
        }
        _ => {
            if ch.is_alphanumeric() {
                let (identifier, range) =
                    consume_predicate_one(line, chars, |c| c.is_alphanumeric() || c == '_');
                let token_type = token_type_alphabetic(identifier);
                DiagnosticResult::ok(Token { token_type, range })
            } else {
                let (identifier, range) = consume_predicate_one(line, chars, |c| {
                    !c.is_alphanumeric() && !c.is_whitespace() && !vec!['(', ')'].contains(&c)
                });
                let token_type = token_type_symbol(identifier);
                DiagnosticResult::ok(Token { token_type, range })
            }
        }
    }
}

/// Given an identifier make of alphanumeric characters, determine the token type.
/// If no specific in-built token type was deduced, the token is simply an `Identifier`.
fn token_type_alphabetic(s: String) -> TokenType {
    match s.as_str() {
        "let" => TokenType::Let,
        _ => TokenType::Identifier(s),
    }
}

/// Given an identifier make of symbolic characters, determine the token type.
/// If no specific in-built token type was deduced, the token is simply an `Identifier`.
fn token_type_symbol(s: String) -> TokenType {
    match s.as_str() {
        "=" => TokenType::Assign,
        ":" => TokenType::Type,
        "->" => TokenType::Arrow,
        "_" => TokenType::Underscore,
        "." => TokenType::Dot,
        _ => TokenType::Identifier(s),
    }
}

/// Consumes all characters conforming to a given predicate.
/// Returns the range of characters that the string contains.
/// If no characters were consumed, the range might be meaningless.
#[rustfmt::skip] // rustfmt messes up the Location blocks and makes them look different
fn consume_predicate<I, P>(line: u32, chars: &mut Peekable<I>, predicate: P) -> (String, Range)
where
    I: Iterator<Item = (u32, char)>,
    P: Fn(char) -> bool,
{
    let start_col = chars.peek().map(|value| value.0).unwrap_or(0);
    // Every loop iteration, we update end_col. This is because we can't be sure that there will be a next character to peek at.
    let mut end_col = start_col;

    let mut s = String::new();
    while let Some(&(_, ch)) = chars.peek() {
        if predicate(ch) {
            end_col += 1;
            s.push(ch);
            chars.next();
        } else {
            break;
        }
    }

    let start = Location { line, col: start_col };
    let end = Location { line, col: end_col };

    (s, Range { start, end })
}

/// Consumes one character, and then all characters conforming to a given predicate.
/// Returns the range of characters that the string contains.
/// If no characters were consumed, the range might be meaningless.
fn consume_predicate_one<I, P>(line: u32, chars: &mut Peekable<I>, predicate: P) -> (String, Range)
where
    I: Iterator<Item = (u32, char)>,
    P: Fn(char) -> bool,
{
    let (start_col, ch) = chars.next().unwrap();
    let (mut s, mut range) = consume_predicate(line, chars, predicate);
    if s.is_empty() {
        range.end.col = start_col + 1;
    }
    s.insert(0, ch);
    range.start.col = start_col;
    (s, range)
}

fn consume_whitespace<I>(line: u32, chars: &mut Peekable<I>) -> (String, Range)
where
    I: Iterator<Item = (u32, char)>,
{
    consume_predicate(line, chars, |c| c.is_whitespace())
}

mod test {
    #[tokio::test]
    async fn test_lexer() {
        use quill_common::location::SourceFileIdentifier;
        use quill_source_file::ErrorEmitter;
        use quill_source_file::PackageFileSystem;
        use std::path::PathBuf;

        use crate::lex;

        let fs = PackageFileSystem::new(PathBuf::from("test"));
        let lexed = lex(
            &fs,
            &SourceFileIdentifier {
                module: vec![].into(),
                file: "file".into(),
            },
        )
        .await;

        let mut error_emitter = ErrorEmitter::new(&fs);
        let lexed = error_emitter.consume_diagnostic(lexed);
        error_emitter.emit_all().await;

        // If the lex fails, the test will fail.
        let lexed = lexed.unwrap();

        println!("lexed: {:?}", lexed);
    }
}
