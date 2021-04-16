//! Converts each line of an input into a list of tokens.

use std::iter::Peekable;

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Location, Range, Ranged, SourceFileIdentifier},
};
use quill_source_file::PackageFileSystem;

#[derive(Debug, PartialEq, Eq)]
pub enum TokenType {
    /// `=`
    Assign,
    /// `:`
    Type,
    /// `->`
    Arrow,
    /// `_`
    Underscore,
    /// `.`
    Dot,
    /// `::`
    Scope,
    /// `|`
    TypeOr,
    /// '\'
    Lambda,
    /// ',' or '\n' after certain characters
    EndOfLine {
        explicit: bool,
    },

    LeftParenthesis,
    RightParenthesis,
    LeftSquare,
    RightSquare,
    LeftBrace,
    RightBrace,

    Pub,
    Data,
    Variant,
    Enum,
    Def,
    Let,
    Use,
    CompilerIntrinsic,

    Identifier(String),
}

/// A single token such as an identifier or special character.
#[derive(Debug)]
pub struct Token {
    pub token_type: TokenType,
    pub range: Range,
}

impl Ranged for Token {
    fn range(&self) -> Range {
        self.range
    }
}

/// A list of tokens grouped by a set of matching brackets.
#[derive(Debug)]
pub struct Tree {
    /// The range representing the open bracket.
    pub open: Range,
    /// The range representing the close bracket.
    pub close: Range,
    /// The actual tokens inside this tree node.
    pub tokens: Vec<TokenTree>,
    /// What kind of brackets does this token tree represent?
    pub bracket_type: BracketType,
}

impl Ranged for Tree {
    fn range(&self) -> Range {
        self.open.union(self.close)
    }
}

/// A program (and by extension a line of code) is subdivided into token trees, which are essentially bracketed groups.
/// For example, in the expression `1 + (2 + 3) + 4`, the token trees are `[1, +, [2, +, 3], +, 4]`.
#[derive(Debug)]
pub enum TokenTree {
    Token(Token),
    Tree(Tree),
}

#[derive(Debug, PartialEq, Eq)]
pub enum BracketType {
    Parentheses,
    Square,
    Brace,
}

impl Ranged for TokenTree {
    fn range(&self) -> Range {
        match self {
            TokenTree::Token(token) => token.range,
            TokenTree::Tree(tree) => tree.range(),
        }
    }
}

/// Lexes a source file. This function reads a source file from disk (if not cached), splits it into tokens, and groups those tokens into token trees.
pub async fn lex(
    fs: &PackageFileSystem,
    source_file: &SourceFileIdentifier,
) -> DiagnosticResult<Vec<TokenTree>> {
    tokenise(fs, source_file)
        .await
        .bind(|tokens| group_token_trees(tokens, source_file))
}

/// Takes a linear list of tokens, and sorts them into a hierarchy of token trees according to the use of brackets.
fn group_token_trees(
    tokens: Vec<Token>,
    source_file: &SourceFileIdentifier,
) -> DiagnosticResult<Vec<TokenTree>> {
    #[derive(Debug)]
    struct OpenBracket {
        /// The range representing the open bracket.
        open: Range,
        /// The actual tokens inside this tree node.
        tokens: Vec<TokenTree>,
        /// What kind of brackets does this token tree represent?
        /// If none, this token tree represents the whole program.
        bracket_type: Option<BracketType>,
    }

    // Every time we encounter an open bracket, put it on the stack.
    // When we encounter a closing bracket, pop off the top element of the stack and check that the bracket type matches.
    let mut open_bracket_stack = vec![OpenBracket {
        open: Location { line: 0, col: 0 }.into(),
        tokens: Vec::new(),
        bracket_type: None,
    }];

    for token in tokens {
        match token.token_type {
            TokenType::LeftParenthesis | TokenType::LeftSquare | TokenType::LeftBrace => {
                let bracket_type = match token.token_type {
                    TokenType::LeftParenthesis => BracketType::Parentheses,
                    TokenType::LeftSquare => BracketType::Square,
                    TokenType::LeftBrace => BracketType::Brace,
                    _ => panic!(),
                };
                open_bracket_stack.push(OpenBracket {
                    open: token.range,
                    tokens: Vec::new(),
                    bracket_type: Some(bracket_type),
                });
            }
            TokenType::RightParenthesis | TokenType::RightSquare | TokenType::RightBrace => {
                // Pop the top element on the stack and check that the bracket type matches.
                let open_bracket = open_bracket_stack.pop().expect("bracket stack was empty");
                let bracket_type = match token.token_type {
                    TokenType::RightParenthesis => BracketType::Parentheses,
                    TokenType::RightSquare => BracketType::Square,
                    TokenType::RightBrace => BracketType::Brace,
                    _ => panic!(),
                };
                match open_bracket.bracket_type {
                    Some(other_bracket_type) => {
                        if other_bracket_type == bracket_type {
                            // The bracket type matched. Turn this open/close bracket pair into a token tree.
                            let tree = Tree {
                                open: open_bracket.open,
                                close: token.range,
                                tokens: open_bracket.tokens,
                                bracket_type,
                            };
                            // Add this tree to the new top item on the stack.
                            // This can't fail, since the lowest item on the stack is the entire program, which has no bracket type.
                            // Hence the entire program can never match any closing bracket, and hence will never be popped without immediately
                            // quitting this compilation step.
                            open_bracket_stack
                                .last_mut()
                                .expect("entire program should never be popped")
                                .tokens
                                .push(TokenTree::Tree(tree));
                        } else {
                            return DiagnosticResult::fail(ErrorMessage::new_with(
                                "this opening bracket didn't match the closing bracket".to_string(),
                                Severity::Error,
                                Diagnostic::at(source_file, &open_bracket.open),
                                HelpMessage {
                                    message: "closing bracket was here".to_string(),
                                    help_type: HelpType::Note,
                                    diagnostic: Diagnostic::at(source_file, &token),
                                },
                            ));
                        }
                    }
                    None => {
                        return DiagnosticResult::fail(ErrorMessage::new(
                            "closing bracket had no opening bracket to pair with".to_string(),
                            Severity::Error,
                            Diagnostic::at(source_file, &token),
                        ));
                    }
                }
            }
            _ => {
                open_bracket_stack
                    .last_mut()
                    .expect("open bracket stack was empty")
                    .tokens
                    .push(TokenTree::Token(token));
            }
        }
    }

    // The open bracket stack should have exactly one element on it, otherwise there are some unclosed brackets.
    if open_bracket_stack.len() > 1 {
        open_bracket_stack
            .into_iter()
            .skip(1)
            .map(|open_bracket| {
                DiagnosticResult::fail(ErrorMessage::new(
                    "this opening bracket was not closed".to_string(),
                    Severity::Error,
                    Diagnostic::at(source_file, &open_bracket.open),
                ))
            })
            .collect::<DiagnosticResult<_>>()
            .deny()
    } else {
        DiagnosticResult::ok(
            open_bracket_stack
                .pop()
                .expect("open bracket stack was empty")
                .tokens,
        )
    }
}

/// This function is asynchronous since it may read the file from disk.
async fn tokenise(
    fs: &PackageFileSystem,
    source_file: &SourceFileIdentifier,
) -> DiagnosticResult<Vec<Token>> {
    fs.with_source_file(source_file, |source| match source {
        Ok(source) => source
            .get_contents()
            .lines()
            .enumerate()
            .map(|(line_number, line)| tokenise_line(source_file, line_number as u32, line))
            .collect::<DiagnosticResult<Vec<Vec<Token>>>>()
            .map(|lines| lines.into_iter().flatten().collect()),
        Err(_) => DiagnosticResult::fail(ErrorMessage::new(
            "could not read file".to_string(),
            Severity::Error,
            Diagnostic::in_file(source_file),
        )),
    })
    .await
}

/// Removes the leading whitespace, and then returns the list of tokens on this line.
fn tokenise_line(
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
        let token = parse_token(source_file, line_number, &mut chars);
        if matches!(token.value(), Some(ParseTokenResult::CommentLine)) {
            break;
        }
        let should_break = token.failed();

        tokens.push(token.map(|result| {
            if let ParseTokenResult::Token(token) = result {
                token
            } else {
                panic!("tried to push a non-token")
            }
        }));

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

    DiagnosticResult::sequence(tokens).map(|mut tokens| {
        // If the last token on the line could be the end of an expression/item, append a semicolon.
        if let Some(token) = tokens.last() {
            if should_insert_semicolon_after(&token.token_type) {
                let range = Location {
                    line: token.range.end.line,
                    col: token.range.end.col + 1,
                }
                .into();
                tokens.push(Token {
                    token_type: TokenType::EndOfLine { explicit: false },
                    range,
                })
            }
        }
        tokens
    })
}

/// If this token type appears at the end of a line, do we insert an implicit semicolon afterwards?
fn should_insert_semicolon_after(ty: &TokenType) -> bool {
    matches!(
        ty,
        TokenType::Identifier(_)
            | TokenType::RightBrace
            | TokenType::RightParenthesis
            | TokenType::RightSquare
    )
}

/// When we have parsed a token, what was the result?
enum ParseTokenResult {
    /// We got a token, as expected.
    Token(Token),
    /// We got a '//' token, which means we are starting a comment line.
    CommentLine,
}

impl From<Token> for ParseTokenResult {
    fn from(token: Token) -> Self {
        Self::Token(token)
    }
}

/// This function parses a single token from the input stream.
/// It must consume at least one character from `chars` if it did not return a `DiagnosticResult::fail`,
/// otherwise we'll end up in an infinite loop.
/// In order to parse correctly, tokens must be separated from each other, or they will be grouped into a single token.
/// Therefore, symbolic tokens e.g. '+' are separated from alphanumeric tokens e.g. 'append' automatically.
/// Putting two symbolic tokens next to each other requires spacing.
fn parse_token(
    source_file: &SourceFileIdentifier,
    line: u32,
    chars: &mut Peekable<impl Iterator<Item = (u32, char)>>,
) -> DiagnosticResult<ParseTokenResult> {
    let (col, ch) = *chars.peek().unwrap();

    if ch.is_control() {
        return DiagnosticResult::fail(ErrorMessage::new(
            String::from("unexpected control character"),
            Severity::Error,
            Diagnostic::at_location(source_file, Location { line, col }),
        ));
    }

    match ch {
        '(' => {
            chars.next();
            DiagnosticResult::ok(
                Token {
                    token_type: TokenType::LeftParenthesis,
                    range: Location { line, col }.into(),
                }
                .into(),
            )
        }
        ')' => {
            chars.next();
            DiagnosticResult::ok(
                Token {
                    token_type: TokenType::RightParenthesis,
                    range: Location { line, col }.into(),
                }
                .into(),
            )
        }
        '[' => {
            chars.next();
            DiagnosticResult::ok(
                Token {
                    token_type: TokenType::LeftSquare,
                    range: Location { line, col }.into(),
                }
                .into(),
            )
        }
        ']' => {
            chars.next();
            DiagnosticResult::ok(
                Token {
                    token_type: TokenType::RightSquare,
                    range: Location { line, col }.into(),
                }
                .into(),
            )
        }
        '{' => {
            chars.next();
            DiagnosticResult::ok(
                Token {
                    token_type: TokenType::LeftBrace,
                    range: Location { line, col }.into(),
                }
                .into(),
            )
        }
        '}' => {
            chars.next();
            DiagnosticResult::ok(
                Token {
                    token_type: TokenType::RightBrace,
                    range: Location { line, col }.into(),
                }
                .into(),
            )
        }
        _ => {
            chars.next();
            if ch == '/' && matches!(chars.peek(), Some((_, '/'))) {
                // This is a comment line.
                return DiagnosticResult::ok(ParseTokenResult::CommentLine);
            }

            if ch.is_alphanumeric() {
                let (identifier, range) = consume_predicate_one(line, col, ch, chars, |c| {
                    c.is_alphanumeric() || c == '_'
                });
                let token_type = token_type_alphabetic(identifier);
                DiagnosticResult::ok(Token { token_type, range }.into())
            } else {
                let (identifier, range) = consume_predicate_one(line, col, ch, chars, |c| {
                    !c.is_alphanumeric()
                        && !c.is_whitespace()
                        && !vec!['(', ')', '{', '}', '[', ']'].contains(&c)
                });
                let token_type = token_type_symbol(identifier);
                DiagnosticResult::ok(Token { token_type, range }.into())
            }
        }
    }
}

/// Given an identifier make of alphanumeric characters, determine the token type.
/// If no specific in-built token type was deduced, the token is simply an `Identifier`.
fn token_type_alphabetic(s: String) -> TokenType {
    use unicode_normalization::UnicodeNormalization;
    match s.nfc().collect::<String>().as_str() {
        "pub" => TokenType::Pub,
        "data" => TokenType::Data,
        "variant" => TokenType::Variant,
        "enum" => TokenType::Enum,
        "def" => TokenType::Def,
        "let" => TokenType::Let,
        "use" => TokenType::Use,
        "compiler_intrinsic" => TokenType::CompilerIntrinsic,
        _ => TokenType::Identifier(s),
    }
}

/// Given an identifier make of symbolic characters, determine the token type.
/// If no specific in-built token type was deduced, the token is simply an `Identifier`.
fn token_type_symbol(s: String) -> TokenType {
    use unicode_normalization::UnicodeNormalization;
    match s.nfc().collect::<String>().as_str() {
        "=" => TokenType::Assign,
        ":" => TokenType::Type,
        "->" => TokenType::Arrow,
        "_" => TokenType::Underscore,
        "." => TokenType::Dot,
        "::" => TokenType::Scope,
        "|" => TokenType::TypeOr,
        "\\" => TokenType::Lambda,
        "," => TokenType::EndOfLine { explicit: true },
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

/// Consumes all characters conforming to a given predicate, adding on the given initial character.
/// Returns the range of characters that the string contains.
/// If no characters were consumed, the range might be meaningless.
fn consume_predicate_one<I, P>(
    line: u32,
    start_col: u32,
    ch: char,
    chars: &mut Peekable<I>,
    predicate: P,
) -> (String, Range)
where
    I: Iterator<Item = (u32, char)>,
    P: Fn(char) -> bool,
{
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
