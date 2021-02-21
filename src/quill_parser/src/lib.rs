//! Types may have certain suffixes to declare what information they contain and where they should be used:
//! - `P`: just been Parsed, no extra information has been deduced.
//!   No type has been deduced, and no effort has been made to ensure syntactic correctness
//!   past the (lenient) parser.
//! - `C`: an intermediate data Cache, used when we're still in the middle of computing the index.
//!   After the index has been computed, we should not need to use `P` or `C` data,
//!   only `I` data should be required.
//! - `I`: an Index entry for the item.
//! - `T`: currently being type checked.
//! - (no suffix): types have been deduced and references have been resolved.

use std::{
    fmt::Debug,
    iter::Peekable,
    ops::{Deref, DerefMut},
};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, Severity},
    location::{Location, Range, Ranged, SourceFileIdentifier},
};
use quill_lexer::{BracketType, Token, TokenTree, TokenType, Tree};

struct TokenStream {
    iter: Peekable<<Vec<TokenTree> as IntoIterator>::IntoIter>,
    last_location: Location,
}

impl TokenStream {
    /// Returns the range of the next token to be consumed.
    /// This is _not_ an implementation of the `Ranged` trait since we require a mutable reference in order to peek the next token.
    fn range(&mut self) -> Range {
        self.iter
            .peek()
            .map(|token| token.range())
            .unwrap_or_else(|| self.last_location.into())
    }
}

impl Deref for TokenStream {
    type Target = Peekable<<Vec<TokenTree> as IntoIterator>::IntoIter>;

    fn deref(&self) -> &Self::Target {
        &self.iter
    }
}

impl DerefMut for TokenStream {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.iter
    }
}

/// Parses a source file. This function parses the top-level item declarations, without parsing the contents of items.
pub fn parse(
    tokens: Vec<TokenTree>,
    source_file: &SourceFileIdentifier,
) -> DiagnosticResult<ModuleP> {
    let last_location = tokens
        .last()
        .map(|token| token.range().end)
        .unwrap_or(Location { line: 0, col: 0 });
    let mut tokens = TokenStream {
        iter: tokens.into_iter().peekable(),
        last_location,
    };

    let mut parser = Parser {
        tokens: &mut tokens,
        source_file,
    };
    let mut items = Vec::new();
    while parser.tokens.peek().is_some() {
        let item = parser.parse_item();
        let failed = item.failed();
        items.push(item);
        if failed {
            break;
        }
    }

    DiagnosticResult::sequence(items).map(|items| {
        let mut data = Vec::new();
        let mut definitions = Vec::new();
        for item in items {
            match item {
                ItemP::Data(i) => data.push(i),
                ItemP::Definition(i) => definitions.push(i),
            }
        }
        ModuleP { data, definitions }
    })
}

struct Parser<'input> {
    tokens: &'input mut TokenStream,
    source_file: &'input SourceFileIdentifier,
}

impl<'input> Parser<'input> {
    /// Parses a single top-level item.
    /// This can be either a function or a data type.
    fn parse_item(&mut self) -> DiagnosticResult<ItemP> {
        // An item starts with an optional visibility declaration.
        let vis = self.parse_visibility();

        // Then we require either the keyword `data` or `fn`.
        let item_type = self.parse_token(|ty| matches!(ty, TokenType::Data | TokenType::Def));

        vis.bind(|vis| {
            if let Some(item_type) = item_type {
                match item_type.token_type {
                    TokenType::Data => dbg!(self.parse_data(vis).map(ItemP::Data)),
                    TokenType::Def => self.parse_def(vis).map(ItemP::Definition),
                    _ => unreachable!(),
                }
            } else {
                DiagnosticResult::fail(ErrorMessage::new(
                    "expected keyword `data` or `def`".to_string(),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &self.tokens.range()),
                ))
            }
        })
    }
}

/// A single `.quill` file is called a module. It may export data types and definitions.
/// This `Module` struct contains the parsed abstract syntax tree of a module.
#[derive(Debug)]
pub struct ModuleP {
    pub data: Vec<DataP>,
    pub definitions: Vec<DefinitionP>,
}

/// Any top level item such as a definition or theorem.
#[derive(Debug)]
enum ItemP {
    Data(DataP),
    Definition(DefinitionP),
}

////////////////////
//// DATA TYPES ////
////////////////////

/// A `data` block, used to define sum or product types.
#[derive(Debug)]
pub struct DataP {
    pub vis: Visibility,
    pub identifier: NameP,
    pub type_params: Vec<NameP>,
    pub type_ctors: Vec<TypeConstructorP>,
}

/// Represents a type constructor in a `data` block.
/// For example, `Just { value: T }`, where the `Just` is the `id`, and the `value` is the only element in `fields`.
#[derive(Debug)]
pub struct TypeConstructorP {
    pub vis: Visibility,
    pub name: NameP,
    pub fields: Vec<FieldP>,
}

#[derive(Debug)]
pub struct FieldP {
    pub name: NameP,
    pub ty: TypeP,
}

impl<'input> Parser<'input> {
    /// `data ::= identifier type_params? "=" type_ctors`
    fn parse_data(&mut self, vis: Visibility) -> DiagnosticResult<DataP> {
        self.parse_name_with_message("expected a name for this new data type")
            .bind(|identifier| {
                // We now need the list of named type parameters.
                let type_params = if let Some(tree) = self.parse_tree(BracketType::Square) {
                    self.parse_in_tree(tree, |parser| parser.parse_named_type_params())
                } else {
                    DiagnosticResult::ok(Vec::new())
                };

                type_params.bind(|type_params| {
                    // We now need an `=` symbol, then a series of type constructors separated by `|` symbols.
                    let assign_symbol = self.require_token(
                        |ty| matches!(ty, TokenType::Assign),
                        "expected assign symbol",
                    );
                    assign_symbol.bind(|_| {
                        let type_ctors = self.parse_type_ctors();
                        type_ctors.map(|type_ctors| DataP {
                            vis,
                            identifier,
                            type_params,
                            type_ctors,
                        })
                    })
                })
            })
    }
}

/////////////////////////////////////
//// DEFINITIONS AND EXPRESSIONS ////
/////////////////////////////////////

/// A `def` block. Defines a symbol's type and what values it takes under what circumstances.
#[derive(Debug)]
pub struct DefinitionP {
    pub identifier: IdentifierP,
    pub quantifiers: Vec<IdentifierP>,
    pub symbol_type: TypeP,
    pub cases: Vec<DefinitionCaseP>,
}

/// Represents a case in a definition where we can replace the left hand side of a pattern with the right hand side.
#[derive(Debug)]
pub struct DefinitionCaseP {
    pub pattern: ExprPatP,
    pub replacement: ExprPatP,
}

/// Represents either an expression or a pattern.
#[derive(Debug)]
pub enum ExprPatP {
    /// A named variable e.g. `x` or `+`.
    Variable(IdentifierP),
    /// Apply the left hand side to the right hand side, e.g. `a b`.
    /// More complicated expressions e.g. `a b c d` can be desugared into `((a b) c) d`.
    Apply(Box<ExprPatP>, Box<ExprPatP>),
    /// A lambda abstraction, specifically `lambda params -> expr`.
    Lambda {
        lambda_token: Range,
        params: Vec<IdentifierP>,
        expr: Box<ExprPatP>,
    },
    /// A let expression, specifically `let identifier = left_expr; right_expr`.
    Let {
        let_token: Range,
        identifier: IdentifierP,
        left_expr: Box<ExprPatP>,
        right_expr: Box<ExprPatP>,
    },
    /// An underscore `_` representing an unknown.
    /// This is valid only in patterns, not normal expressions.
    Unknown(Range),
}

impl Ranged for ExprPatP {
    fn range(&self) -> Range {
        match self {
            ExprPatP::Variable(identifier) => identifier.range(),
            ExprPatP::Apply(left, right) => left.range().union(right.range()),
            ExprPatP::Unknown(range) => *range,
            ExprPatP::Lambda {
                lambda_token, expr, ..
            } => lambda_token.union(expr.range()),
            ExprPatP::Let {
                let_token,
                right_expr,
                ..
            } => let_token.union(right_expr.range()),
        }
    }
}

impl<'input> Parser<'input> {
    fn parse_def(&mut self, vis: Visibility) -> DiagnosticResult<DefinitionP> {
        DiagnosticResult::fail(ErrorMessage::new(
            "test".to_string(),
            Severity::Error,
            Diagnostic::at(self.source_file, &self.tokens.range()),
        ))
    }

    /// `type_ctors ::= type_ctor ("|" type_ctors)?`
    fn parse_type_ctors(&mut self) -> DiagnosticResult<Vec<TypeConstructorP>> {
        self.parse_type_ctor().bind(|type_ctor| {
            if self
                .parse_token(|ty| matches!(ty, TokenType::TypeOr))
                .is_some()
            {
                // We have another type to parse.
                self.parse_type_ctors().map(|mut remaining_type_ctors| {
                    remaining_type_ctors.insert(0, type_ctor);
                    remaining_type_ctors
                })
            } else {
                DiagnosticResult::ok(vec![type_ctor])
            }
        })
    }

    /// `type_ctor ::= visibility? name '{' type_ctor_body '}'`
    fn parse_type_ctor(&mut self) -> DiagnosticResult<TypeConstructorP> {
        self.parse_visibility().bind(|vis| {
            self.parse_name().bind(|name| {
                if let Some(tree) = self.parse_tree(BracketType::Brace) {
                    self.parse_in_tree(tree, |parser| parser.parse_type_ctor_body())
                        .map(|fields| TypeConstructorP { vis, name, fields })
                } else {
                    DiagnosticResult::fail(ErrorMessage::new(
                        "expected brace brackets".to_string(),
                        Severity::Error,
                        Diagnostic::at(self.source_file, &self.tokens.range()),
                    ))
                }
            })
        })
    }

    /// `type_ctor_body ::= (field (',' type_ctor_body)?)?`
    fn parse_type_ctor_body(&mut self) -> DiagnosticResult<Vec<FieldP>> {
        if let Some(token) = self.parse_token(|ty| matches!(ty, TokenType::Identifier(_))) {
            if let TokenType::Identifier(name) = token.token_type {
                self.parse_field(NameP {
                    name,
                    range: token.range,
                })
                .bind(|field| {
                    if self
                        .parse_token(|ty| matches!(ty, TokenType::Comma))
                        .is_some()
                    {
                        self.parse_type_ctor_body().map(|mut remaining_body| {
                            remaining_body.insert(0, field);
                            remaining_body
                        })
                    } else {
                        DiagnosticResult::ok(vec![field])
                    }
                })
            } else {
                unreachable!()
            }
        } else {
            DiagnosticResult::ok(Vec::new())
        }
    }

    /// `field ::= name ':' type`
    /// The name will have already been parsed; it is supplied to this function as a parameter.
    fn parse_field(&mut self, name: NameP) -> DiagnosticResult<FieldP> {
        self.require_token(|ty| matches!(ty, TokenType::Type), "expected colon")
            .bind(|_| self.parse_type().map(|ty| FieldP { name, ty }))
    }
}

///////////////
//// TYPES ////
///////////////

#[derive(Debug)]
pub enum TypeP {
    /// An explicitly named type possibly with type parameters, e.g. `Bool` or `Either[T, U]`.
    Named {
        identifier: IdentifierP,
        params: Vec<TypeP>,
    },
    /// A function `a -> b`.
    /// Functions with more arguments, e.g. `a -> b -> c` are represented as
    /// curried functions, e.g. `a -> (b -> c)`.
    Function(Box<TypeP>, Box<TypeP>),
}

impl Ranged for TypeP {
    fn range(&self) -> Range {
        match self {
            TypeP::Named {
                identifier,
                params: args,
            } => args
                .iter()
                .fold(identifier.range(), |acc, i| acc.union(i.range())),
            TypeP::Function(left, right) => left.range().union(right.range()),
        }
    }
}

impl<'input> Parser<'input> {
    /// `type ::= (type_name type_args | "(" type ")") ("->" type)?`
    fn parse_type(&mut self) -> DiagnosticResult<TypeP> {
        let initial_type = match self.tokens.peek() {
            Some(TokenTree::Tree { .. }) => {
                if let TokenTree::Tree(tree) = self.tokens.next().unwrap() {
                    // This is either a parenthesised type, or a list/array type (a type surrounded with square brackets).
                    match tree.bracket_type {
                        BracketType::Parentheses => {
                            // This is a parenthesised type.
                            self.parse_in_tree(tree, |inner| inner.parse_type())
                        }
                        BracketType::Square => {
                            // TODO This is a list/array type.
                            // Currently, these are not implemented.
                            DiagnosticResult::fail(ErrorMessage::new(
                                "expected a type, but found a square bracket".to_string(),
                                Severity::Error,
                                Diagnostic::at(self.source_file, &tree.range()),
                            ))
                        }
                        BracketType::Brace => DiagnosticResult::fail(ErrorMessage::new(
                            "expected a type, but found a brace bracket".to_string(),
                            Severity::Error,
                            Diagnostic::at(self.source_file, &tree.range()),
                        )),
                    }
                } else {
                    unreachable!()
                }
            }
            _ => {
                self.parse_identifier().bind(|identifier| {
                    // If we have a square bracket token tree, they are type parameters.
                    if let Some(tree) = self.parse_tree(BracketType::Square) {
                        // Parse each type parameter inside this tree.
                        let type_parameters =
                            self.parse_in_tree(tree, |inner| inner.parse_type_params());
                        type_parameters.map(|params| TypeP::Named { identifier, params })
                    } else {
                        DiagnosticResult::ok(TypeP::Named {
                            identifier,
                            params: Vec::new(),
                        })
                    }
                })
            }
        };

        initial_type.bind(|parsed_type| {
            if self
                .parse_token(|ty| matches!(ty, TokenType::Arrow))
                .is_some()
            {
                self.parse_type()
                    .map(|rhs_type| TypeP::Function(Box::new(parsed_type), Box::new(rhs_type)))
            } else {
                DiagnosticResult::ok(parsed_type)
            }
        })
    }

    /// Parses a list of named type parameters, e.g. [A, B, C] but not something like [bool] because that is a type not a named type parameter.
    fn parse_named_type_params(&mut self) -> DiagnosticResult<Vec<NameP>> {
        self.parse_name().bind(|first_param| {
            if self
                .parse_token(|ty| matches!(ty, TokenType::Comma))
                .is_some()
            {
                self.parse_named_type_params().map(|mut remaining_params| {
                    remaining_params.insert(0, first_param);
                    remaining_params
                })
            } else {
                DiagnosticResult::ok(vec![first_param])
            }
        })
    }

    /// Parses a list of type parameters.
    fn parse_type_params(&mut self) -> DiagnosticResult<Vec<TypeP>> {
        self.parse_type().bind(|first_param| {
            if self
                .parse_token(|ty| matches!(ty, TokenType::Comma))
                .is_some()
            {
                self.parse_type_params().map(|mut remaining_params| {
                    remaining_params.insert(0, first_param);
                    remaining_params
                })
            } else {
                DiagnosticResult::ok(vec![first_param])
            }
        })
    }
}

/////////////////////////
//// OTHER UTILITIES ////
/////////////////////////

/// An unresolved identifier, which is a string of text at some range in code.
#[derive(Debug, Clone)]
pub struct IdentifierP {
    /// Must contain at least one segment.
    pub segments: Vec<NameP>,
}

impl Ranged for IdentifierP {
    fn range(&self) -> Range {
        self.segments
            .iter()
            .fold(self.segments[0].range, |range, segment| {
                range.union(segment.range)
            })
    }
}

/// A name for an item, which cannot be qualified.
#[derive(Debug, Clone)]
pub struct NameP {
    pub name: String,
    pub range: Range,
}

pub enum Visibility {
    Public(Range),
    Private,
}

impl Debug for Visibility {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Visibility::Public(_) => write!(f, "public"),
            Visibility::Private => write!(f, "private"),
        }
    }
}

impl<'input> Parser<'input> {
    fn parse_identifier(&mut self) -> DiagnosticResult<IdentifierP> {
        self.parse_name_with_message("expected identifier segment")
            .bind(|first_segment| {
                if self
                    .parse_token(|ty| matches!(ty, TokenType::Scope))
                    .is_some()
                {
                    self.parse_identifier().map(|mut remaining_segments| {
                        remaining_segments.segments.insert(0, first_segment);
                        remaining_segments
                    })
                } else {
                    DiagnosticResult::ok(IdentifierP {
                        segments: vec![first_segment],
                    })
                }
            })
    }

    fn parse_name(&mut self) -> DiagnosticResult<NameP> {
        self.parse_name_with_message("expected name")
    }

    /// Parses a name from the input stream. If the next token was not a name, this emits the given message.
    fn parse_name_with_message(&mut self, fail_message: &str) -> DiagnosticResult<NameP> {
        self.parse_token(|ty| matches!(ty, TokenType::Identifier(_)))
            .map(|token| {
                if let TokenType::Identifier(name) = token.token_type {
                    NameP {
                        name,
                        range: token.range,
                    }
                } else {
                    panic!("parse_token returned a token that was not a name");
                }
            })
            .ok_or_else(|| {
                ErrorMessage::new(
                    fail_message.to_string(),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &self.tokens.range()),
                )
            })
            .into()
    }

    /// A visibility declaration is either the keyword `pub`, or nothing at all.
    fn parse_visibility(&mut self) -> DiagnosticResult<Visibility> {
        DiagnosticResult::ok(
            if let Some(token) = self.parse_token(|ty| matches!(ty, TokenType::Pub)) {
                Visibility::Public(token.range)
            } else {
                Visibility::Private
            },
        )
    }

    fn require_token(
        &mut self,
        predicate: impl FnOnce(&TokenType) -> bool,
        fail_message: &str,
    ) -> DiagnosticResult<Token> {
        self.parse_token(predicate)
            .ok_or_else(|| {
                ErrorMessage::new(
                    fail_message.to_string(),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &self.tokens.range()),
                )
            })
            .into()
    }

    /// If the next token tree is a tree with this bracket type, return it.
    fn parse_tree(&mut self, bracket_type: BracketType) -> Option<Tree> {
        if let Some(TokenTree::Tree(tree)) = self.tokens.peek() {
            if tree.bracket_type == bracket_type {
                if let Some(TokenTree::Tree(tree)) = self.tokens.next() {
                    return Some(tree);
                } else {
                    panic!("peek and next did not match");
                }
            }
        }
        None
    }

    /// If the next token tree is a token matching this predicate, return it.
    fn parse_token(&mut self, predicate: impl FnOnce(&TokenType) -> bool) -> Option<Token> {
        if let Some(TokenTree::Token(token)) = self.tokens.peek() {
            if predicate(&token.token_type) {
                if let Some(TokenTree::Token(token)) = self.tokens.next() {
                    return Some(token);
                } else {
                    panic!("peek and next did not match");
                }
            }
        }
        None
    }

    /// Creates a parser for the same source file, but operating inside an inner token stream.
    /// Then, executes the given command inside the internal parser.
    /// After the command is done, this function then checks to make sure that the inner token stream's tokens are all consumed.
    /// If there were extra tokens, an error is emitted.
    fn parse_in_tree<T>(
        &self,
        tree: Tree,
        command: impl FnOnce(&mut Parser) -> DiagnosticResult<T>,
    ) -> DiagnosticResult<T> {
        let mut stream = TokenStream {
            iter: tree.tokens.into_iter().peekable(),
            last_location: tree.close.start,
        };
        let mut inner_parser = Parser {
            tokens: &mut stream,
            source_file: self.source_file,
        };
        let result = command(&mut inner_parser);
        result.bind(|result| {
            // Check to see if we've used up the whole token tree.
            if let Some(next_token) = stream.peek() {
                DiagnosticResult::ok_with(
                    result,
                    ErrorMessage::new(
                        "unexpected extra tokens".to_string(),
                        Severity::Error,
                        Diagnostic::at(self.source_file, &next_token.range()),
                    ),
                )
            } else {
                DiagnosticResult::ok(result)
            }
        })
    }
}

mod test {
    #[tokio::test]
    async fn test_parser() {
        use quill_common::location::SourceFileIdentifier;
        use quill_lexer::lex;
        use quill_source_file::ErrorEmitter;
        use quill_source_file::PackageFileSystem;
        use std::path::PathBuf;

        use crate::parse;

        let fs = PackageFileSystem::new(PathBuf::from("test"));
        let file_ident = SourceFileIdentifier {
            module: vec![].into(),
            file: "file".into(),
        };

        let lexed = lex(&fs, &file_ident).await;
        let parsed = lexed.bind(|lexed| parse(lexed, &file_ident));

        let mut error_emitter = ErrorEmitter::new(&fs);
        let parsed = error_emitter.consume_diagnostic(parsed);
        error_emitter.emit_all().await;

        // If the parse fails, the test will fail.
        let parsed = parsed.unwrap();

        println!("parsed: {:#?}", parsed);
    }
}
