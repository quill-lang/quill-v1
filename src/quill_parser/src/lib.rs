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
) -> DiagnosticResult<FileP> {
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
        FileP { data, definitions }
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
        let item_type = self.parse_token_maybe(|ty| matches!(ty, TokenType::Data | TokenType::Def));

        vis.bind(|vis| {
            if let Some(item_type) = item_type {
                match item_type.token_type {
                    TokenType::Data => self.parse_data(vis).map(ItemP::Data),
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

/// A single `.quill` file may export data types and definitions.
/// This `File` struct contains the parsed abstract syntax tree of a file.
#[derive(Debug)]
pub struct FileP {
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
    pub type_params: Vec<TypeParameterP>,
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
                let named_type_params = if let Some(tree) = self.parse_tree(BracketType::Square) {
                    self.parse_in_tree(tree, |parser| parser.parse_type_param_names())
                } else {
                    DiagnosticResult::ok(Vec::new())
                };

                named_type_params.bind(|type_params| {
                    // We now need an `=` symbol, then a series of type constructors separated by `|` symbols.
                    let assign_symbol = self.parse_token(
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

    /// `type_ctors ::= type_ctor ("|" type_ctors)?`
    fn parse_type_ctors(&mut self) -> DiagnosticResult<Vec<TypeConstructorP>> {
        self.parse_type_ctor().bind(|type_ctor| {
            if self
                .parse_token_maybe(|ty| matches!(ty, TokenType::TypeOr))
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
        if let Some(token) = self.parse_token_maybe(|ty| matches!(ty, TokenType::Identifier(_))) {
            if let TokenType::Identifier(name) = token.token_type {
                self.parse_field(NameP {
                    name,
                    range: token.range,
                })
                .bind(|field| {
                    if self
                        .parse_token_maybe(|ty| matches!(ty, TokenType::Comma))
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
        self.parse_token(|ty| matches!(ty, TokenType::Type), "expected colon")
            .bind(|_| self.parse_type().map(|ty| FieldP { name, ty }))
    }
}

/////////////////////////////////////
//// DEFINITIONS AND EXPRESSIONS ////
/////////////////////////////////////

/// A `def` block. Defines a symbol's type and what values it takes under what circumstances.
#[derive(Debug)]
pub struct DefinitionP {
    pub vis: Visibility,
    pub name: NameP,
    /// This definition might be defined with certain quantified type variables, e.g. foo[A, B].
    pub type_parameters: Vec<TypeParameterP>,
    pub definition_type: TypeP,
    pub cases: Vec<DefinitionCaseP>,
}

#[derive(Debug, Clone)]
pub struct TypeParameterP {
    pub name: NameP,
    /// A type variable may have one or more unnamed parameters, e.g. `F[_]` is a common type for a functor.
    /// This field stores how many such parameters the type variable has.
    pub parameters: u32,
}

/// Represents a case in a definition where we can replace the left hand side of a pattern with the right hand side.
#[derive(Debug)]
pub struct DefinitionCaseP {
    pub pattern: ExprPatP,
    pub replacement: ExprPatP,
}

impl<'input> Parser<'input> {
    /// `def ::= name named_type_params? ':' ty '{' def_body '}'
    fn parse_def(&mut self, vis: Visibility) -> DiagnosticResult<DefinitionP> {
        self.parse_name().bind(|name| {
            let quantifiers = if let Some(tree) = self.parse_tree(BracketType::Square) {
                self.parse_in_tree(tree, |parser| parser.parse_type_param_names())
            } else {
                DiagnosticResult::ok(Vec::new())
            };
            quantifiers.bind(|quantifiers| {
                self.parse_token(|ty| matches!(ty, TokenType::Type), "expected colon")
                    .bind(|_| {
                        self.parse_type().bind(|definition_type| {
                            if let Some(tree) = self.parse_tree(BracketType::Brace) {
                                let cases =
                                    self.parse_in_tree(tree, |parser| parser.parse_def_body());
                                cases.map(|cases| DefinitionP {
                                    vis,
                                    name,
                                    type_parameters: quantifiers,
                                    definition_type,
                                    cases,
                                })
                            } else {
                                DiagnosticResult::fail(ErrorMessage::new(
                                    "expected brace bracket block".to_string(),
                                    Severity::Error,
                                    Diagnostic::at(self.source_file, &self.tokens.range()),
                                ))
                            }
                        })
                    })
            })
        })
    }

    /// `def_body ::= def_case (',' def_body?)?`
    fn parse_def_body(&mut self) -> DiagnosticResult<Vec<DefinitionCaseP>> {
        self.parse_def_case().bind(|first_case| {
            if self
                .parse_token_maybe(|ty| matches!(ty, TokenType::Comma))
                .is_some()
            {
                if self.tokens.peek().is_some() {
                    self.parse_def_body().map(|mut remaining_body| {
                        remaining_body.insert(0, first_case);
                        remaining_body
                    })
                } else {
                    DiagnosticResult::ok(vec![first_case])
                }
            } else {
                DiagnosticResult::ok(vec![first_case])
            }
        })
    }

    /// `def_case ::= pattern -> expression`
    fn parse_def_case(&mut self) -> DiagnosticResult<DefinitionCaseP> {
        self.parse_expr().bind(|pattern| {
            self.parse_token(|ty| matches!(ty, TokenType::Arrow), "expected arrow")
                .bind(|_| {
                    self.parse_expr().map(|replacement| DefinitionCaseP {
                        pattern,
                        replacement,
                    })
                })
        })
    }
}

///////////////
//// TYPES ////
///////////////

#[derive(Debug)]
pub enum TypeP {
    /// An explicitly named type possibly with type parameters, e.g. `Bool`, `Either[T, U]` or `Foo[T[_]]`.
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
                .parse_token_maybe(|ty| matches!(ty, TokenType::Arrow))
                .is_some()
            {
                self.parse_type()
                    .map(|rhs_type| TypeP::Function(Box::new(parsed_type), Box::new(rhs_type)))
            } else {
                DiagnosticResult::ok(parsed_type)
            }
        })
    }

    /// Parses a list of names for type parameters, e.g. [A, B, C[_]] but not something like [bool] because that is a type not a type parameter name.
    fn parse_type_param_names(&mut self) -> DiagnosticResult<Vec<TypeParameterP>> {
        self.parse_name().bind(|first_param| {
            // Check if this is a higher-kinded type, i.e. we have parameters for this type variable.
            let type_parameters = if let Some(tree) = self.parse_tree(BracketType::Square) {
                self.parse_in_tree(tree, |parser| parser.parse_type_param_params())
            } else {
                DiagnosticResult::ok(0)
            };

            type_parameters.bind(|type_parameters| {
                let first_param = TypeParameterP {
                    name: first_param,
                    parameters: type_parameters,
                };

                if self
                    .parse_token_maybe(|ty| matches!(ty, TokenType::Comma))
                    .is_some()
                {
                    self.parse_type_param_names().map(|mut remaining_params| {
                        remaining_params.insert(0, first_param);
                        remaining_params
                    })
                } else {
                    DiagnosticResult::ok(vec![first_param])
                }
            })
        })
    }

    /// Parse a list of underscores. This amount of underscores is the amount of unnamed type parameters in this higher kinded type.
    /// We are never going to need to nest deeper than higher-kinded types of order 1.
    /// In other words, `F[_]` is valid, but `F[_[_]]` will never be valid.
    /// Therefore, we don't need to use any kind of recursion into parsing higher and higher kinded types.
    fn parse_type_param_params(&mut self) -> DiagnosticResult<u32> {
        self.parse_token(
            |ty| matches!(ty, TokenType::Underscore),
            "expected underscore in higher kinded type parameter",
        )
        .bind(|_| {
            if self
                .parse_token_maybe(|ty| matches!(ty, TokenType::Comma))
                .is_some()
            {
                self.parse_type_param_params().map(|value| value + 1)
            } else {
                DiagnosticResult::ok(1)
            }
        })
    }

    /// Parses a list of type parameters, e.g. [bool, T].
    fn parse_type_params(&mut self) -> DiagnosticResult<Vec<TypeP>> {
        self.parse_type().bind(|first_param| {
            if self
                .parse_token_maybe(|ty| matches!(ty, TokenType::Comma))
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

//////////////////////////////////
//// EXPRESSIONS AND PATTERNS ////
//////////////////////////////////

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
        params: Vec<NameP>,
        expr: Box<ExprPatP>,
    },
    /// A let statement, specifically `let identifier = left_expr;`.
    /// This kind of statement is only valid as an intermediate statement in a block.
    Let {
        let_token: Range,
        name: NameP,
        expr: Box<ExprPatP>,
    },
    /// A block of statements, inside parentheses, separated by semicolons,
    /// where the final expression in the block is the type of the block as a whole.
    /// If a semicolon is included as the last token in the block, the block implicitly returns the unit type instead;
    /// in this case, the `final_semicolon` variable contains this semicolon and the block's return type is considered to just be unit.
    Block {
        open_bracket: Range,
        close_bracket: Range,
        statements: Vec<ExprPatP>,
        final_semicolon: Option<Range>,
    },
    /// The name of a data type, followed by brace brackets containing the data structure's fields.
    ConstructData {
        data_constructor: IdentifierP,
        open_brace: Range,
        close_brace: Range,
        fields: ConstructDataFields,
    },
    /// An underscore `_` representing an unknown.
    /// This is valid only in patterns, not normal expressions.
    Unknown(Range),
}

#[derive(Debug)]
pub struct ConstructDataFields {
    /// Fields that have been assigned values, e.g. `foo = 1`.
    fields: Vec<(NameP, ExprPatP)>,
    /// Fields that have not been assigned values (so will inherit their value from the local variable with that name), e.g. `foo`.
    /// This is useful in patterns, where fields are often not assigned different names.
    auto_fields: Vec<NameP>,
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
                let_token, expr, ..
            } => let_token.union(expr.range()),
            ExprPatP::Block {
                open_bracket,
                close_bracket,
                ..
            } => open_bracket.union(*close_bracket),
            ExprPatP::ConstructData {
                data_constructor,
                close_brace,
                ..
            } => data_constructor.range().union(close_brace.range()),
        }
    }
}

/// An internal structure used when parsing expression blocks.
struct ExprBlockBody {
    statements: Vec<ExprPatP>,
    final_semicolon: Option<Range>,
}

impl<'input> Parser<'input> {
    /// Expressions may contain `_` tokens, which represent data that we don't care about.
    /// We will evaluate patterns and normal expressions differently in a later parse step.
    fn parse_expr(&mut self) -> DiagnosticResult<ExprPatP> {
        // Check what kind of expression this is.
        // - variable: one term
        // - application: many terms, the leftmost one is considered a function applied to terms on the right
        // - abstraction: a lambda abstraction beginning with the `\` lambda symbol
        // - let: a `let` statement
        // - block: a block of statements followed by a returned value
        // Any expressions we add to the language in the future must reduce to one of these basic
        // expression types, so that we can apply a Hindley-Milner-like type system solver.
        if let Some(tk) = self.parse_token_maybe(|ty| matches!(ty, TokenType::Lambda)) {
            // This is a lambda expression.
            self.parse_expr_lambda(tk.range)
        } else if let Some(tk) = self.parse_token_maybe(|ty| matches!(ty, TokenType::Let)) {
            // This is a let statement.
            self.parse_expr_let(tk.range)
        } else {
            // Default to a variable or application expression, since this will show a decent error message.
            self.parse_expr_app()
        }
    }

    /// Parses a variable or application expression.
    fn parse_expr_app(&mut self) -> DiagnosticResult<ExprPatP> {
        let mut terms = Vec::new();
        while let Some(next_term) = self.parse_expr_term() {
            terms.push(next_term);
        }

        if terms.is_empty() {
            return DiagnosticResult::fail(ErrorMessage::new(
                String::from("expected expression"),
                Severity::Error,
                Diagnostic::at(self.source_file, &self.tokens.range()),
            ));
        }

        DiagnosticResult::sequence(terms).map(|terms| {
            let mut terms = terms.into_iter();
            let first = terms.next().unwrap();
            terms
                .into_iter()
                .fold(first, |acc, i| ExprPatP::Apply(Box::new(acc), Box::new(i)))
        })
    }

    /// Parses a lambda expression.
    fn parse_expr_lambda(&mut self, lambda_token: Range) -> DiagnosticResult<ExprPatP> {
        let mut params = Vec::new();
        while let Some(token) = self.parse_token_maybe(|ty| matches!(ty, TokenType::Identifier(_)))
        {
            if let TokenType::Identifier(name) = token.token_type {
                params.push(NameP {
                    name,
                    range: token.range,
                });
            } else {
                unreachable!()
            }
        }

        self.parse_token(|ty| matches!(ty, TokenType::Arrow), "expected arrow symbol")
            .bind(|_| {
                self.parse_expr().map(|expr| ExprPatP::Lambda {
                    lambda_token,
                    params,
                    expr: Box::new(expr),
                })
            })
    }

    /// Parses a let expression.
    /// `expr_let ::= name '=' expr ';'`
    fn parse_expr_let(&mut self, let_token: Range) -> DiagnosticResult<ExprPatP> {
        self.parse_name().bind(|name| {
            self.parse_token(
                |ty| matches!(ty, TokenType::Assign),
                "expected assign symbol",
            )
            .bind(|_| {
                self.parse_expr().map(|expr| ExprPatP::Let {
                    let_token,
                    name,
                    expr: Box::new(expr),
                })
            })
        })
    }

    /// Parses a single term from an expression by consuming either zero or one token trees from the input.
    /// If the following token did not constitute an expression, nothing is consumed.
    fn parse_expr_term(&mut self) -> Option<DiagnosticResult<ExprPatP>> {
        if let Some(tree) = self.parse_tree(BracketType::Parentheses) {
            // This is a block, containing statements followed by a final expression.
            let open_bracket = tree.open;
            let close_bracket = tree.close;
            Some(
                self.parse_in_tree(tree, |parser| parser.parse_expr_block_body())
                    .map(|expr_block_body| ExprPatP::Block {
                        open_bracket,
                        close_bracket,
                        statements: expr_block_body.statements,
                        final_semicolon: expr_block_body.final_semicolon,
                    }),
            )
        } else if let Some(token) = self.parse_token_maybe(|ty| matches!(ty, TokenType::Underscore))
        {
            // This is an unknown in a pattern.
            Some(DiagnosticResult::ok(ExprPatP::Unknown(token.range)))
        } else if let Some(identifier) = self.parse_identifier_maybe() {
            // If this is followed by a brace bracket, we are trying to construct an instance of a data type.
            if let Some(tree) = self.parse_tree(BracketType::Brace) {
                // We are constructing a data type.
                Some(identifier.bind(|identifier| {
                    let open_brace = tree.open;
                    let close_brace = tree.close;
                    self.parse_in_tree(tree, |parser| parser.parse_construct_data_body())
                        .map(|fields| ExprPatP::ConstructData {
                            data_constructor: identifier,
                            open_brace,
                            close_brace,
                            fields,
                        })
                }))
            } else {
                Some(identifier.map(ExprPatP::Variable))
            }
        } else {
            None
        }
    }

    /// `expr_block_body ::= expr (';' expr_block_body?)?`
    fn parse_expr_block_body(&mut self) -> DiagnosticResult<ExprBlockBody> {
        self.parse_expr().bind(|expr| {
            // Is the next token a semicolon?
            if let Some(semicolon) = self.parse_token_maybe(|ty| matches!(ty, TokenType::Semicolon))
            {
                // We have a semicolon, so potentially there's another expression/statement in the block left to parse.
                if self.tokens.peek().is_some() {
                    // There are more expressions to consider.
                    self.parse_expr_block_body().map(|mut remaining_body| {
                        remaining_body.statements.insert(0, expr);
                        remaining_body
                    })
                } else {
                    // This is the final semicolon, and the end of this expression block.
                    DiagnosticResult::ok(ExprBlockBody {
                        statements: vec![expr],
                        final_semicolon: Some(semicolon.range),
                    })
                }
            } else {
                // This is the end of this expression block, and there was no final semicolon.
                DiagnosticResult::ok(ExprBlockBody {
                    statements: vec![expr],
                    final_semicolon: None,
                })
            }
        })
    }

    /// `construct_data_body = name ('=' expr)? (',' expr_block_body?)?`
    fn parse_construct_data_body(&mut self) -> DiagnosticResult<ConstructDataFields> {
        self.parse_name().bind(|field_name| {
            let value = if self
                .parse_token_maybe(|ty| matches!(ty, TokenType::Assign))
                .is_some()
            {
                // We're assigning an expression to this field.
                self.parse_expr().map(Some)
            } else {
                DiagnosticResult::ok(None)
            };

            value.bind(|value| {
                if self
                    .parse_token_maybe(|ty| matches!(ty, TokenType::Comma))
                    .is_some()
                {
                    // We might have more of the body to parse.
                    if self.tokens.peek().is_some() {
                        // There is more of the body to parse.
                        self.parse_construct_data_body().map(|mut remaining_body| {
                            if let Some(value) = value {
                                remaining_body.fields.insert(0, (field_name, value));
                            } else {
                                remaining_body.auto_fields.insert(0, field_name);
                            }
                            remaining_body
                        })
                    } else {
                        // That's the end of the body.
                        if let Some(value) = value {
                            DiagnosticResult::ok(ConstructDataFields {
                                fields: vec![(field_name, value)],
                                auto_fields: Vec::new(),
                            })
                        } else {
                            DiagnosticResult::ok(ConstructDataFields {
                                fields: Vec::new(),
                                auto_fields: vec![field_name],
                            })
                        }
                    }
                } else {
                    // That's the end of the body.
                    if let Some(value) = value {
                        DiagnosticResult::ok(ConstructDataFields {
                            fields: vec![(field_name, value)],
                            auto_fields: Vec::new(),
                        })
                    } else {
                        DiagnosticResult::ok(ConstructDataFields {
                            fields: Vec::new(),
                            auto_fields: vec![field_name],
                        })
                    }
                }
            })
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
    /// Parses an identifier if the next token is an identifier fragment.
    fn parse_identifier_maybe(&mut self) -> Option<DiagnosticResult<IdentifierP>> {
        if let Some(TokenTree::Token(token)) = self.tokens.peek() {
            if let TokenType::Identifier(_) = token.token_type {
                // This should be an identifier.
                Some(self.parse_identifier())
            } else {
                None
            }
        } else {
            None
        }
    }

    fn parse_identifier(&mut self) -> DiagnosticResult<IdentifierP> {
        self.parse_name_with_message("expected identifier segment")
            .bind(|first_segment| {
                if self
                    .parse_token_maybe(|ty| matches!(ty, TokenType::Scope))
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
        self.parse_token_maybe(|ty| matches!(ty, TokenType::Identifier(_)))
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
            if let Some(token) = self.parse_token_maybe(|ty| matches!(ty, TokenType::Pub)) {
                Visibility::Public(token.range)
            } else {
                Visibility::Private
            },
        )
    }

    fn parse_token(
        &mut self,
        predicate: impl FnOnce(&TokenType) -> bool,
        fail_message: &str,
    ) -> DiagnosticResult<Token> {
        self.parse_token_maybe(predicate)
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
    fn parse_token_maybe(&mut self, predicate: impl FnOnce(&TokenType) -> bool) -> Option<Token> {
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
                        "did not understand this extra data".to_string(),
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
