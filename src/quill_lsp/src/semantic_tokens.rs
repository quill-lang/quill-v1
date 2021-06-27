use std::collections::HashMap;

use lspower::lsp::*;
use quill_common::location::Ranged;
use quill_parser::{
    definition::{DefinitionBodyP, DefinitionP, TypeParameterP},
    expr_pat::ExprPatP,
    file::FileP,
    types::TypeP,
};

#[derive(Debug)]
struct RawSemanticToken {
    pub line: u32,
    pub col: u32,
    pub length: u32,
    pub token_type: u32,
    pub token_modifiers_bitset: u32,
}

struct SemanticTokenGenerator {
    tokens: Vec<RawSemanticToken>,
}

#[derive(Default, Clone)]
struct SemanticExprConditions {
    /// A list of all the known named parameters.
    parameters: Vec<String>,
    /// Is this expression a function or a function application?
    is_function: bool,
}

impl SemanticTokenGenerator {
    fn finish(mut self) -> Vec<SemanticToken> {
        self.tokens
            .sort_by(|l, r| u32::cmp(&l.line, &r.line).then(u32::cmp(&l.col, &r.col)));
        let mut result = Vec::new();
        let mut line = 0;
        let mut col = 0;
        for token in self.tokens {
            if line != token.line {
                col = 0;
            }
            result.push(SemanticToken {
                delta_line: token.line - line,
                delta_start: token.col - col,
                length: token.length,
                token_type: token.token_type,
                token_modifiers_bitset: token.token_modifiers_bitset,
            });
            line = token.line;
            col = token.col;
        }
        result
    }

    fn push_token(
        &mut self,
        range: quill_common::location::Range,
        token_type: u32,
        token_modifiers_bitset: u32,
    ) {
        for line in range.start.line..=range.end.line {
            let col = if line == range.start.line {
                range.start.col
            } else {
                0
            };
            let final_col = if line == range.end.line {
                range.end.col
            } else {
                10000
            };
            let length = final_col - col;

            self.tokens.push(RawSemanticToken {
                line,
                col,
                length,
                token_type,
                token_modifiers_bitset,
            });
        }
    }

    fn gen(&mut self, file: FileP) {
        for def in file.definitions {
            self.gen_def(def);
        }
    }

    fn gen_def(&mut self, def: DefinitionP) {
        self.push_token(
            def.decl.name.range,
            SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::FUNCTION],
            0,
        );
        for param in def.decl.type_parameters {
            self.gen_type_parameter(param);
        }
        self.gen_type(def.decl.definition_type);
        self.gen_def_body(def.body);
    }

    fn gen_def_body(&mut self, def_body: DefinitionBodyP) {
        match def_body {
            DefinitionBodyP::PatternMatch(pm) => {
                for case in pm {
                    let parameters = get_named_parameters(&case.pattern, true);
                    self.gen_expr(
                        case.pattern,
                        SemanticExprConditions {
                            is_function: true,
                            parameters: parameters.clone(),
                        },
                    );
                    self.gen_expr(
                        case.replacement,
                        SemanticExprConditions {
                            parameters,
                            ..Default::default()
                        },
                    );
                }
            }
            DefinitionBodyP::CompilerIntrinsic(range) => {
                self.push_token(range, SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::MACRO], 0);
            }
        }
    }

    fn gen_type_parameter(&mut self, param: TypeParameterP) {
        self.push_token(
            param.name.range,
            SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::TYPE_PARAMETER],
            0,
        );
    }

    fn gen_type(&mut self, ty: TypeP) {
        match ty {
            TypeP::Named { identifier, params } => {
                self.push_token(
                    identifier.range(),
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::TYPE],
                    0,
                );
                for param in params {
                    self.gen_type(param);
                }
            }
            TypeP::Function(l, r) => {
                self.gen_type(*l);
                self.gen_type(*r);
            }
            TypeP::Borrow { ty, .. } => {
                self.gen_type(*ty);
            }
            TypeP::Impl {
                impl_token,
                aspect,
                params,
            } => {
                self.push_token(
                    impl_token,
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::KEYWORD],
                    0,
                );
                self.push_token(
                    aspect.range(),
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::TYPE],
                    0,
                );
                for param in params {
                    self.gen_type(param);
                }
            }
        }
    }

    fn gen_expr(&mut self, expr: ExprPatP, conditions: SemanticExprConditions) {
        match expr {
            ExprPatP::Variable(variable) => {
                self.push_token(
                    variable.range(),
                    if conditions.is_function {
                        SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::FUNCTION]
                    } else if variable.segments.len() == 1
                        && conditions.parameters.contains(&variable.segments[0].name)
                    {
                        SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::PARAMETER]
                    } else if variable.segments.len() == 1
                        && variable.segments[0].name.chars().all(|ch| ch.is_numeric())
                    {
                        SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::NUMBER]
                    } else {
                        SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::VARIABLE]
                    },
                    0,
                );
            }
            ExprPatP::Immediate { range, .. } => {
                self.push_token(range, SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::NUMBER], 0);
            }
            ExprPatP::Apply(l, r) => {
                self.gen_expr(
                    *l,
                    SemanticExprConditions {
                        is_function: true,
                        ..conditions.clone()
                    },
                );
                self.gen_expr(
                    *r,
                    SemanticExprConditions {
                        is_function: false,
                        ..conditions
                    },
                );
            }
            ExprPatP::Lambda { params, expr, .. } => {
                let mut conditions = conditions;
                for param in params {
                    self.push_token(
                        param.range,
                        SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::PARAMETER],
                        0,
                    );
                    conditions.parameters.push(param.name);
                }
                self.gen_expr(*expr, conditions);
            }
            ExprPatP::Let { name, expr, .. } => {
                self.push_token(
                    name.range,
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::VARIABLE],
                    0,
                );
                self.gen_expr(*expr, conditions);
            }
            ExprPatP::Block { statements, .. } => {
                for stmt in statements {
                    self.gen_expr(stmt, conditions.clone());
                }
            }
            ExprPatP::ConstructData {
                data_constructor,
                fields,
                ..
            } => {
                self.push_token(
                    data_constructor.range(),
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::TYPE],
                    0,
                );
                for (name, pat) in fields.fields {
                    self.push_token(
                        name.range,
                        SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::PROPERTY],
                        0,
                    );
                    self.gen_expr(pat, conditions.clone());
                }
                for name in fields.auto_fields {
                    self.push_token(
                        name.range,
                        SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::PROPERTY],
                        0,
                    );
                }
            }
            ExprPatP::Unknown(_) => {}
            ExprPatP::Borrow { expr, .. } => self.gen_expr(*expr, conditions),
            ExprPatP::Copy { expr, .. } => self.gen_expr(*expr, conditions),
            ExprPatP::Impl { impl_token, body } => {
                self.push_token(
                    impl_token,
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::KEYWORD],
                    0,
                );
                self.gen_def_body(body);
            }
            ExprPatP::Field {
                container,
                field,
                dot,
            } => {
                self.gen_expr(*container, conditions);
                self.push_token(
                    field.range,
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::PROPERTY],
                    0,
                )
            }
        }
    }
}

/// `is_main_pattern` is true if this contains the function name.
fn get_named_parameters(pattern: &ExprPatP, is_main_pattern: bool) -> Vec<String> {
    match pattern {
        ExprPatP::Variable(variable) => {
            if variable.segments.len() == 1 {
                vec![variable.segments[0].name.clone()]
            } else {
                Vec::new()
            }
        }
        ExprPatP::Immediate { .. } => Vec::new(),
        ExprPatP::Apply(l, r) => {
            let mut result = get_named_parameters(&*l, is_main_pattern);
            result.extend(get_named_parameters(&*r, false));
            result
        }
        ExprPatP::Lambda { .. } => unreachable!(),
        ExprPatP::Let { .. } => unreachable!(),
        ExprPatP::Block { .. } => unreachable!(),
        ExprPatP::ConstructData { fields, .. } => {
            let mut result = Vec::new();
            for (_, pat) in &fields.fields {
                result.extend(get_named_parameters(pat, false));
            }
            for name in &fields.auto_fields {
                result.push(name.name.clone());
            }
            result
        }
        ExprPatP::Unknown(_) => Vec::new(),
        ExprPatP::Borrow { .. } => unreachable!(),
        ExprPatP::Copy { .. } => unreachable!(),
        ExprPatP::Impl { .. } => unreachable!(),
        ExprPatP::Field { .. } => unreachable!(),
    }
}

pub fn create_semantic_tokens(parsed: FileP) -> Vec<SemanticToken> {
    let mut gen = SemanticTokenGenerator { tokens: Vec::new() };
    gen.gen(parsed);
    gen.finish()
}

pub fn semantic_tokens_legend() -> SemanticTokensLegend {
    SemanticTokensLegend {
        token_types: SEMANTIC_TOKEN_LEGEND_VEC.clone(),
        token_modifiers: vec![SemanticTokenModifier::DEFINITION],
    }
}

lazy_static::lazy_static! {
    static ref SEMANTIC_TOKEN_LEGEND_VEC: Vec<SemanticTokenType> = {
        vec![
            SemanticTokenType::KEYWORD,
            SemanticTokenType::FUNCTION,
            SemanticTokenType::VARIABLE,
            SemanticTokenType::TYPE,
            SemanticTokenType::TYPE_PARAMETER,
            SemanticTokenType::MACRO,
            SemanticTokenType::PROPERTY,
            SemanticTokenType::PARAMETER,
            SemanticTokenType::NUMBER,
        ]
    };
    static ref SEMANTIC_TOKEN_LEGEND: HashMap<SemanticTokenType, u32> = {
        let mut m = HashMap::new();
        for (i, value) in SEMANTIC_TOKEN_LEGEND_VEC.iter().enumerate() {
            m.insert(value.clone(), i as u32);
        }
        m
    };
}
