use std::collections::HashMap;

use lspower::lsp::*;
use quill_common::location::Ranged;

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

    fn gen(&mut self, file: quill_parser::FileP) {
        for def in file.definitions {
            self.push_token(
                def.name.range,
                SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::FUNCTION],
                0,
            );
            for param in def.type_parameters {
                self.gen_type_parameter(param);
            }
            self.gen_type(def.definition_type);
            match def.body {
                quill_parser::DefinitionBodyP::PatternMatch(pm) => {
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
                quill_parser::DefinitionBodyP::CompilerIntrinsic(range) => {
                    self.push_token(range, SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::MACRO], 0);
                }
            }
        }
    }

    fn gen_type_parameter(&mut self, param: quill_parser::TypeParameterP) {
        self.push_token(
            param.name.range,
            SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::TYPE_PARAMETER],
            0,
        );
    }

    fn gen_type(&mut self, ty: quill_parser::TypeP) {
        match ty {
            quill_parser::TypeP::Named { identifier, params } => {
                self.push_token(
                    identifier.range(),
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::TYPE],
                    0,
                );
                for param in params {
                    self.gen_type(param);
                }
            }
            quill_parser::TypeP::Function(l, r) => {
                self.gen_type(*l);
                self.gen_type(*r);
            }
            quill_parser::TypeP::Borrow { ty, .. } => {
                self.gen_type(*ty);
            }
        }
    }

    fn gen_expr(&mut self, expr: quill_parser::ExprPatP, conditions: SemanticExprConditions) {
        match expr {
            quill_parser::ExprPatP::Variable(variable) => {
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
            quill_parser::ExprPatP::Immediate { range, .. } => {
                self.push_token(range, SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::NUMBER], 0);
            }
            quill_parser::ExprPatP::Apply(l, r) => {
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
            quill_parser::ExprPatP::Lambda { params, expr, .. } => {
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
            quill_parser::ExprPatP::Let { name, expr, .. } => {
                self.push_token(
                    name.range,
                    SEMANTIC_TOKEN_LEGEND[&SemanticTokenType::VARIABLE],
                    0,
                );
                self.gen_expr(*expr, conditions);
            }
            quill_parser::ExprPatP::Block { statements, .. } => {
                for stmt in statements {
                    self.gen_expr(stmt, conditions.clone());
                }
            }
            quill_parser::ExprPatP::ConstructData {
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
            quill_parser::ExprPatP::Unknown(_) => {}
            quill_parser::ExprPatP::Borrow { expr, .. } => self.gen_expr(*expr, conditions),
            quill_parser::ExprPatP::Copy { expr, .. } => self.gen_expr(*expr, conditions),
        }
    }
}

/// `is_main_pattern` is true if this contains the function name.
fn get_named_parameters(pattern: &quill_parser::ExprPatP, is_main_pattern: bool) -> Vec<String> {
    match pattern {
        quill_parser::ExprPatP::Variable(variable) => {
            if variable.segments.len() == 1 {
                vec![variable.segments[0].name.clone()]
            } else {
                Vec::new()
            }
        }
        quill_parser::ExprPatP::Immediate { .. } => Vec::new(),
        quill_parser::ExprPatP::Apply(l, r) => {
            let mut result = get_named_parameters(&*l, is_main_pattern);
            result.extend(get_named_parameters(&*r, false));
            result
        }
        quill_parser::ExprPatP::Lambda { .. } => unreachable!(),
        quill_parser::ExprPatP::Let { .. } => unreachable!(),
        quill_parser::ExprPatP::Block { .. } => unreachable!(),
        quill_parser::ExprPatP::ConstructData { fields, .. } => {
            let mut result = Vec::new();
            for (_, pat) in &fields.fields {
                result.extend(get_named_parameters(pat, false));
            }
            for name in &fields.auto_fields {
                result.push(name.name.clone());
            }
            result
        }
        quill_parser::ExprPatP::Unknown(_) => Vec::new(),
        quill_parser::ExprPatP::Borrow { .. } => unreachable!(),
        quill_parser::ExprPatP::Copy { .. } => unreachable!(),
    }
}

pub fn create_semantic_tokens(parsed: quill_parser::FileP) -> Vec<SemanticToken> {
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
