use std::{
    collections::HashMap,
    path::{Component, Path, PathBuf},
    sync::Arc,
};

use lspower::jsonrpc;
use lspower::lsp::*;
use lspower::{Client, LanguageServer, LspService, Server};
use multimap::MultiMap;
use quill_common::name::QualifiedName;
use quill_common::{diagnostic::DiagnosticResult, location::Ranged};
use quill_common::{
    diagnostic::{ErrorMessage, Severity},
    location::{ModuleIdentifier, SourceFileIdentifier, SourceFileType},
};
use quill_mir::ProjectMIR;
use quill_source_file::PackageFileSystem;
use quillc_api::ProjectInfo;
use tokio::sync::RwLock;
use tracing::{info, trace, Level};

/// Takes a relativised path and converts it to a source file identifier.
fn path_to_file(root_module: String, path: &Path) -> SourceFileIdentifier {
    let map = |component| match component {
        Component::Normal(component) => component.to_string_lossy().to_string(),
        _ => unreachable!(),
    };

    let ext = path.extension();
    let path = path.with_extension("");

    let mut components = path.components().collect::<Vec<_>>();
    let file = components.pop().unwrap();
    SourceFileIdentifier {
        module: ModuleIdentifier {
            segments: std::iter::once(root_module)
                .chain(components.into_iter().map(map))
                .map(|str| str.into())
                .collect(),
        },
        file: map(file).into(),
        file_type: if let Some(ext) = ext {
            let ext = ext.to_string_lossy().to_string();
            match ext.as_str() {
                "ql" => SourceFileType::Quill,
                "toml" => SourceFileType::Toml,
                _ => unreachable!("ext was {}", ext),
            }
        } else {
            unreachable!()
        },
    }
}

fn file_to_url(project_roots: &HashMap<String, PathBuf>, file: SourceFileIdentifier) -> Url {
    let mut iter = file
        .module
        .segments
        .into_iter()
        .chain(std::iter::once(file.file));
    let project = iter.next().unwrap().0;
    let project_root = project_roots[&project].clone();
    let segments = iter.map(|segment| segment.0);
    Url::from_file_path(
        segments
            .fold(project_root, |dir, segment| dir.join(segment))
            .with_extension(file.file_type.file_extension()),
    )
    .unwrap()
}

fn into_diagnostic(project_roots: &HashMap<String, PathBuf>, message: ErrorMessage) -> Diagnostic {
    let related_information = if message.help.is_empty() {
        None
    } else {
        Some(
            message
                .help
                .into_iter()
                .map(|help| DiagnosticRelatedInformation {
                    location: Location {
                        uri: file_to_url(project_roots, help.diagnostic.source_file),
                        range: help.diagnostic.range.map_or(
                            Range {
                                start: Position {
                                    line: 0,
                                    character: 0,
                                },
                                end: Position {
                                    line: 0,
                                    character: 0,
                                },
                            },
                            |range| Range {
                                start: Position {
                                    line: range.start.line,
                                    character: range.start.col,
                                },
                                end: Position {
                                    line: range.end.line,
                                    character: range.end.col,
                                },
                            },
                        ),
                    },
                    message: help.message,
                })
                .collect(),
        )
    };

    Diagnostic {
        range: message.diagnostic.range.map_or(
            Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: 0,
                    character: 0,
                },
            },
            |range| Range {
                start: Position {
                    line: range.start.line,
                    character: range.start.col,
                },
                end: Position {
                    line: range.end.line,
                    character: range.end.col,
                },
            },
        ),
        severity: Some(match message.severity {
            Severity::Error => DiagnosticSeverity::Error,
            Severity::Warning => DiagnosticSeverity::Warning,
        }),
        code: None,
        code_description: None,
        source: Some("quill_lsp".to_string()),
        message: message.message,
        related_information,
        tags: None,
        data: None,
    }
}

struct Backend {
    client: Client,
    /// A new file system is created for every potential root.
    root_file_systems: Arc<RwLock<RootFileSystems>>,
    /// Maps project roots to the files in which diagnostics were emitted.
    /// This allows us to clear the diagnostics before emitting more.
    emitted_diagnostics_to: Arc<RwLock<HashMap<PathBuf, Vec<SourceFileIdentifier>>>>,
}

struct ProjectRoot {
    dir: PathBuf,
    project_name: String,
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Self {
            client,
            root_file_systems: Arc::new(RwLock::new(RootFileSystems::default())),
            emitted_diagnostics_to: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Check whether the given URI is inside a Quill project.
    /// This function returns the project root folder, which can be used as a key
    /// in RootFileSystems, along with the identifier of the source file relative to
    /// the project root.
    ///
    /// In particular, this checks parent URIs until a `quill.toml` file is found.
    /// If one is found, then that directory is added to `RootFileSystems` as a file
    /// system root.
    pub async fn get_project_root(&self, url: Url) -> Option<(SourceFileIdentifier, ProjectRoot)> {
        assert!(url.scheme() == "file");
        let path = url.to_file_path().unwrap();

        // First, check if we've already loaded this project folder.
        {
            let read = self.root_file_systems.read().await;
            for (k, (root_module, _)) in &read.file_systems {
                if let Ok(relative) = path.strip_prefix(k) {
                    return Some((
                        path_to_file(root_module.clone(), relative),
                        ProjectRoot {
                            dir: k.clone(),
                            project_name: root_module.clone(),
                        },
                    ));
                }
            }
        }

        let mut new_path = path.clone();
        loop {
            if let Ok(file_bytes) = tokio::fs::read(new_path.join("quill.toml")).await {
                if let Ok(file_str) = std::str::from_utf8(&file_bytes) {
                    if let Ok(file_toml) = toml::from_str::<ProjectInfo>(file_str) {
                        let fs = PackageFileSystem::new({
                            let mut map = HashMap::new();
                            map.insert(file_toml.name.clone(), new_path.clone());
                            map
                        });
                        info!(
                            "found quill project '{}' at {}",
                            file_toml.name,
                            new_path.to_str().unwrap()
                        );
                        self.root_file_systems
                            .write()
                            .await
                            .file_systems
                            .insert(new_path.clone(), (file_toml.name.clone(), fs));
                        return Some((
                            path_to_file(
                                file_toml.name.clone(),
                                path.strip_prefix(&new_path).unwrap(),
                            ),
                            ProjectRoot {
                                dir: new_path,
                                project_name: file_toml.name,
                            },
                        ));
                    }
                }
            }

            if !new_path.pop() {
                return None;
            }
        }
    }

    async fn emit_project_diagnostics(
        &self,
        project_root: PathBuf,
        fs: &PackageFileSystem,
        messages: impl IntoIterator<Item = ErrorMessage>,
    ) {
        let diagnostics_by_file = messages
            .into_iter()
            .map(|message| (message.diagnostic.source_file.clone(), message))
            .collect::<MultiMap<_, _>>();

        let mut emitted = self.emitted_diagnostics_to.write().await;
        let emitted = emitted.entry(project_root).or_default();

        for file in emitted.iter() {
            self.client
                .publish_diagnostics(
                    file_to_url(&fs.project_directories, file.clone()),
                    vec![],
                    None,
                )
                .await;
        }

        emitted.clear();

        for (file, diagnostics) in diagnostics_by_file {
            emitted.push(file.clone());
            let diags = diagnostics
                .into_iter()
                .map(|message| into_diagnostic(&fs.project_directories, message))
                .collect();

            self.client
                .publish_diagnostics(file_to_url(&fs.project_directories, file), diags, None)
                .await;
        }
    }
}

/// Creates a PackageFileSystem for every Quill project we find.
#[derive(Default)]
struct RootFileSystems {
    /// Maps workspace roots to package file systems and the name of the package at that root.
    pub file_systems: HashMap<PathBuf, (String, PackageFileSystem)>,
}

#[lspower::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> jsonrpc::Result<InitializeResult> {
        let capabilities = ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::Full)),
            semantic_tokens_provider: Some(
                SemanticTokensServerCapabilities::SemanticTokensOptions(SemanticTokensOptions {
                    work_done_progress_options: WorkDoneProgressOptions {
                        work_done_progress: None,
                    },
                    legend: SemanticTokensLegend {
                        token_types: SEMANTIC_TOKEN_LEGEND_VEC.clone(),
                        token_modifiers: vec![SemanticTokenModifier::DEFINITION],
                    },
                    range: None,
                    full: Some(SemanticTokensFullOptions::Bool(true)),
                }),
            ),
            ..Default::default()
        };

        let server_info = ServerInfo {
            name: "quill-lsp".to_string(),
            version: None,
        };

        Ok(InitializeResult {
            capabilities,
            server_info: Some(server_info),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        info!("server initialized!");
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        info!("opened file");
        self.did_change(DidChangeTextDocumentParams {
            text_document: VersionedTextDocumentIdentifier {
                uri: params.text_document.uri,
                version: params.text_document.version,
            },
            content_changes: vec![TextDocumentContentChangeEvent {
                text: params.text_document.text,
                range: None,
                range_length: None,
            }],
        })
        .await;
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> jsonrpc::Result<Option<SemanticTokensResult>> {
        if let Some((identifier, project_root)) = self
            .get_project_root(params.text_document.uri.clone())
            .await
        {
            let guard = self.root_file_systems.read().await;
            let (_, fs) = &guard.file_systems[&project_root.dir];

            // Parse the file and emit semantic tokens based on the parse.
            let lexed = quill_lexer::lex(fs, &identifier).await;
            let parsed = lexed.bind(|lexed| quill_parser::parse(lexed, &identifier));
            let (parsed, _) = parsed.destructure();

            let tokens = if let Some(parsed) = parsed {
                create_semantic_tokens(parsed)
            } else {
                Vec::new()
            };

            let semantic_tokens = SemanticTokensResult::Tokens(SemanticTokens {
                result_id: None,
                data: tokens,
            });

            Ok(Some(semantic_tokens))
        } else {
            Ok(None)
        }
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // Since we're using full text document synchronisation, we can just get the first change and that will be the whole document.
        if let Some((identifier, project_root)) = self
            .get_project_root(params.text_document.uri.clone())
            .await
        {
            trace!(
                "file {} in {} changed",
                identifier,
                project_root.dir.to_string_lossy(),
            );
            let contents = params.content_changes[0].text.clone();
            let guard = self.root_file_systems.read().await;
            let (_, fs) = &guard.file_systems[&project_root.dir];
            fs.overwrite_source_file(identifier.clone(), contents).await;

            // Parse the file and emit diagnostics.
            let lexed = quill_lexer::lex(fs, &identifier).await;
            let parsed = lexed.bind(|lexed| quill_parser::parse(lexed, &identifier));
            let (_, messages) = parsed.destructure();

            let diags = messages
                .into_iter()
                .map(|message| into_diagnostic(&fs.project_directories, message))
                .collect();

            self.client
                .publish_diagnostics(params.text_document.uri, diags, None)
                .await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        info!("closed file");
        // Remove the cached entry from the file system so that it reads the truth
        // of the file from disk when it next needs to.
        if let Some((identifier, project_root)) =
            self.get_project_root(params.text_document.uri).await
        {
            self.root_file_systems.read().await.file_systems[&project_root.dir]
                .1
                .remove_cache(&identifier)
                .await;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        info!("saved file");

        if let Some((_file_ident, project_root)) =
            self.get_project_root(params.text_document.uri).await
        {
            // Create more detailed diagnostics by running the full Quill compiler
            // (at least, up to the MIR step) on this file's project root.
            let guard = self.root_file_systems.read().await;
            let fs = &guard.file_systems[&project_root.dir].1;

            // Find all the source files.
            let source_files = quill_source_file::find_all_source_files(
                ModuleIdentifier {
                    segments: vec![project_root.project_name.clone().into()],
                },
                &project_root.dir,
            )
            .await;

            let lexed = {
                let mut results = Vec::new();
                for file_ident in source_files.iter() {
                    results.push(
                        quill_lexer::lex(&fs, &file_ident)
                            .await
                            .map(|lexed| (file_ident.clone(), lexed)),
                    );
                }
                DiagnosticResult::sequence_unfail(results)
                    .map(|results| results.into_iter().collect::<HashMap<_, _>>())
                    .deny()
            };

            let parsed = lexed.bind(|lexed| {
                DiagnosticResult::sequence_unfail(lexed.into_iter().map(|(file, lexed)| {
                    quill_parser::parse(lexed, &file).map(|parsed| (file, parsed))
                }))
                .map(|results| results.into_iter().collect::<HashMap<_, _>>())
                .deny()
            });

            let mir = parsed
                .bind(|parsed| {
                    quill_index::index_project(&parsed).bind(|index| {
                        // Now that we have the index, run type deduction and MIR generation.
                        DiagnosticResult::sequence_unfail(parsed.into_iter().map(
                            |(file_ident, parsed)| {
                                quill_type_deduce::check(&file_ident, &index, parsed)
                                    .deny()
                                    .map(|typeck| quill_mir::to_mir(&index, typeck, &file_ident))
                                    .bind(|mir| quill_borrow_check::borrow_check(&file_ident, mir))
                                    .map(|mir| (file_ident, mir))
                            },
                        ))
                        .map(|results| results.into_iter().collect::<HashMap<_, _>>())
                        .deny()
                        .map(|result| (result, index))
                    })
                })
                .deny()
                .map(|(mir, index)| ProjectMIR {
                    files: mir,
                    entry_point: QualifiedName {
                        source_file: SourceFileIdentifier {
                            module: ModuleIdentifier {
                                segments: vec![project_root.project_name.clone().into()],
                            },
                            file: "main".to_string().into(),
                            file_type: SourceFileType::Quill,
                        },
                        name: "main".to_string(),
                        range: quill_common::location::Location { line: 0, col: 0 }.into(),
                    },
                    index,
                });

            let (_, messages) = mir.destructure();

            info!(
                "compiled {:?} with {} messages",
                source_files,
                messages.len()
            );

            self.emit_project_diagnostics(project_root.dir, fs, messages)
                .await;
        }
    }

    async fn shutdown(&self) -> jsonrpc::Result<()> {
        Ok(())
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

fn create_semantic_tokens(parsed: quill_parser::FileP) -> Vec<SemanticToken> {
    let mut gen = SemanticTokenGenerator { tokens: Vec::new() };
    gen.gen(parsed);
    gen.finish()
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    tracing_subscriber::fmt()
        .with_ansi(false)
        .with_writer(std::io::stderr)
        .with_max_level(Level::INFO)
        .with_env_filter("quill_lsp=trace,lspower=trace")
        .init();

    let (service, messages) = LspService::new(Backend::new);
    Server::new(stdin, stdout)
        .interleave(messages)
        .serve(service)
        .await;
}
