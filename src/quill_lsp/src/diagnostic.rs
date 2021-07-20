use std::{collections::BTreeMap, path::PathBuf};

use lspower::lsp::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location, Position, Range,
};
use quill_common::diagnostic::{ErrorMessage, Severity};

use crate::path::file_to_url;

pub fn into_diagnostic(
    project_roots: &BTreeMap<String, PathBuf>,
    message: ErrorMessage,
) -> Diagnostic {
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
