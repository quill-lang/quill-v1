//! This crate contains functions to pretty-print error messages to the console window.

use std::{
    collections::BTreeMap,
    fmt::{Debug, Display},
    ops::Range,
};

use ariadne::{Cache, Color, Label, Report, ReportKind, Source};
use quill_common::{
    diagnostic::{Diagnostic, ErrorMessage, HelpType, Severity},
    location::{Location, SourceFileIdentifier},
};
use quill_source_file::PackageFileSystem;

/// Prints error and warning messages, outputting the relevant lines of source code from the input files.
pub struct ErrorEmitter<'fs> {
    fs: &'fs PackageFileSystem,
}

struct PackageFileSystemCache<'fs> {
    fs: &'fs PackageFileSystem,
    /// The string value is an error.
    cache: BTreeMap<SourceFileIdentifier, Result<Source, String>>,
}

impl Cache<SourceFileIdentifier> for PackageFileSystemCache<'_> {
    fn fetch(&mut self, id: &SourceFileIdentifier) -> Result<&Source, Box<dyn Debug + '_>> {
        let fs = self.fs;
        let entry = self.cache.entry(id.clone()).or_insert_with_key(|id| {
            fs.with_source_file(id, |file| match file {
                Ok(source) => Ok(Source::from(source.get_contents().to_string())),
                Err(err) => Err(format!("{:?}", err)),
            })
        });

        match entry {
            Ok(source) => Ok(source),
            Err(err) => Err(Box::new(err)),
        }
    }

    fn display<'a>(&self, id: &'a SourceFileIdentifier) -> Option<Box<dyn Display + 'a>> {
        Some(Box::new(id))
    }
}

/// Returns the character offset for the given location in the string.
fn location_to_character(s: &str, loc: Location) -> usize {
    // Don't really care about speed since this is the slow path anyway.
    // We're printing fancy messages with no regard for efficiency.
    let source = Source::from(s.to_string());
    let line = source.lines().nth(loc.line as usize).unwrap();
    line.offset() + loc.col as usize
}

impl<'fs> ErrorEmitter<'fs> {
    pub fn new(fs: &'fs PackageFileSystem) -> Self {
        Self { fs }
    }

    /// Emits the given message to the screen.
    pub fn emit(&self, message: ErrorMessage) {
        let diagnostic_to_span = |diagnostic: Diagnostic| {
            (
                diagnostic.source_file.clone(),
                if let Some(range) = diagnostic.range {
                    self.fs
                        .with_source_file(&diagnostic.source_file, |source| match source {
                            Ok(source) => {
                                // Convert the line:column range into a character offset range.
                                location_to_character(source.get_contents(), range.start)
                                    ..location_to_character(source.get_contents(), range.end)
                            }
                            Err(_) => 0..1,
                        })
                } else {
                    0..1
                },
            )
        };

        let span = diagnostic_to_span(message.diagnostic.clone());
        let mut builder = Report::<(SourceFileIdentifier, Range<usize>)>::build(
            match message.severity {
                Severity::Error => ReportKind::Error,
                Severity::Warning => ReportKind::Warning,
            },
            message.diagnostic.source_file,
            span.1.start,
        )
        .with_label(
            Label::new(span)
                .with_message(message.message)
                .with_priority(10)
                .with_color(match message.severity {
                    Severity::Error => Color::Red,
                    Severity::Warning => Color::Yellow,
                }),
        );

        let mut other_builders = Vec::new();
        for help in message.help {
            match help.help_type {
                HelpType::Help => {
                    let span = diagnostic_to_span(help.diagnostic.clone());
                    let builder = Report::<(SourceFileIdentifier, Range<usize>)>::build(
                        ReportKind::Advice,
                        help.diagnostic.source_file,
                        span.1.start,
                    )
                    .with_label(
                        Label::new(span)
                            .with_message(help.message)
                            .with_priority(10)
                            // This is the "advice" colour used by ariadne.
                            .with_color(Color::Fixed(147)),
                    );
                    other_builders.push(builder);
                }
                HelpType::Note => {
                    builder = builder.with_label(
                        Label::new(diagnostic_to_span(help.diagnostic))
                            .with_message(help.message)
                            .with_color(Color::Cyan),
                    );
                }
            }
        }

        builder
            .finish()
            .eprint(PackageFileSystemCache {
                fs: self.fs,
                cache: BTreeMap::new(),
            })
            .unwrap();
        for builder in other_builders {
            builder
                .finish()
                .eprint(PackageFileSystemCache {
                    fs: self.fs,
                    cache: BTreeMap::new(),
                })
                .unwrap();
        }
    }
}
