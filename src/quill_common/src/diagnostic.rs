use std::iter::FromIterator;

use crate::location::{Location, Range, Ranged, SourceFileIdentifier};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Diagnostic {
    pub source_file: SourceFileIdentifier,
    /// If the location is not specified, then the diagnostic refers to the entire file.
    pub range: Option<Range>,
}

impl Diagnostic {
    pub fn in_file(source_file: &SourceFileIdentifier) -> Self {
        Self {
            source_file: source_file.clone(),
            range: None,
        }
    }

    pub fn at_location(source_file: &SourceFileIdentifier, location: Location) -> Self {
        Self {
            source_file: source_file.clone(),
            range: Some(location.into()),
        }
    }

    pub fn at(source_file: &SourceFileIdentifier, range: &impl Ranged) -> Self {
        Self {
            source_file: source_file.clone(),
            range: Some(range.range()),
        }
    }
}

/// <https://rustc-dev-guide.rust-lang.org/diagnostics.html#diagnostic-levels>
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum HelpType {
    Help,
    Note,
}

/// Represents an error/warning/lint message displayed to the user.
#[derive(Debug, Serialize, Deserialize)]
pub struct ErrorMessage {
    pub message: String,
    pub severity: Severity,
    pub diagnostic: Diagnostic,
    pub help: Vec<HelpMessage>,
}

/// TODO: consider <https://doc.rust-lang.org/nightly/nightly-rustc/rustc_errors/enum.Applicability.html>
#[derive(Debug, Serialize, Deserialize)]
pub struct HelpMessage {
    pub message: String,
    pub help_type: HelpType,
    pub diagnostic: Diagnostic,
}

impl ErrorMessage {
    pub fn new(message: String, severity: Severity, diagnostic: Diagnostic) -> Self {
        Self {
            message,
            severity,
            diagnostic,
            help: Vec::new(),
        }
    }

    pub fn new_with(
        message: String,
        severity: Severity,
        diagnostic: Diagnostic,
        help: HelpMessage,
    ) -> Self {
        Self {
            message,
            severity,
            diagnostic,
            help: vec![help],
        }
    }

    pub fn new_with_many(
        message: String,
        severity: Severity,
        diagnostic: Diagnostic,
        help: Vec<HelpMessage>,
    ) -> Self {
        Self {
            message,
            severity,
            diagnostic,
            help,
        }
    }
}

/// Even if warnings or errors are emitted, we may still be able to continue parsing the code.
/// So we need some kind of result type that allows us to raise errors or other messages while still
/// retaining an 'Ok' state, as far as the rest of the code is aware.
///
/// Upon exiting the program, all error messages will be scanned to check the most severe error level.
/// If any errors exist, no warnings will be emitted.
#[derive(Debug)]
#[must_use = "errors must be processed by an ErrorEmitter"]
pub struct DiagnosticResult<T> {
    /// If this is `None`, then the computation failed. Error messages will be contained inside `messages.
    /// If this is `Some`, then the computation succeeded, but there may still be some messages (e.g. warnings
    /// or errors) inside `messages`.
    value: Option<T>,
    messages: Vec<ErrorMessage>,
}

impl<T> From<T> for DiagnosticResult<T> {
    fn from(value: T) -> Self {
        Self::ok(value)
    }
}

impl<T> From<Result<T, ErrorMessage>> for DiagnosticResult<T> {
    fn from(result: Result<T, ErrorMessage>) -> Self {
        match result {
            Ok(value) => Self::ok(value),
            Err(error) => Self::fail(error),
        }
    }
}

impl<T> From<Result<T, Vec<ErrorMessage>>> for DiagnosticResult<T> {
    fn from(result: Result<T, Vec<ErrorMessage>>) -> Self {
        match result {
            Ok(value) => Self::ok(value),
            Err(errors) => Self::fail_many(errors),
        }
    }
}

impl<T> DiagnosticResult<T> {
    /// The computation succeeded with no messages.
    /// This is the monadic `return` operation.
    pub fn ok(value: T) -> Self {
        Self {
            value: Some(value),
            messages: Vec::new(),
        }
    }

    /// The computation succeeded, but there was some error or warning message.
    pub fn ok_with(value: T, message: ErrorMessage) -> Self {
        Self {
            value: Some(value),
            messages: vec![message],
        }
    }

    pub fn ok_with_many(value: T, messages: Vec<ErrorMessage>) -> Self {
        Self {
            value: Some(value),
            messages,
        }
    }

    /// The computation failed. An error message is mandatory if the computation failed.
    pub fn fail(message: ErrorMessage) -> Self {
        assert!(message.severity == Severity::Error);
        Self {
            value: None,
            messages: vec![message],
        }
    }

    pub fn fail_many(messages: Vec<ErrorMessage>) -> Self {
        assert!(messages.iter().any(|m| m.severity == Severity::Error));
        Self {
            value: None,
            messages,
        }
    }

    /// Apply an infallible operation to the value inside this result. If the operation could fail, use [`DiagnosticResult::bind`] instead.
    pub fn map<F, U>(self, f: F) -> DiagnosticResult<U>
    where
        F: FnOnce(T) -> U,
    {
        match self.value {
            Some(value) => DiagnosticResult {
                value: Some(f(value)),
                messages: self.messages,
            },
            None => DiagnosticResult {
                value: None,
                messages: self.messages,
            },
        }
    }

    /// A monadic bind operation that consumes this diagnostic result and uses the value it contains, if it exists,
    /// to produce a new diagnostic result.
    pub fn bind<F, U>(mut self, f: F) -> DiagnosticResult<U>
    where
        F: FnOnce(T) -> DiagnosticResult<U>,
    {
        match self.value {
            Some(value) => {
                let mut result = f(value);
                self.messages.append(&mut result.messages);
                DiagnosticResult {
                    value: result.value,
                    messages: self.messages,
                }
            }
            None => DiagnosticResult {
                value: None,
                messages: self.messages,
            },
        }
    }

    /// Appends a message to this diagnostic result, regardless of whether the result succeeded or failed.
    pub fn with(mut self, message: ErrorMessage) -> Self {
        self.messages.push(message);
        self
    }

    /// Converts a failed diagnostic into a successful diagnostic by wrapping
    /// the contained value in an `Option`.
    pub fn unfail(self) -> DiagnosticResult<Option<T>> {
        DiagnosticResult {
            value: Some(self.value),
            messages: self.messages,
        }
    }

    /// Converts a successful diagnostic that had one or more `Error` messages into a failed diagnostic (with the same messages).
    /// Diagnostics without `Error` messages are unaffected.
    pub fn deny(self) -> Self {
        if self.messages.iter().any(|m| m.severity == Severity::Error) {
            Self {
                value: None,
                messages: self.messages,
            }
        } else {
            self
        }
    }

    /// Combines a list of diagnostic results into a single result by binding them all together.
    pub fn sequence(
        results: impl IntoIterator<Item = DiagnosticResult<T>>,
    ) -> DiagnosticResult<Vec<T>> {
        results
            .into_iter()
            .fold(DiagnosticResult::ok(Vec::new()), |acc, i| {
                acc.bind(|mut list| {
                    i.bind(|i| {
                        list.push(i);
                        DiagnosticResult::ok(list)
                    })
                })
            })
    }

    /// Combines a list of diagnostic results into a single result by binding them all together.
    /// Any failed diagnostics will be excluded from the output, but their error messages will remain.
    /// Therefore, this function will never fail - it might just produce an empty list as its output.
    pub fn sequence_unfail(
        results: impl IntoIterator<Item = DiagnosticResult<T>>,
    ) -> DiagnosticResult<Vec<T>> {
        results
            .into_iter()
            .fold(DiagnosticResult::ok(Vec::new()), |acc, i| {
                acc.bind(|mut list| {
                    i.unfail().bind(|i| {
                        if let Some(i) = i {
                            list.push(i);
                        }
                        DiagnosticResult::ok(list)
                    })
                })
            })
    }

    /// Returns true if the computation succeeded.
    pub fn succeeded(&self) -> bool {
        self.value.is_some()
    }

    /// Returns true if the computation failed.
    pub fn failed(&self) -> bool {
        self.value.is_none()
    }

    /// Splits up this diagnostic result into its value and its error messages.
    /// It is your responsibility to put these error messages back inside another diagnostic result.
    /// Failure to do so will result in errors not being displayed, or invalid programs erroneously
    /// being considered correct.
    pub fn destructure(self) -> (Option<T>, Vec<ErrorMessage>) {
        (self.value, self.messages)
    }

    /// Retrieves the value for inspection.
    pub fn value(&self) -> &Option<T> {
        &self.value
    }
}

impl<T> FromIterator<DiagnosticResult<T>> for DiagnosticResult<Vec<T>> {
    /// Any failed diagnostics will be excluded from the output, but their error messages will remain.
    /// Therefore, this function will never fail - it might just produce an empty list as its output.
    fn from_iter<U: IntoIterator<Item = DiagnosticResult<T>>>(iter: U) -> Self {
        DiagnosticResult::sequence_unfail(iter)
    }
}
