use std::ops::Deref;

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_index::ProjectIndex;
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

use crate::{
    definition::DefinitionTranslationContext,
    expr::ExprGeneratedM,
    mir::{
        BasicBlockId, LocalVariableInfo, LocalVariableName, Place, Rvalue, Statement, StatementKind,
    },
};

/// A definition that can be invoked to yield a default impl for an aspect.
struct DefaultImpl {
    def_name: QualifiedName,
    type_params: Vec<Type>,
    params: Vec<DefaultImpl>,
}

/// Given an expression (a function taking an impl), and an impl type (the parameter),
/// find a relevant default impl and apply it to the expression.
/// We insert instructions at the end of `coerce_block`.
pub(crate) fn find_and_apply_default_impl(
    ctx: &mut DefinitionTranslationContext,
    range: Range,
    name: &QualifiedName,
    parameters: Vec<Type>,
    expr: &ExprGeneratedM,
    coerce_block: BasicBlockId,
) -> DiagnosticResult<ExprGeneratedM> {
    find_default_impl(ctx.project_index, ctx.source_file, range, name, parameters)
        .map(|default_impl| apply_default_impl(ctx, coerce_block, range, expr, default_impl))
}

fn apply_default_impl(
    ctx: &mut DefinitionTranslationContext,
    coerce_block: BasicBlockId,
    range: Range,
    expr: &ExprGeneratedM,
    default_impl: DefaultImpl,
) -> ExprGeneratedM {
    let def = ctx.project_index.definition(&default_impl.def_name);

    let argument_type = replace_type_variables(
        def.symbol_type.clone(),
        &def.type_variables,
        &default_impl.type_params,
    );
    let return_type = if let Type::Function(_, r) = &ctx.locals[&expr.variable].ty {
        r.deref().clone()
    } else {
        unreachable!()
    };

    let impl_variable = ctx.new_local_variable(LocalVariableInfo {
        range,
        ty: argument_type.clone(),
        name: None,
    });

    let result_variable = ctx.new_local_variable(LocalVariableInfo {
        range,
        ty: return_type.clone(),
        name: None,
    });

    let statements = &mut ctx
        .control_flow_graph
        .basic_blocks
        .get_mut(&coerce_block)
        .unwrap()
        .statements;

    // Instance the impl.
    statements.push(Statement {
        range,
        kind: StatementKind::InstanceSymbol {
            name: default_impl.def_name,
            type_variables: default_impl.type_params,
            target: LocalVariableName::Local(impl_variable),
        },
    });

    // Apply the arguments.
    if !default_impl.params.is_empty() {
        todo!();
    }

    // Apply the impl to the expr.
    statements.push(Statement {
        range,
        kind: StatementKind::Apply {
            argument: Box::new(Rvalue::Move(Place::new(LocalVariableName::Local(
                impl_variable,
            )))),
            function: Box::new(Rvalue::Move(Place::new(expr.variable))),
            target: LocalVariableName::Local(result_variable),
            return_type,
            argument_type,
        },
    });

    // Now, return the resultant expression.
    ExprGeneratedM {
        block: expr.block,
        variable: LocalVariableName::Local(result_variable),
    }
}

/// Searches the project index for a default implementation of the following aspect.
fn find_default_impl(
    project_index: &ProjectIndex,
    source_file: &SourceFileIdentifier,
    range: Range,
    name: &QualifiedName,
    parameters: Vec<Type>,
) -> DiagnosticResult<DefaultImpl> {
    let impls = project_index.default_impls(name);
    // Scan this list of default impls to see if any of them can work with this set of parameters.
    let mut candidates = impls
        .iter()
        .filter_map(|def_name| {
            let def = project_index.definition(def_name);
            // Can this definition be used to create an impl of the required type?
            // First, check its result type.
            let mut result_ty = &def.symbol_type;
            while let Type::Function(_, r) = result_ty {
                result_ty = r.deref();
            }

            // TODO: For now, just assume that the impl definition is compatible,
            // and that it takes no arguments or type params.
            Some(DefaultImpl {
                def_name: def_name.clone(),
                type_params: Vec::new(),
                params: Vec::new(),
            })
        })
        .collect::<Vec<_>>();

    if candidates.is_empty() {
        DiagnosticResult::fail(ErrorMessage::new(
            format!(
                "did not find a default impl of type {}",
                Type::Impl {
                    name: name.clone(),
                    parameters
                }
            ),
            Severity::Error,
            Diagnostic::at(source_file, &range),
        ))
    } else if candidates.len() > 1 {
        DiagnosticResult::fail(ErrorMessage::new_with_many(
            format!(
                "found conflicting default impls of type {}",
                Type::Impl {
                    name: name.clone(),
                    parameters
                }
            ),
            Severity::Error,
            Diagnostic::at(source_file, &range),
            candidates
                .iter()
                .enumerate()
                .map(|(n, the_impl)| {
                    let def = project_index.definition(&the_impl.def_name);
                    HelpMessage {
                        message: format!("candidate #{}", n + 1),
                        help_type: HelpType::Note,
                        diagnostic: Diagnostic::at(&the_impl.def_name.source_file, &def.name.range),
                    }
                })
                .collect(),
        ))
    } else {
        candidates.pop().unwrap().into()
    }
}
