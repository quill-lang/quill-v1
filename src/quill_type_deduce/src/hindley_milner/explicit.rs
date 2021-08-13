use crate::hir::expr::TypeVariable;

/// If this type is a function, and the first argument is an impl, remove it.
/// This operation is done recursively.
/// This allows us to type check function calls that are not performed explicitly.
pub fn remove_impls_variable(mut ty: TypeVariable) -> TypeVariable {
    while let TypeVariable::Function(l, r) = ty {
        if let TypeVariable::Impl { .. } = &*l {
            ty = *r;
        } else {
            ty = TypeVariable::Function(l, r);
            break;
        }
    }
    ty
}
