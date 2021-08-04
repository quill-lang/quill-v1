use quill_type::Type;

/// If this type is a function, and the first argument is an impl, remove it.
/// This operation is done recursively.
/// This allows us to type check function calls that are not performed explicitly.
pub fn remove_impls(ty: Type) -> Type {
    if let Type::Function(l, r) = ty {
        if let Type::Impl { .. } = &*l {
            remove_impls(*r)
        } else {
            Type::Function(l, r)
        }
    } else {
        ty
    }
}
