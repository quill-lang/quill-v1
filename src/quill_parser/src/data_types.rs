use crate::{definition::TypeParameterP, identifier::NameP, types::TypeP, visibility::Visibility};

/// A `data` block, used to define product types.
#[derive(Debug)]
pub struct DataP {
    pub vis: Visibility,
    pub identifier: NameP,
    pub type_params: Vec<TypeParameterP>,
    pub type_ctor: TypeConstructorP,
}

/// Represents a type constructor in a `data` block.
/// For example, `Just { value: T }`, where the `Just` is the `id`, and the `value` is the only element in `fields`.
#[derive(Debug)]
pub struct TypeConstructorP {
    pub fields: Vec<FieldP>,
}

#[derive(Debug)]
pub struct FieldP {
    pub name: NameP,
    pub ty: TypeP,
}

/// An `enum` block, used to define sum types.
/// This kind of block allows you to associate arbitrary other types together into a single type.
/// Any data type can be used inside an enum, even one used in a completely different enum.
#[derive(Debug)]
pub struct EnumP {
    pub vis: Visibility,
    pub identifier: NameP,
    pub type_params: Vec<TypeParameterP>,
    /// Has size 1 or larger.
    pub alternatives: Vec<EnumVariantP>,
}

#[derive(Debug)]
pub struct EnumVariantP {
    pub name: NameP,
    pub type_ctor: TypeConstructorP,
}
