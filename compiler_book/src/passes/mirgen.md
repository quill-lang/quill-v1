# MIR Generation

This step generates the MIR from the HIR. MIR is a mid-level intermediate representation. Creation and destruction of objects is made explicit. MIR contains polymorphic code that is stack/heap agnostic. Monomorphisation and data representation deduction occur later. This step handles definitions only, and does not operate on types.

## Type variables

A definition in MIR contains a list of type variables. These type parameters have a name, e.g. `T`, and might be _higher-kinded_. A higher-kinded type is a type variable that takes one or more parameters. For instance, `M[_]` is a higher-kinded type with one parameter.

## Arity and return type

A definition's _arity_ is the amount of parameters that must be supplied in order to execute the definition body. The _return type_ of the definition is the type that results from applying a number of arguments equal to its arity to the function. For instance, if we defined a function

```
def foo: int -> int -> int {
    foo a b = a
}
```

then the arity would be two, the arguments would have types `[int, int]` and the return type would be `int`. If instead we defined it as

```
def foo: int -> int -> int {
    foo a = \b -> a
}
```

then the arity would be one, the argument would have type `int` and the return type would be `int -> int`.

## Definition body

The body of a definition is composed of a set of _basic blocks_. A basic block has an ID and contains zero or more _statements_. Statements are simple structures such as creating and destroying data, or calling a function. Control flow is linear inside a basic block. Basic blocks end with a _terminator_, which governs what happens once the basic block finishes.

## Local variables and places

Certain statements will retrieve values from, or assign values to, local variables. A local variable is simply a container that can hold a single value of a certain (fixed) type. Local variables are always in static single assignment (SSA) form; they are assigned a value a maximum of once, and then that value may be retrieved later. Intermediate values of expressions are also local variables. The arguments to a function are also considered to be local variables. In order to manipulate a value, it must first be made into a local variable. For instance, to call a function, the function must first be instantiated into a local variable.

A _place_ is a local variable along with a _projection_ which allows us to index inside this local variable into deeper and deeper nested places. For instance, suppose we define a data type

```
data Foo { value: Bar }
```

Then, if `foo` is a local variable, `foo.value` is a place inside `foo`, accessible through the projection `.place`. Projections can also be made for enum values, e.g. `foo.<Bar>.baz` references the field `baz` of the variant `Bar` of the local variable `foo`. Note that when accessing an enum field through a projection, no check is made to see whether the enum really has the given variant.
