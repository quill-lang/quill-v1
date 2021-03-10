# Keywords and Conventions

We define a number of useful keywords for the internals of the compiler to ensure consistency.

## Locations and Ranges

A _location_ is a zero-indexed line number and column number inside a source file. An empty file begins at location (0, 0). A _range_ is a pair of locations, the beginning and end of the range. The end location is _not included_ in the range, so a range starting at (3, 6) containing two characters would have end point (3, 8).

A _source file_ is a `.quill` file, containing Quill source code. Source files may be grouped into directories on disk, which are referred to as _modules_. A source file identifier is the combination of a module identifier (a list of module segments, which may be empty) and a file name (which does not include the `.quill` extension, as this is implicit).

## Names and Identifiers

We define a _name_ to be an unqualified name for a variable, data structure, function, or something like this. An _identifier_, on the other hand, is a potentially qualified name. While forming the HIR (described below), the compiler resolves identifiers into _qualified names_, which contain the exact path where a definition/function was defined.

## Diagnostics and Errors

A monadic diagnostic system is used, which allows for correct chaining of diagnostic messages combined with results (see the compiler source code for how diagnostic results are used in practise). A _diagnostic_ is the location where a message is emitted from, represented by a source file identifier and optionally a more specific range of characters inside the file. If a range is supplied to the diagnostic, then it will print this range of characters alongside the error message it emits. A _diagnostic result_ contains the result of a calculation (if it succeeded), along with a list of error messages to be emitted.

## Expressions

An _expression_ is the core building block of programs in Quill. It represents a computation that can be evaluated. An expression's _content_ is the actual code that makes up an expression. The content of an expression is a local variable, a block of code, a `let` statement, a `lambda` abstraction, or something similar. An expression has a _type_ associated with it.

## Types

A _type_ can be one of the following:

- a concrete type, such as `int` or `Either[int, bool]`, or
- a type variable, like `T` or `M[A]`, or
- a function, such as `int -> bool`.

Concrete types and type variables may take a number of _type parameters_. A _primitive type_ is a concrete type that is built in to the language (not the standard library), such as `unit` or `int`.

## Intermediate Representations

Quill code is translated through a number of different intermediate representations, or IRs, before being translated into machine code. The main stages, in order, are:

- HIR (high-level IR). In high-level IR, expression contents are known, but expression types are not. All references have already been resolved by this point, converting unqualified identifiers into qualified names.
- MIR (mid-level IR). At this stage, the types of each expression have been deduced. This IR still looks mostly like the structure of a Quill program you would write yourself. It is at this stage that borrow checking and move checking occurs.
- LIR (low-level IR). Explicit creation and deletion instructions have been now added to objects, and the control flow has been translated from a functional style into an imperative style. The main primitive is no longer the _expression_, but the _instruction_. Code is organised into blocks, which have jump conditions that describe how to jump between code blocks.
- LLVM IR (low-level IR). LIR is converted into LLVM's IR, which allows it to be compiled to machine code. It is at this stage that the compiler performs useful tasks such as monomorphisation and inlining.
