# Quill Compiler Project

The Quill compiler's internals are documented here in this book. This is not intended as a programmer's guide to learning the language, but rather a guide to the internals of the compiler itself.

## Goals

The project aims to create a programming language which is expressive, safe, and fast (in that order). We accomplish these goals through various means. The language is designed to be expression-oriented, making expressions (rather than statements) the core structural primitive of the language. This lends the language to more of a functional programming style than an imperative programming style. This is augmented with a higher-kinded type system that allows for rich abstractions. To ensure safety, we use a Rust-style borrow system that ensures that all references to data are valid, and that data is deleted once it is no longer required. This allows us to avoid the necessity of a garbage collector, which has become a staple in most modern functional programming languages. Finally, the language is compiled down into LLVM which is then translated into machine code for any given architecture, which allows the language to be fast.
