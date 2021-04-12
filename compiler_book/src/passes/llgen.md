# LLVM IR Generation

Finally, we can produce LLVM IR, an IR which can be translated into an object file for many kinds of architectures.

## Representations

A _representation_ of a type is a way of encoding a value of that type into binary. A representation is defined recursively.

- The empty set \\( \varnothing \\) is a representation.
- The 'integer representation' \\( i_n \\) for \\( n \in \mathbb N, n > 0 \\) is a representation.
- The 'pointer representation' \\( p \\) is a representation.
- The set \\( \\{ (n_1, R_1), (n_2, R_2), \dots, (n_k, R_k) \\} \\) is a representation, where the \\( n_i \\) are names and the \\( R_i \\) are representations.

We say that a representation has _zero size_ if requires no bits of data to encode it in binary.

- \\( \varnothing \\) has zero size.
- \\( p \\) has non-zero size.
- \\( i_n \\) has non-zero size.
- The set \\( \\{ (n_1, R_1), (n_2, R_2), \dots, (n_k, R_k) \\} \\) has zero size if and only if all \\( R_i \\) have zero size.

In the compiler, if a type's representation has zero size, we sometimes say that the type has _no representation_.

## Primitive representations

In order to convert a program into LLVM IR, we need to compute a representation for every type in a program. Primitive types have pre-defined representations:

- `unit` \\( \to \varnothing \\)
- `int` \\( \to i_{64} \\)
