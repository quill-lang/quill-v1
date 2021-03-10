//! The borrow checker takes in expressions, and outputs MIR, the mid-level intermediate representation.
//! The MIR is an expression-oriented IR, where the type and borrow status of every object is known.
//! This IR form is a good place to perform optimisations.
