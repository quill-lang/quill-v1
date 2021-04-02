//! Inside the compiler, types may have certain suffixes to declare what information they contain and where they should be used:
//! - `P`: just been Parsed, no extra information has been deduced.
//!   No type has been deduced, and no effort has been made to ensure syntactic correctness
//!   past the (lenient) parser.
//! - `C`: an intermediate data Cache, used when we're still in the middle of computing the index.
//!   After the index has been computed, we should not need to use `P` or `C` data,
//!   only `I` data should be required. This type suffix is *internal to the `quill_index` crate*.
//! - `I`: an Index entry for the item.
//! - `T`: currently being type checked.
//! - `M`: part of the MIR intermediate representation.
//! - (no suffix): types have been deduced and references have been resolved.

fn main() {}
