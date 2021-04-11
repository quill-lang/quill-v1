# Indexing

The indexing phase collates all of the parsed files from the entire project and compiles top-level data declarations and definitions into an index. At this point, the types of definitions are deduced, but their contents are not considered. Similarly, the types of fields of data types are deduced. This phase is split into two halves.

First, the type _cache_ is created, which stores all type declarations. Each type declaration is cached as a qualified name.

Then, the type cache is used to resolve the types of all definitions and fields in data types. This yields the _project index_, which is a map from qualified names of types and definitions to the actual type or definition it references. Note that the types and definitions are stored in separate 'namespaces'; it is possible to give a type and a definition the same name without name collisions. Enum variants are also stored, mapping the names of enum variants to the enum type it constructs. This allows unqualified identifiers to be translated into fully qualified identifiers.
