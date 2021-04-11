# Parsing

The parsing phase converts a list of token trees (representing a source file) and identifies their structure. For example, it identifies top-level item declarations such as data types and definitions, and it also parses the contents of expressions. This phase creates an abstract syntax tree, with the `P` (for parsed) suffix on most data types. Identifiers are not resolved in this step.

## Items

The top level construct to be parsed is called an _item_. This is either a definition (created with the `def` keyword) or a type (created with the `data` or `enum` keywords). Every item has a _visibility_, which is either public or private. The parser operates by trying to parse items until the end of the file.

## `data` and `enum` blocks

A data block defines a product data type. An enum block defines a sum data type, represented as the sum of one or more variants. Each variant has the same syntax as a data block.
