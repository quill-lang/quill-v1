# Lexing (`quill_lexer`)

The lexing phase is the first pass. It takes an input string of code, and converts it into a stream of individual tokens, which after that point may not be separated. It assigns each token a _type_, such as `Assign` (`=`) or `Arrow` (`->`).

This is implemented as an LL(1) parser on a stream of Unicode code points. In particular, the input string is partitioned into lines, which are individually tokenised. To tokenise a single line of code, whitespace is skipped, and then the next code point is peeked at. Depending on the type of this code point (symbolic, alphanumeric, or a bracket), the tokeniser will greedily consume more code points according to a given predicate. In particular,

- brackets `[](){}` are always single character tokens
- control characters are always invalid, and emit an error
- if the code point is a `/`, the tokeniser looks ahead one code point; if this is also a `/` then the remainder of this line is considered a comment line and discarded
- for alphanumeric characters (those in the `Alphabetic`, `Nd`, `Nl` and `No` Unicode categories), more alphanumeric characters and the `_` character are consumed
- for any other character, non-alphanumeric, non-whitespace, non-bracket characters are consumed

If the token is not a bracket, a comment line, it is first Unicode normalised (according to the NFC convention). Then, a check is performed to see if this token is a reserved keyword. If it is not a reserved keyword, it is an identifier. The list of reserved keywords can be found in the lexer's source code in the `token_type_alphabetic` and `token_type_symbol` functions.

Note that as this tokenisation is happening, the lexer keeps track of the range that each token occupies inside the file.

Then, the lexer pairs up opening and closing brackets of each type, grouping the contents of each bracketed block into a _token tree_. If brackets could not be paired, an error message is emitted. The lexer then returns the list of token trees it has lexed. The entire file is not considered to be a single token tree, rather it is a list of token trees.
