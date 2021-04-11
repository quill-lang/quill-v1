# Compilation Passes

The Quill compiler runs a number of passes on input code to transform it into machine code. The passes are detailed below. If any pass fails (i.e. emits an unrecoverable error), then subsequent passes are not executed, and the compiler stops processing.
