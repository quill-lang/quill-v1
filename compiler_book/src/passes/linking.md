# Linking

We invoke LLVM's linker `lld` to combine the object files into a single executable, and to link statically with the C standard library. This allows us to use common, optimised functions such as `malloc`.
