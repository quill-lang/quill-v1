aspect Convert[From, To] {
    convert: From -> To
}

def int_to_char_intrinsic: Int -> Char { compiler_intrinsic }
def char_to_int_intrinsic: Char -> Int { compiler_intrinsic }

def default int_to_char: impl Convert[Int, Char] {
    int_to_char = impl {
        convert = int_to_char_intrinsic
    }
}

def default char_to_int: impl Convert[Char, Int] {
    char_to_int = impl {
        convert = char_to_int_intrinsic
    }
}
