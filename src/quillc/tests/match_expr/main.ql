def putchar: Int -> Unit { compiler_intrinsic }

def invert: Bool -> Bool {
    invert b = match b (
        true -> false
        false -> true
    )
}

def main: Unit {
    main = match (invert true) (
        false -> putchar 65
        true -> putchar 66
    )
}
