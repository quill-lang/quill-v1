def putchar: Int -> Unit { compiler_intrinsic }

enum Bool2 = True {} | False {}

def invert: Bool2 -> Bool2 {
    invert b = match b (
        True {} -> False {}
        False {} -> True {}
    )
}

def main: Unit {
    main = match (invert True {}) (
        False {} -> putchar 65
        True {} -> putchar 66
    )
}
