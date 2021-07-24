def putchar: Int -> Unit { compiler_intrinsic }

enum Option[T] = Some { value: T } | None {}

def unwrap_or[T]: Option[T] -> T -> T {
    unwrap_or opt other = match opt (
        Some { value } -> value
        None {} -> other
    )
}

def main: Unit {
    main = (
        putchar (unwrap_or Some { value = 65 } 66)
        putchar (unwrap_or None {} 66)
    )
}
