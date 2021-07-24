def putchar: Int -> Unit { compiler_intrinsic }

aspect Container[T] {
    value: T
}

def get_value[T]: impl Container[T] -> T {
    get_value container = match container (
        impl { value } -> value
    )
}

def main: Unit {
    main = (
        putchar (get_value impl { value = 65 })
    )
}
