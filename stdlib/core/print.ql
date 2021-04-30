use list
use int
use bool

def putchar: Int -> Unit { compiler_intrinsic }

def newline: Unit -> Unit {
    newline _ = putchar 10
}

def print_list: List[Int] -> Unit {
    print_list Cons { value, list } = (
        putchar value
        print_list list
    )
    print_list _ = unit
}

def print_int: Int -> Unit {
    print_int n = if_lazy ((copy &n) >= 10) (print_int_large (copy &n)) (print_int_small n)
}

def print_int_large: Int -> Unit -> Unit {
    print_int_large n _ = (
        let quot = (copy &n) / 10
        let rem = n - (copy &quot) * 10
        print_int quot
        print_int_small rem unit
    )
}

def print_int_small: Int -> Unit -> Unit {
    print_int_small i _ = putchar (i + 48)
}
