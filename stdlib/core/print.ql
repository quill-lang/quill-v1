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
    print_int n = (
        let n2 = copy &n
        if ((copy &n) >= 10) (\a -> (
            let quot = (copy &n) / 10
            let rem = n - (copy &quot) * 10
            print_int quot
            print_int rem
        )) (\a ->
            putchar (n2 + 48)
        )
    )
}
