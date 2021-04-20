use list
use int
use bool

def putchar: Int -> Unit { compiler_intrinsic }

def print_list: List[Int] -> Unit {
    print_list Cons { value, list } = (
        putchar value
        print_list list
    )
    print_list _ = unit
}

// Compiler bug: 0local not moved or dropped
// def print_int: int -> unit {
//     print_int n = unit
// }

def print_int: Int -> Unit {
    print_int n = if_lazy (ge_int 10 (copy &n)) (print_int_large (copy &n)) (print_int_small n)
}

def print_int_large: Int -> Unit -> Unit {
    print_int_large n _ = (
        let quot = div_int_unchecked (copy &n) 10
        let rem = sub_int_unchecked n (mul_int_unchecked (copy &quot) 10)
        print_int_large quot unit
        print_int_small rem unit
    )
}

def print_int_small: Int -> Unit -> Unit {
    print_int_small i _ = putchar (add_int_unchecked i 48)
}
