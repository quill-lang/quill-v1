use list
use int

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
