use list

def putchar: int -> unit { compiler_intrinsic }

def print_list: List[int] -> unit {
    print_list Cons { value, list } = (
        putchar value
        print_list list
    )
    print_list _ = unit
}
