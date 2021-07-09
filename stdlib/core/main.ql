use print
use list
use bool
use int

def main: Unit {
    main = (
        // "Hello, world!" in Unicode code points is
        // 72 101 108 108 111 44 32 119 111 114 108 100 33
        if false (
            nop
        ) (
            \a -> (
                let list = 72 :- 101 :- 108 :- 108 :- 111 :- 44 :- 32 :- 119 :- 111 :- 114 :- 108 :- 100 :- 33 :- empty
                mapM putchar (copy &list)
                perform_print_list print_list (copy &list)
                // TODO: borrowing `print_list` directly doesn't work
                let print_list_2 = print_list
                perform_print_list (copy &print_list_2) list
            )
        )
        newline unit

        print_factorials 0 20
    )
}

def print_factorials: Int -> Int -> Unit {
    print_factorials low high = if ((copy &low) > (copy &high)) (
        nop
    ) (\a -> (
        print_int (copy &low)
        putchar 33
        putchar 32
        putchar 61
        putchar 32
        print_int (factorial (copy &low))
        newline unit
        print_factorials (low + 1) high
    ))
}

def nop: Unit -> Unit {
    nop unit = unit
}

// A very specific implementation of a monadic mapM function, to map a function over a list.
def mapM: (Int -> Unit) -> List[Int] -> Unit {
    mapM f Cons { value, list } = ((copy &f) value, mapM f list)
    mapM f Empty {} = unit
}
