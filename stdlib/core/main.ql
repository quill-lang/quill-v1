use print
use list
use bool
use int

def main: Unit {
    main = (
        // "Hello, world!" in Unicode code points is
        // 72 101 108 108 111 44 32 119 111 114 108 100 33
        if_lazy false (
            nop
        ) (
            \a -> print_list (72 :- 101 :- 108 :- 108 :- 111 :- 44 :- 32 :- 119 :- 111 :- 114 :- 108 :- 100 :- 33 :- empty)
        )
        newline unit

        print_factorials 0 20
    )
}

def print_factorials: Int -> Int -> Unit {
    print_factorials low high = if_lazy ((copy &low) > (copy &high)) nop (\a -> print_factorials_inner low high a)
}

def nop: Unit -> Unit {
    nop unit = unit
}

def print_factorials_inner: Int -> Int -> Unit -> Unit {
    print_factorials_inner low high _ = (
        print_int (copy &low)
        putchar 33
        putchar 32
        putchar 61
        putchar 32
        print_int (factorial (copy &low))
        newline unit
        print_factorials (low + 1) high
    )
}
