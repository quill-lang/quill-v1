use print
use input
use list
use bool
use int
use option

def main: Unit {
    main = add_ints
}

def add_ints: Unit {
    add_ints = (
        // Print "Type two integers to add.\n"
        @perform_print_list print_list (84 :- 121 :- 112 :- 101 :- 32 :- 116 :- 119 :- 111 :- 32 :- 105 :- 110 :- 116 :- 101 :- 103 :- 101 :- 114 :- 115 :- 32 :- 116 :- 111 :- 32 :- 97 :- 100 :- 100 :- 46 :- 10 :- empty)
        match (get_int unit) (
            Some { value } -> match (get_int unit) (
                Some { value = value_2 } -> (
                    print_int (copy &value)
                    // " + "
                    putchar 32
                    putchar 43
                    putchar 32
                    print_int (copy &value_2)
                    // " = "
                    putchar 32
                    putchar 61
                    putchar 32
                    print_int (value + value_2)
                )
                // Print "Error"
                None {} -> @perform_print_list print_list (69 :- 114 :- 114 :- 111 :- 114 :- empty)
            )
            // Print "Error"
            None {} -> perform_print_list (69 :- 114 :- 114 :- 111 :- 114 :- empty)
        )
    )
}

def hello_world_factorials: Unit {
    hello_world_factorials = (
        // "Hello, world!" in Unicode code points is
        // 72 101 108 108 111 44 32 119 111 114 108 100 33
        if false (
            nop
        ) (
            \a -> (
                let list = 72 :- 101 :- 108 :- 108 :- 111 :- 44 :- 32 :- 119 :- 111 :- 114 :- 108 :- 100 :- 33 :- empty
                perform_print_list print_list (copy &list)
                perform_print_list (copy &print_list) (copied (as_ref &list))
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
