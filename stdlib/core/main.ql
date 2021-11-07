use print
use input
use list
use bool
use int
use option
use ops

def main: Unit {
    main = add_ints unit
}

def add_ints: Unit -> Unit {
    add_ints unit = (
        print "Type two integers to add.\n"
        match (get_int unit) (
            Some { value } -> match (get_int unit) (
                Some { value = value_2 } -> (
                    print (copy &value)
                    // " + "
                    putchar ' '
                    putchar '+'
                    putchar ' '
                    print (copy &value_2)
                    // " = "
                    putchar 32
                    putchar 61
                    putchar 32
                    print (value + value_2)
                )
                // Print "Error"
                None {} -> print (69 :- 114 :- 114 :- 111 :- 114 :- empty)
            )
            // Print "Error"
            None {} -> print (69 :- 114 :- 114 :- 111 :- 114 :- empty)
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
                @print print_show (copy &list)
                @print (copy &print_show) (copied (as_ref &list))
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
        print (copy &low)
        putchar 33
        putchar 32
        putchar 61
        putchar 32
        print (factorial (copy &low))
        newline unit
        print_factorials (low + 1) high
    ))
}

def nop: Unit -> Unit {
    nop unit = unit
}
