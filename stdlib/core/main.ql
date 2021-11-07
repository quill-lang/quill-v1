use print
use input
use list
use bool
use int
use option
use ops
use func
use convert

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
                    print " + "
                    print (copy &value_2)
                    print " = "
                    print (value + value_2)
                )
                None {} -> print "Error"
            )
            None {} -> print "Error"
        )
    )
}

def hello_world_factorials: Unit {
    hello_world_factorials = (
        if false (
            nop
        ) (
            \a -> (
                let list = "Hello, world!"
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
        (putchar <|| convert) 33
        (putchar <|| convert) 32
        (putchar <|| convert) 61
        (putchar <|| convert) 32
        print (factorial (copy &low))
        newline unit
        print_factorials (low + 1) high
    ))
}

def nop: Unit -> Unit {
    nop unit = unit
}
