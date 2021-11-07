use list
use int
use bool
use func
use iter
use ops
use convert

def putchar: Char -> Unit { compiler_intrinsic }

def newline: Unit -> Unit {
    newline _ = putchar (convert 10)
}

aspect Show[T] {
    show: T -> List[Char]
}

aspect Print[T] {
    print: T -> Unit
}

def default print_show[T]: impl Show[T] -> impl Print[T] {
    print_show impl { show } = impl {
        print val = for_each putchar (show val)
    }
}

def default show_list_char: impl Show[List[Char]] {
    show_list_char = impl {
        show = id
    }
}

def default show_int: impl Show[Int] {
    show_int = impl {
        show n = (
            match ((copy &n) >= 10) (
                true -> (
                    let quot = (copy &n) / 10
                    let rem = n - (copy &quot) * 10
                    concat (show quot) (show rem)
                )
                false -> (convert (n + 48)) :- empty
            )
        )
    }
}
