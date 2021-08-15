use list
use int
use bool
use func
use iter

def putchar: Int -> Unit { compiler_intrinsic }

def newline: Unit -> Unit {
    newline _ = putchar 10
}

aspect Show[T] {
    show: T -> List[Int]
}

aspect Print[T] {
    print: T -> Unit
}

def default print_show[T]: impl Show[T] -> impl Print[T] {
    print_show impl { show } = impl {
        print val = for_each putchar (show val)
    }
}

def default show_list: impl Show[List[Int]] {
    show_list = impl {
        show = id
    }
}

def default show_int: impl Show[Int] {
    show_int = impl {
        show n = (
            let n2 = copy &n
            match ((copy &n) >= 10) (
                true -> (
                    let quot = (copy &n) / 10
                    let rem = n - (copy &quot) * 10
                    concat (show quot) (show rem)
                )
                false -> (n2 + 48) :- empty
            )
        )
    }
}
