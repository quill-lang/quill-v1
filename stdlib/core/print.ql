use list
use int
use bool

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

def show[T]: impl Show[T] -> T -> List[Int] {
    show impl { show } value = show value
}

// TODO: Automatically generate this function,
// perhaps by using a keyword like "export"?
// `export f: T` => `def f: impl -> T { .. }`
def print[T]: impl Print[T] -> T -> Unit {
    print impl { print } value = print value
}

def default print_show[T]: impl Show[T] -> impl Print[T] {
    print_show impl { show } = impl {
        print val = for_each putchar (show val)
    }
}

def id[T]: T -> T {
    id x = x
}

def default show_list: impl Show[List[Int]] {
    show_list = impl {
        show = id
    }
}

def default show_int: impl Show[Int] {
    show_int = impl {
        show = show_int_inner
    }
}

def show_int_inner: Int -> List[Int] {
    show_int_inner n = (
        let n2 = copy &n
        if ((copy &n) >= 10) (\a -> (
            let quot = (copy &n) / 10
            let rem = n - (copy &quot) * 10
            concat (show quot) (show rem)
        )) (\a ->
            (n2 + 48) :- empty
        )
    )
}
