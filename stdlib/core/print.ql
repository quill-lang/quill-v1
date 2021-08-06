use list
use int
use bool

def putchar: Int -> Unit { compiler_intrinsic }

def newline: Unit -> Unit {
    newline _ = putchar 10
}

aspect Print[T] {
    print: T -> Unit
}

// TODO: Automatically generate this function,
// perhaps by using a keyword like "export"?
// `export f: T` => `def f: impl -> T { .. }`
def print[T]: impl Print[T] -> T -> Unit {
    print impl { print } value = print value
}

def default print_list: impl Print[List[Int]] {
    print_list = impl {
        print = for_each putchar
    }
}

def default print_int: impl Print[Int] {
    print_int = impl {
        print = print_int_inner
    }
}

def print_int_inner: Int -> Unit {
    print_int_inner n = (
        let n2 = copy &n
        if ((copy &n) >= 10) (\a -> (
            let quot = (copy &n) / 10
            let rem = n - (copy &quot) * 10
            print quot
            print rem
        )) (\a ->
            putchar (n2 + 48)
        )
    )
}
