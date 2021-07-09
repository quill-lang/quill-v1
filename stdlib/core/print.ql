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

def print_list: impl Print[List[Int]] {
    print_list = impl {
        print = for_each putchar
    }
}

def perform_print_list: impl Print[List[Int]] -> List[Int] -> Unit {
    perform_print_list impl { print } list = print list
}

def print_int: Int -> Unit {
    print_int n = (
        let n2 = copy &n
        if ((copy &n) >= 10) (\a -> (
            let quot = (copy &n) / 10
            let rem = n - (copy &quot) * 10
            print_int quot
            print_int rem
        )) (\a ->
            putchar (n2 + 48)
        )
    )
}
