def putchar: Int -> Unit { compiler_intrinsic }

enum List[T] = Cons { value: T, list: List[T] } | Empty {}

def :- [T]: T -> List[T] -> List[T] {
    x :- xs = Cons { value = x, list = xs }
}

// This regression test is for the functionality of copying functions.
def mapM: (Int -> Unit) -> List[Int] -> Unit {
    mapM f Cons { value, list } = ((copy &f) value, mapM f list)
    mapM _ Empty {} = unit
}

// This specific test tries to verify that copying functions works, even if the function contains data,
// and even if that data has heap indirections.
def print_list_delayed: List[Int] -> Unit -> Unit {
    print_list_delayed list _ = mapM putchar list
}

def main: Unit {
    main = (
        let f = print_list_delayed (72 :- 101 :- 108 :- 108 :- 111 :- 44 :- 32 :- 119 :- 111 :- 114 :- 108 :- 100 :- 33 :- Empty {})
        (copy &f) unit
        (copy &f) unit
        f unit
    )
}
