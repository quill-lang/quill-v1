use print
use list
use bool
use int

def + : Int -> Int -> Int {
    + = add_int_unchecked
}

def - : Int -> Int -> Int {
    i - = sub_int_unchecked i
}

def :-[T]: T -> List[T] -> List[T] {
    x :- xs = Cons { value = x, list = xs }
}

def empty[T]: List[T] {
    empty = Empty {}
}

def main: Unit {
    main = (
        // "Hello, world!" in Unicode code points is
        // 72 101 108 108 111 44 32 119 111 114 108 100 33
        // let hello = Cons { value = add_int_unchecked 70 (if true 2 3), list = Cons { value = 101, list = Cons { value = 108, list = Cons { value = 108, list = Cons { value = 111, list  = Empty {} } } } } }
        // let punctuation = Cons { value = 44, list = Cons { value = 32, list = Empty {} } }
        // let world = Cons { value = 119, list = Cons { value = 111, list = Cons { value = 114, list = Cons { value = 108, list = Cons { value = 100, list = Cons { value = 33, list = Empty {} } } } } } }
        // let hello_world = concat (concat hello punctuation) world
        // print_list hello_world
        // newline unit

        print_list (72 :- 101 :- 108 :- 108 :- 111 :- 44 :- 32 :- 119 :- 111 :- 114 :- 108 :- 100 :- 33 :- empty)
        newline unit

        print_factorials 0 20
    )
}

def print_factorials: Int -> Int -> Unit {
    print_factorials low high = if_lazy (gt_int (copy &low) (copy &high)) nop (print_factorials_inner low high)
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
