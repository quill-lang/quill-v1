def putchar: Int -> Unit { compiler_intrinsic }

data Tuple[T, U] { fst: T, snd: U }

def get_fst[T, U]: Tuple[T, U] -> T {
    get_fst tuple = match tuple (
        Tuple { fst, snd = _ } -> fst
    )
}

def main: Unit {
    main = (
        putchar (get_fst Tuple { fst = 65, snd = false })
    )
}
