enum List[T] = Cons { value: T, list: List[T] } | Empty {}

def :- [T]: T -> List[T] -> List[T] {
    x :- xs = Cons { value = x, list = xs }
}

def empty[T]: List[T] {
    empty = Empty {}
}

def concat[T]: List[T] -> List[T] -> List[T] {
    concat Empty {} list = list
    concat Cons { value, list } other = Cons { value, list = concat list other }
}

def for_each[T]: (T -> Unit) -> List[T] -> Unit {
    for_each f Cons { value, list } = ((copy &f) value, for_each f list)
    for_each f Empty {} = unit
}

data SameType[T] { a: T, b: T }

def as_ref[T]: (& 'a List[T]) -> List[& 'a T] {
    as_ref &Cons { value, list } = (
        Cons { value, list = as_ref list }
    )
    as_ref &Empty {} = Empty {}
}

def copied[T]: List[& 'a T] -> List[T] {
    copied Cons { value, list } = Cons { value = copy value, list = copied list }
    copied Empty {} = Empty {}
}
