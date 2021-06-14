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

def should_fail: List[Int] {
    // Does not contain all required fields.
    should_fail = Cons { value = 0 }
}
