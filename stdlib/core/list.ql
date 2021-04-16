enum List[T] = Cons { value: T, list: List[T] } | Empty {}

def concat[T]: List[T] -> List[T] -> List[T] {
    concat Empty {} list = list
    concat Cons { value, list } other = Cons { value, list = concat list other }
}
