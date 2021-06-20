enum List[T] = Cons { value: T, list: List[T] } | Empty {}
def should_fail: List[Int] {
    // Does not contain all required fields.
    should_fail = Cons { value = 0 }
}
def main: Unit {
    main = unit
}
