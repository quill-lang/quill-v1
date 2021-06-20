class PartialEq[T] {
    def ==: T -> T -> Bool
}

// FIXME: This syntax should definitely be improved but it's good enough for trying things out.
def partial_eq_for_int: impl PartialEq[Int] {
    partial_eq_for_int = impl PartialEq[Int] {
        == = eq_int
    }
}
