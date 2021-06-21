use int

aspect PartialEq[T] {
    == : T -> T -> Bool
}

def partial_eq_for_int: impl PartialEq[Int] {
    partial_eq_for_int = impl {
        == = eq_int
    }
}
