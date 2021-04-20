def or: Bool -> Bool -> Bool {
    or false false = false
    or _ _ = true
}

// Laziness is not yet implemented; this `if` statement will evaluate both input operands before returning.
def if[T]: Bool -> T -> T -> T {
    if true value _ = value
    if false _ value = value
}

def if_lazy[T]: Bool -> (Unit -> T) -> (Unit -> T) -> T {
    if_lazy true value _ = value unit
    if_lazy false _ value = value unit
}

def true2: Bool {
    true2 = true
}
