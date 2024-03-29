def not: Bool -> Bool {
    not false = true
    not true = false
}

def or: Bool -> Bool -> Bool {
    or false false = false
    or _ _ = true
}

def and: Bool -> Bool -> Bool {
    and true true = true
    and _ _ = false
}

def if[T]: Bool -> (Unit -> T) -> (Unit -> T) -> T {
    if true value _ = value unit
    if false _ value = value unit
}

def true2: Bool {
    true2 = true
}
