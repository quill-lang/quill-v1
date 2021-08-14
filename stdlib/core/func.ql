def id[T]: T -> T {
    id x = x
}

def |> [A, B]: A -> (A -> B) -> B {
    a |> b = b a
}

def <| [A, B]: (A -> B) -> A -> B {
    <| = id
}

def ||> [A, B, C]: (A -> B) -> (B -> C) -> (A -> C) {
    f ||> g = \a -> g (f a)
}

def <|| [A, B, C]: (B -> C) -> (A -> B) -> (A -> C) {
    f <|| g = \a -> f (g a)
}
