use bool

aspect PartialEq[T] {
    == : T -> T -> Bool
}

def != [T]: impl PartialEq[T] -> T -> T -> Bool {
    != the_impl a b = not (@ == the_impl a b)
}

enum Ordering = Less {} | Equal {} | Greater {}

aspect Ord[T] {
    cmp: T -> T -> Ordering
}

def > [T]: impl Ord[T] -> T -> T -> Bool {
    > the_impl x y = match (@cmp the_impl x y) (
        Greater {} -> true
        _ -> false
    )
}

def < [T]: impl Ord[T] -> T -> T -> Bool {
    < the_impl x y = match (@cmp the_impl x y) (
        Less {} -> true
        _ -> false
    )
}

def >= [T]: impl Ord[T] -> T -> T -> Bool {
    >= the_impl x y = match (@cmp the_impl x y) (
        Less {} -> false
        _ -> true
    )
}

def <= [T]: impl Ord[T] -> T -> T -> Bool {
    <= the_impl x y = match (@cmp the_impl x y) (
        Greater {} -> false
        _ -> true
    )
}

aspect Add[L, R] {
    + : L -> R -> L
}

aspect Sub[L, R] {
    - : L -> R -> L
}

aspect Mul[L, R] {
    * : L -> R -> L
}

aspect Div[L, R] {
    / : L -> R -> L
}
