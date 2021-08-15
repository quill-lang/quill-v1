aspect PartialEq[T] {
    == : T -> T -> Bool
}

aspect Add[L, R, O] {
    + : L -> R -> O
}

aspect Sub[L, R, O] {
    - : L -> R -> O
}

aspect Mul[L, R, O] {
    * : L -> R -> O
}

aspect Div[L, R, O] {
    / : L -> R -> O
}
