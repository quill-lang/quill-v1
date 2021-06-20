def should_succeed: Int -> Int {
    // Should succeed, using `_` as an abstraction variable name.
    should_succeed = \_ -> 1
}

def main: Unit {
    main = (
        should_succeed 2
        unit
    )
}
