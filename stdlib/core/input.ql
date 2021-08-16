use bool
use int
use list
use option
use ops

def getchar: Unit -> Int { compiler_intrinsic }

// Returns a line, delimited by \r or \n.
def get_line: Unit -> List[Int] {
    get_line _ = match (getchar unit) (
        // \n
        10 -> Empty {}
        // \r
        13 -> Empty {}
        // Any other character.
        value -> Cons { value, list = get_line unit }
    )
}

def get_int: Unit -> Option[Int] {
    get_int _ = parse_int (get_line unit)
}

// Converts a string into a parsed integer.
def parse_int: List[Int] -> Option[Int] {
    parse_int = parse_int_inner 0
}

// The first argument is an already-parsed prefix to the string.
def parse_int_inner: Int -> List[Int] -> Option[Int] {
    parse_int_inner prefix Cons { value, list } = (
        // If the value is in the range 48-57, then this is a number.
        match (and ((copy &value) >= 48) ((copy &value) <= 57)) (
            true -> (
                let int = value - 48
                parse_int_inner (prefix * 10 + int) list
            )
            false -> None {}
        )
    )
    parse_int_inner value Empty {} = Some { value }
}
