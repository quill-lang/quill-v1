use list

def getchar: Unit -> Int { compiler_intrinsic }

def get_line: Unit -> List[Int] {
    get_line _ = match (getchar unit) (
        10 -> Empty {}
        value -> Cons { value, list = get_line unit }
    )
}
