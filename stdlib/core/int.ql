use ops

def add_int_unchecked: Int -> Int -> Int { compiler_intrinsic }
def sub_int_unchecked: Int -> Int -> Int { compiler_intrinsic }
def mul_int_unchecked: Int -> Int -> Int { compiler_intrinsic }
def div_int_unchecked: Int -> Int -> Int { compiler_intrinsic }
def gt_int: Int -> Int -> Bool { compiler_intrinsic }
def ge_int: Int -> Int -> Bool { compiler_intrinsic }
def lt_int: Int -> Int -> Bool { compiler_intrinsic }
def le_int: Int -> Int -> Bool { compiler_intrinsic }
def eq_int: Int -> Int -> Bool { compiler_intrinsic }
def ne_int: Int -> Int -> Bool { compiler_intrinsic }

def default add_int: impl Add[Int, Int] {
    add_int = impl {
        + = add_int_unchecked
    }
}

def default sub_int: impl Sub[Int, Int] {
    sub_int = impl {
        - = sub_int_unchecked
    }
}

def default mul_int: impl Mul[Int, Int] {
    mul_int = impl {
        * = mul_int_unchecked
    }
}

def default div_int: impl Div[Int, Int] {
    div_int = impl {
        / = div_int_unchecked
    }
}

def default ord_int: impl Ord[Int] {
    ord_int = impl {
        cmp x y = match (le_int (copy &x) (copy &y)) (
            true -> Less {}
            false -> match (eq_int x y) (
                true -> Equal {}
                false -> Greater {}
            )
        )
    }
}

def default partial_eq_int: impl PartialEq[Int] {
    partial_eq_int = impl {
        == = eq_int
    }
}

def factorial: Int -> Int {
    factorial 0 = 1
    factorial n = (copy &n) * (factorial (n - 1))
}
