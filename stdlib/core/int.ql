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

def + : Int -> Int -> Int {
    + = add_int_unchecked
}

def - : Int -> Int -> Int {
    - = sub_int_unchecked
}

def * : Int -> Int -> Int {
    * = mul_int_unchecked
}

def / : Int -> Int -> Int {
    / = div_int_unchecked
}

def > : Int -> Int -> Bool {
    > = gt_int
}

def < : Int -> Int -> Bool {
    < = lt_int
}

def >= : Int -> Int -> Bool {
    >= = ge_int
}

def <= : Int -> Int -> Bool {
    <= = le_int
}

def != : Int -> Int -> Bool {
    != = ne_int
}

def factorial: Int -> Int {
    factorial 0 = 1
    factorial n = (copy &n) * (factorial (n - 1))
}
