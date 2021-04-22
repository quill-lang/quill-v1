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

def factorial: Int -> Int {
    factorial 0 = 1
    factorial n = mul_int_unchecked (copy &n) (factorial (sub_int_unchecked n 1))
}
