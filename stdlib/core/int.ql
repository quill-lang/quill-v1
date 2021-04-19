def add_int_unchecked: Int -> Int -> Int { compiler_intrinsic }
def sub_int_unchecked: Int -> Int -> Int { compiler_intrinsic }
def mul_int_unchecked: Int -> Int -> Int { compiler_intrinsic }
def div_int_unchecked: Int -> Int -> Int { compiler_intrinsic }

def is_zero: Int -> Bool {
    is_zero 0 = true
    is_zero _ = false
}
