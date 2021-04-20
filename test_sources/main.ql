pub enum Either[T, U] = Left { value: T } | Right { value: U }

pub data Unit {}

pub def create_either[T]: T -> Either[T, Unit] {
    create_either t = Left { value = t }
    //create_either a = Right { value = a }
}

pub enum Option[T] = Some { value: T } | None {}

pub def unwrap_or[T]: T -> Option[T] -> T {
    unwrap_or _ Some { value } = value
    unwrap_or t None {} = t
}

pub def block: Option[Option[Unit]] {
    block = (
        let inner = Unit {}
        let next = Some { value = inner }
        Some { value = next }
    )
}

// pub enum Bool = True {} | False {}
//
// pub def or: Bool -> Bool -> Bool {
//     or True {} = \a -> a
//     or _ = \a -> False {}
// }

def main: unit {
    main = (
        // unwrap_or Some { value = Unit {} } block
        // create_either 104
        // drop make_unit
        // drop Some { value = 100 }
        // putchar 72
        // putchar (unwrap_or 65 Some { value = 66 })

        // "Hello, world!" in Unicode code points is
        // 72 101 108 108 111 44 32 119 111 114 108 100 33
        let hello = Cons { value = 72, list = Cons { value = 101, list = Cons { value = 108, list = Cons { value = 108, list = Cons { value = 111, list  = Empty {} } } } } }
        let punctuation = Cons { value = 44, list = Cons { value = 32, list = Empty {} } }
        let world = Cons { value = 119, list = Cons { value = 111, list = Cons { value = 114, list = Cons { value = 108, list = Cons { value = 100, list = Cons { value = 33, list = Empty {} } } } } } }
        let hello_world = concat (concat hello punctuation) world
        print_list hello_world
    )
}

def make_unit: Unit {
    make_unit = unit
}

def drop[T]: T -> Unit {
    drop _ = unit
}

def putchar: Int -> Unit { compiler_intrinsic }

enum List[T] = Cons { value: T, list: List[T] } | Empty {}

def map_first[T]: (T -> T) -> (List[T] -> List[T]) {
    map_first f Cons { value, list } = Cons { value = f value, list }
    map_first _ Empty {}             = Empty {}
}

def print_list: List[Int] -> Unit {
    print_list Cons { value, list } = (
        putchar value
        print_list list
    )
    print_list _ = unit
}

def concat[T]: List[T] -> List[T] -> List[T] {
    concat Empty {} list = list
    concat Cons { value, list } other = Cons { value, list = concat list other }
}

// Once we have some `clone` function, we can implement `map` for a cloneable function object.
// def map[T, U]: (T -> U) -> (List[T] -> List[U]) {
//     map f Cons { value, list } = Cons { value = f value, list = map f list }
//     map _ Empty {}             = Empty {}
// }
