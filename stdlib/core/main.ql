use print
use list

def main: unit {
    main = (
        // "Hello, world!" in Unicode code points is
        // 72 101 108 108 111 44 32 119 111 114 108 100 33
        let hello = Cons { value = 72, list = Cons { value = 101, list = Cons { value = 108, list = Cons { value = 108, list = Cons { value = 111, list  = Empty {} } } } } }
        let punctuation = Cons { value = 44, list = Cons { value = 32, list = Empty {} } }
        let world = Cons { value = 119, list = Cons { value = 111, list = Cons { value = 114, list = Cons { value = 108, list = Cons { value = 100, list = Cons { value = 33, list = Empty {} } } } } } }
        let hello_world = concat (concat hello punctuation) world
        print_list hello_world
    )
}

// "error: could not resolve definition" ?
// def or: Bool -> Bool -> Bool {
//     or False {} False {} = False {}
//     or _ _ = True {}
// }
