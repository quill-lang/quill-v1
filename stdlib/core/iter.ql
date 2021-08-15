use option
use list

data IterResult[Iter, Item] { iter: Iter, item: Option[Item] }

aspect Iterator[Iter, Item] {
    next: Iter -> IterResult[Iter, Item]
}

// TODO make this automatically created from the aspect
def next[Iter, Item]: impl Iterator[Iter, Item] -> Iter -> IterResult[Iter, Item] {
    next impl { next } value = next value
}

def default iter_list[T]: impl Iterator[List[T], T] {
    iter_list = impl {
        next Cons { value, list } = IterResult { iter = list, item = Some { value } }
        next Empty {} = IterResult { iter = Empty {}, item = None {} }
    }
}

def for_each[Iter, Item]: impl Iterator[Iter, Item] -> (Item -> Unit) -> Iter -> Unit {
    for_each the_impl f iter = match (@next the_impl iter) (
        IterResult { iter, item = None {} } -> unit
        IterResult { iter, item = Some { value } } -> (
            (copy &f) value
            @for_each the_impl f iter
        )
    )
}
