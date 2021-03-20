pub enum Bool = True {} | False {}
pub enum Option[T] = Some { value: T } | None {}

pub def id[F[_]]: F[Bool] -> F[Bool] {
    id x = x
}

// More higher-kinded test cases will be inserted here, once traits are done.
// After all, we can't operate generically over types if we have no typeclasses!
