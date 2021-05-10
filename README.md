# The Quill Programming Language

[![release latest](https://github.com/quill-lang/quill/actions/workflows/release-latest.yml/badge.svg)](https://github.com/quill-lang/quill/actions/workflows/release-latest.yml)
[![test](https://github.com/quill-lang/quill/actions/workflows/test.yml/badge.svg)](https://github.com/quill-lang/quill/actions/workflows/test.yml)
[![format](https://github.com/quill-lang/quill/actions/workflows/format.yml/badge.svg)](https://github.com/quill-lang/quill/actions/workflows/format.yml)

Quill is a modern programming language that aims to bring the functional paradigm to high-performance, low level programming.

## 🚧 Actively Developed 🚧

Quill is evolving all the time, and is in very early stages of development. The features outlined below are not all currently implemented in the Quill compiler. In particular, the borrow checker and zero-cost function currying abstractions are not implemented, although this will change in the near future.

## Code Sample

```
enum List[T] = Cons { value: T, list: List[T] } | Empty {}

def :- [T]: T -> List[T] -> List[T] {
    x :- xs = Cons { value = x, list = xs }
}

def concat[T]: List[T] -> List[T] -> List[T] {
    concat Empty {} list = list
    concat Cons { value, list } other = Cons {
        value
        list = concat list other
    }
}

def one_to_five: List[Int] {
    one_to_five = 1 :- 2 :- 3 :- 4 :- 5 :- Empty{}
}
```

## Installing

Quill is not ready for use in any 'real' projects.
However, if you want to experiment with the compiler, go to the [latest release](https://github.com/quill-lang/quill/releases/tag/latest) page, and download `ubuntu-latest_quill_install` or `windows-latest_quill_install.exe`.
Run the relevant executable inside a terminal.
These installers will download and extract the Quill compiler and its dependencies.
It will prompt you to add the binary directory to your `PATH` so that you can run `quill` from any terminal.

```sh
# Automatically update quill and its dependencies
quill update

# Build and run the core library
quill -p stdlib/core run
```

## Goals

The project aims to create a programming language which is expressive, safe, portable, and fast (in that order).
We aim to offer a paradigm comparable to Haskell, safety and compile-time correctness comparable to Rust, and speed comparable to C.

### Expressiveness

Quill is designed to be expression-oriented, making expressions (rather than statements) the core structural primitive of the language.
This gives the language its functional style.
Unlike other FP languages, Quill is eager by default and uses an explicit effect system instead of monadic effect encapsulation.

### Safety

To ensure memory safety, Quill uses a Rust-style borrow system that ensures that all references to data are valid, and that data is deleted once it is no longer required.
There is no garbage collector, and memory is handled entirely at compile-time when possible.

### Portability

Quill is built on the LLVM compiler architecture so you can compile code for any OS, while developing on any OS.
No docker, no configuration, no extra dependencies - you can write code once and have it run anywhere with no changes.
The same code should behave exactly the same on all platforms, wherever possible.

### Speed

The language is compiled down into machine code, which allows Quill's theoretical maximum speed to be the same as C, C++ or Rust.
Quill contains a lot of zero-cost abstractions, such as the effect system or the ability to partially apply functions.
