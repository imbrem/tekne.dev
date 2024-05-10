---
title: What Makes a Language Fast?
edited: '2024-05-10'
published: '2023-08-18'
---
Back in the day, I had a teacher tell me there was no such thing (at least in the context of the
.NET framework) as a "fast" or "slow" programming language, since, after all, the .NET languages all
compiled to the same [intermediate
representation](https://en.wikipedia.org/wiki/Common_Intermediate_Language). Of course, this isn't
true: even for languages targeting the same platform, programs doing the same thing can have vastly
different performance characteristics. [^1] [^2]

The stereotypical answer is that faster programming languages allow the user more direct control
over the machine. C, after all, can in a sense never be faster than assembly, since I always have
the option of writing out the assembly code my C compiler would generate. Performance, however, is
dictated not by the very fastest code I _can_ write, but rather by the code I _actually_ write. [^3]

In this article, we’ll begin to explore a more subtle explanation for the speed differences between
programming languages taking into account the above observation. We’ll do so by comparing solutions
to the same very simple problem: sorting a list of price levels by price, then quantity, in C, C++,
and Rust, three languages which afford the programmer rather similar levels of “machine control.”
This will allow us to explore how other factors can have a drastic effect on speed. In the process,
we’ll briefly cover:
- Benchmarking simple functions effectively using
  [Criterion](https://github.com/bheisler/criterion.rs)
- Compiling and linking with C and C++ code from Rust using the
  [`cc`](https://docs.rs/cc/latest/cc/) crate
- The effect of inlining on performance and binary size

Source code to follow along can be found at
[https://github.com/imbrem/sorting-bench](https://github.com/imbrem/sorting-bench)

# The Problem

Our goal is to show the difference in the _practical_, rather than _theoretical_, performance of
programming languages. Therefore, we want to pick a small problem which is not going to be the
performance bottleneck of a given application; instead, it’s going to be one of the many things
given 10 minutes of development time and then promptly forgotten. The idea is that the performance
of such code is going to determine the baseline performance of the bulk of the application. To keep
the comparison between languages fair, we’re going to expose a single function with the standard C
ABI. [^4]

Let’s assume we’re given an array of price levels in the following format:
```rust
#[repr(C)]
struct PriceLevel {
    price: u32,
    quantity: u32,
    exchange_id: u32,
    order_id: u32
}
```
Our goal will be to sort this array by price followed by quantity, leaving the ordering by exchange
ID and order ID arbitrary. So, for example, the input
```rust
[
    PriceLevel { price: 1, quantity: 2, exchange_id: 5, order_id: 6 },
    PriceLevel { price: 2, quantity: 1, exchange_id: 9, order_id: 0 },
    PriceLevel { price: 1, quantity: 2, exchange_id: 3, order_id: 4 }, 
    PriceLevel { price: 1, quantity: 3, exchange_id: 7, order_id: 8 },
]
```
should be transformed to _either_
```rust
[
    PriceLevel { price: 1, quantity: 2, exchange_id: 3, order_id: 4 }, 
    PriceLevel { price: 1, quantity: 2, exchange_id: 5, order_id: 6 },
    PriceLevel { price: 1, quantity: 3, exchange_id: 7, order_id: 8 },
    PriceLevel { price: 2, quantity: 1, exchange_id: 9, order_id: 0 },
]
```
or
```rust
[
    PriceLevel { price: 1, quantity: 2, exchange_id: 5, order_id: 6 }, 
    PriceLevel { price: 1, quantity: 2, exchange_id: 3, order_id: 4 },
    PriceLevel { price: 1, quantity: 3, exchange_id: 7, order_id: 8 },
    PriceLevel { price: 2, quantity: 1, exchange_id: 9, order_id: 0 },
]
```

# The Solutions

Let’s go ahead and write up some annotated solutions to this problem in each source language.
Remember, we’re not trying to write the fastest code, rather, we’re trying to emulate the process of
quickly addressing a small, unimportant problem in a large code-base. So yes standard library, no
manual inlining and micro-optimization. 

## C

Here’s our algorithm written in C:
```c
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

// Struct representing a (price, quantity) pair
typedef struct {
    uint32_t price;
    uint32_t quantity;
    uint32_t exchange_id;
    uint32_t order_id;
} PriceLevel;

// Comparison function for qsort
inline static int compare_levels(const void *a, const void *b) {
    const PriceLevel *levelA = (const PriceLevel*)a;
    const PriceLevel *levelB = (const PriceLevel*)b;

    // Compare based on price, followed by quantity
    if (levelA->price < levelB->price)
        return -1;
    else if (levelA->price > levelB->price)
        return 1;
    else if (levelA->quantity < levelB->quantity)
        return -1;
    else if (levelA->quantity > levelB->quantity)
        return 1;
    else
        return 0;
}

void sort_price_levels_c(PriceLevel* data, size_t len) {
    qsort(data, len, sizeof(PriceLevel), compare_levels);
}
```
As you can see, we do our sorting by simply calling the standard library `qsort` function with a
custom comparison function `compare_levels`. As is standard in C, this returns a positive number if
the left is greater than the right, a negative number if the right is greater than the left, and
zero if they are equal. It’s not very elegant code, but it’s what someone could write using only the
standard library in a hurry.

## C++

In C++, things are looking a little nicer. For a start, the standard library nudges us towards using
a boolean comparator function (rather than returning an ordering via signed integer)  which can
easily be implemented in a branch-free fashion. In particular, we get the following code:
```cpp
#include <iostream>
#include <algorithm>
#include <cstdint>

// Struct representing a (price, quantity) level
struct PriceLevel {
    uint32_t price;
    uint32_t quantity;
    uint32_t exchange_id;
    uint32_t order_id;
};

// Comparison function for std::sort (branch-free)
inline static bool compare_levels(const PriceLevel& levelA, const PriceLevel& levelB) {
    return (levelA.price < levelB.price) 
        || ((levelA.price == levelB.price) && (levelA.quantity < levelB.quantity));
}

extern "C" {
    void sort_price_levels_cpp(PriceLevel* data, size_t len) {
        std::sort(data, data + len, compare_levels);
    }
}
```
Notice how we have to put the `sort_price_levels_cpp` function in an extern “C” block. This
indicates to the C++ compiler not to perform name mangling[^5], allowing us to call
`sort_price_levels_cpp` just like a regular C function.

## Rust

Finally, we come to our Rust implementation:

```rust
use std::cmp::Ordering;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(C)]
pub struct PriceLevel {
    pub price: u32,
    pub quantity: u32,
    pub exchange_id: u32,
    pub order_id: u32,
}

#[inline(always)]
fn compare_price_levels(left: &PriceLevel, right: &PriceLevel) -> Ordering {
    left.price
        .cmp(&right.price)
        .then(left.quantity.cmp(&right.quantity))
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn sort_price_levels_rust(data: *mut PriceLevel, len: usize) {
    let slice = std::slice::from_raw_parts_mut(data, len);
    slice.sort_unstable_by(compare_price_levels)
}
```

Interestingly, native Rust-style comparison is very much like C-style comparison, except that the
`Ordering` enum ensures that there are only three possible return values from a comparator
(`Greater`, corresponding to a positive number, `Equal`, corresponding to 0, and `Less`,
corresponding to a negative number).

Note that our `sort_price_levels_rust` function is `unsafe` since, to match the API provided by C
and C++, it takes in a raw pointer to `PriceLevel` and a length, which are not guaranteed to be
valid. Otherwise, this is exactly equivalent to what we’d write in regular Rust, since a slice is
guaranteed to be composed of a data pointer and a length (and the latter is coerced into the former
via `std::slice::from_raw_parts`).

We mark our function `#[inline(never)]` to make our benchmark a little more fair, though,  given the
way we set it up, it shouldn’t have much of an effect. As in C++, we use the `extern “C”` modifier
to indicate that our function should use the C ABI[^6], and the `#[no_mangle]` attribute to indicate
that the Rust compiler should not perform name mangling.

# Benchmarking

Now that we’ve got our implementations, let’s see if they’re any good!

## Setting up our crate

We’re going to be benchmarking our code using Criterion, so for that, we need to give everything a
nice shiny Rust API. We’re going to expose all our code as a single crate, which we’ll create as
follows:
```
cargo new --lib sorting-bench
```
We’ll empty out the automatically generated `src/lib.rs` and replace it with our Rust code above.
We’ll then put the C code in `src/sort.c` and `src/sort.cpp`; right now this doesn’t do anything,
but we’ll get back to it later when we set up FFI.

Finally, it’s nice to have some sanity checks to make sure everything looks about right before we
start benchmarking proper. We’ll write a generic test that takes in a pointer to a sorting function
and performs a quick sanity check, and apply it to our Rust code (for now), by sticking the
following at the end of `lib.rs`:
```rust
#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn rust_sort() {
        unsafe { sorting_test(sort_price_levels_rust) }
    }

    unsafe fn sorting_test(
        sorter: unsafe extern "C" fn(*mut PriceLevel, usize)
    ) {
        let mut levels = [
            PriceLevel {
                price: 5,
                quantity: 100,
                exchange_id: 2,
                order_id: 42,
            },
            PriceLevel {
                price: 3,
                quantity: 100,
                exchange_id: 88,
                order_id: 32,
            },
            PriceLevel {
                price: 1,
                quantity: 50,
                exchange_id: 39,
                order_id: 40,
            },
            PriceLevel {
                price: 1,
                quantity: 100,
                exchange_id: 32,
                order_id: 12,
            },
        ];
        let len = levels.len();
        unsafe { sorter(levels.as_mut_ptr(), len) };
        assert_eq!(
            levels,
            [
                PriceLevel {
                    price: 1,
                    quantity: 50,
                    exchange_id: 39,
                    order_id: 40,
                },
                PriceLevel {
                    price: 1,
                    quantity: 100,
                    exchange_id: 32,
                    order_id: 12,
                },
                PriceLevel {
                    price: 3,
                    quantity: 100,
                    exchange_id: 88,
                    order_id: 32,
                },
                PriceLevel {
                    price: 5,
                    quantity: 100,
                    exchange_id: 2,
                    order_id: 42,
                },
            ]
        );
    }
}
```
We can now check everything is working by simply running
```
cargo test
```

## Setting up Criterion

Let’s now begin setting up the benchmarks proper. To do so, we’ll need to add `criterion` to our
list of `dev-dependencies` (which are dependencies required only when testing or benchmarking).
While we’re at it, we’ll add `rand` and `rand_xoshiro` as well, to help us generate random numbers
for our benchmark. To do so, we add the following to our `Cargo.toml`:
```toml
[dev-dependencies]
criterion = "0.5"
rand = "0.8"
rand_xoshiro = "0.6"
```
Next, we’ll install `cargo-criterion`, which is a utility for running Criterion benchmarks, as
follows:
```
cargo install cargo-criterion
```
Note that this step is optional; Criterion benchmarks can also be run by invoking `cargo bench`
instead of `cargo criterion`, but plots will not be generated.

We now need to create the benchmark proper. First, we have to declare it in our `Cargo.toml`, by
simply adding the following:
```toml
[[bench]]
name = "sorting"
harness = false
```
Time to create the benchmark proper: first, we create a folder called `benches` in the root
directory, and then, in `benches/sorting.rs`, we write the following:
```rust
use criterion::{criterion_group, criterion_main, Criterion};
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro128Plus;
use sorting_bench::*;

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut buf = Vec::with_capacity(BENCHMARK_LEN);
    let mut rng = Xoshiro128Plus::from_seed([2; 16]);
    c.bench_function("sort rust", |b| {
        b.iter(|| unsafe { benchmark_sorter(sort_price_levels_rust, &mut buf, &mut rng) })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

const BENCHMARK_LEN: usize = 4096;

unsafe fn benchmark_sorter(
    sorter: unsafe extern "C" fn(*mut PriceLevel, usize),
    buf: &mut Vec<PriceLevel>,
    rng: &mut impl Rng,
) {
    buf.clear();
    buf.extend((0..BENCHMARK_LEN).map(|_| PriceLevel {
        price: rng.gen(),
        quantity: rng.gen(),
        exchange_id: rng.gen(),
        order_id: rng.gen(),
    }));
    unsafe { sorter(buf.as_mut_ptr(), BENCHMARK_LEN) }
    for i in 1..BENCHMARK_LEN {
        assert!((buf[i - 1].price, buf[i - 1].quantity) <= (buf[i].price, buf[i].quantity))
    }
}
```
Let’s break down what this code is doing:
- `criterion_benchmark` registers a benchmark, `sort rust`, which measures the time it takes to call
  `benchmark_sorter` with the given sorting implementation (here, the Rust one), buffer, and RNG
- `criterion_group` makes a benchmark group `benches` containing the benchmarks registered by
  `criterion_benchmark`
- `criterion_main` generates a `main` function which executes the benchmarks in benches
- The actual benchmark itself, `benchmark_sorter`, generates `BENCHMARK_LEN = 4096` random price
  levels, sorts them, and then checks if they’re sorted.

We can now execute this benchmark by running
```
cargo criterion
```
This will give us the results for Rust; we now want to link in our C and C++ to compare.

## Setting up FFI

To link with our C and C++, we need to compile it. Thankfully, with Cargo, it’s not too difficult.
First, we need to add a `build-dependency` on the `cc` crate; this is going to allow us to call out
to a C or C++ compiler from our build script. Doing this is as simple as adding the following to our
`Cargo.toml`:
```toml
[build-dependencies]
cc = "1.0"
```
Now, all that’s left is to write the build script itself: in our root directory, we create a file
called `build.rs` containing the following:
```rust
fn main() {
    println!("cargo:rerun-if-changed=src/sort.c");
    cc::Build::new().file("src/sort.c").compile("libcsort.a");
    println!("cargo:rerun-if-changed=src/sort.cpp");
    cc::Build::new()
        .file("src/sort.cpp")
        .cpp(true)
        .compile("libcppsort.a");
}
```
The code here is mostly self-explanatory: `sort.c` and `sort.cpp` are compiled into static libraries
`libcsort.a` and `libcppsort.a` respectively, the latter with a C++ compiler. These will be linked
with our Rust source automatically by Cargo. The print statements instruct Cargo to rerun the build
script if either of `sort.c` or `sort.cpp` change, recompiling the static libraries as necessary.
And that’s about it!

Now all that’s left to do is put the names and prototypes of our C and C++ functions in an extern
block in `src/lib.rs` as follows:
```rust
extern "C" {
    pub fn sort_price_levels_c(data: *mut PriceLevel, len: usize);
    pub fn sort_price_levels_cpp(data: *mut PriceLevel, len: usize);
}
```
To make sure everything is working correctly, we’ll add tests for our C++ and C sorting algorithms
to lib.rs by modifying our tests modules as follows:
```rust
#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn c_sort() {
        unsafe { sorting_test(sort_price_levels_c) }
    }

    #[test]
    fn cpp_sort() {
        unsafe { sorting_test(sort_price_levels_cpp) }
    }

    // --- snip ---
}
```
And, for the moment of truth,
```
cargo test
```
And it works! Let’s similarly extend our benchmarks in `benches/sorting.rs`...
```rust
// --- snip ---

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut buf = Vec::with_capacity(BENCHMARK_LEN);
    let mut rng = Xoshiro128Plus::from_seed([2; 16]);
    c.bench_function("sort c", |b| {
        b.iter(|| unsafe { benchmark_sorter(sort_price_levels_c, &mut buf, &mut rng) })
    });
    c.bench_function("sort cpp", |b| {
        b.iter(|| unsafe { benchmark_sorter(sort_price_levels_cpp, &mut buf, &mut rng) })
    });
    c.bench_function("sort rust", |b| {
        b.iter(|| unsafe { benchmark_sorter(sort_price_levels_rust, &mut buf, &mut rng) })
    });
}

// --- snip ---
```
and we’re done!

## Results

Let’s take a look at the results of the above benchmark[^7]:
```
sort c                  time:   [387.67 µs 388.17 µs 388.90 µs]                   

sort cpp                time:   [194.39 µs 194.52 µs 194.66 µs]  

sort rust               time:   [193.24 µs 193.37 µs 193.51 µs]
```
While C++ and Rust have comparable performance, the C is almost exactly twice as slow! That’s an
interesting result... but _why_?

One thing we might notice is that this is not exactly a fair comparison: while the Rust and C
comparison functions do about the same things, the former is written at a much higher level, and
therefore might be compiled differently. Let’s test this hypothesis by writing a new C++ sorting
algorithm with the comparator copied as directly as possible from C. We’ll add the following to
`src/sort.cpp`:
```cpp
// Comparison function for qsort
inline static int compare_levels_int(const PriceLevel& levelA, const PriceLevel& levelB) {
    // Compare based on price, followed by quantity
    if (levelA.price < levelB.price)
        return -1;
    else if (levelA.price > levelB.price)
        return 1;
    else if (levelA.quantity < levelB.quantity)
        return -1;
    else if (levelA.quantity > levelB.quantity)
        return 1;
    else
        return 0;
}

// Comparison function for std::sort (adapted from C)
inline static bool compare_levels_c(const PriceLevel& levelA, const PriceLevel& levelB) {
    return compare_levels_int(levelA, levelB) < 0;
}

extern "C" {
    void sort_price_levels_c_cpp(PriceLevel* data, size_t len) {
        std::sort(data, data + len, compare_levels_c);
    }
}
```
As we can see, `compare_levels_int` is an almost direct translation of the `compare_levels` function
in `sort.c`, except we leave out the `void*` fiddling. Sticking this in the benchmark is as easy as
adding the following to `src/lib.rs`:
```rust
// --- snip ---

extern "C" {
    // --- snip ---
    pub fn sort_price_levels_c_cpp(data: *mut PriceLevel, len: usize);
    // --- snip ---
}

#[cfg(test)]
mod test {
    use super::*;
    // --- snip ---
    #[test]
    fn c_cpp_sort() {
        unsafe { sorting_test(sort_price_levels_c_cpp) }
    }
    // --- snip ---
}
```
and the following new benchmark to `benches/sorting.rs`:
```rust
pub fn criterion_benchmark(c: &mut Criterion) {
    // --- snip ---
    c.bench_function("sort c cpp", |b| {
        b.iter(|| unsafe { benchmark_sorter(sort_price_levels_c_cpp, &mut buf, &mut rng) })
    });
    // --- snip ---
}
```
Re-running our benchmarks, we obtain
```
sort c                  time:   [385.94 µs 385.98 µs 386.03 µs]

sort cpp                time:   [193.41 µs 193.67 µs 194.16 µs]                     

sort c cpp              time:   [219.83 µs 219.97 µs 220.09 µs]    

sort rust               time:   [192.35 µs 192.37 µs 192.38 µs]
```
As we can see, while the C-style comparator is slower than the original C++ (and, more
interestingly, slower than the similar Rust comparator), it’s still much faster than the actual C
code. So it’s not the comparator... what’s going on, then?

## Inlining 101

At this point, it makes sense to dig into the assembly to get an idea of what’s going on. So let’s
fire up [Compiler Explorer](https://godbolt.org/) and begin with our [C
code](https://godbolt.org/z/3Mjs4ch7P). Using clang 16.0.0 with optimization level -O3, we get the
following assembly:
```asm
sort_price_levels_c:                    # @sort_price_levels_c
        lea     rcx, [rip + compare_levels]
        mov     edx, 16
        jmp     qsort@PLT                       # TAILCALL
compare_levels:                         # @compare_levels
        mov     ecx, dword ptr [rsi]
        mov     eax, -1
        cmp     dword ptr [rdi], ecx
        jb      .LBB1_4
        mov     eax, 1
        ja      .LBB1_4
        mov     ecx, dword ptr [rsi + 4]
        mov     eax, -1
        cmp     dword ptr [rdi + 4], ecx
        jb      .LBB1_4
        seta    al
        movzx   eax, al
.LBB1_4:
        ret
```
As we can see, it looks like a pretty direct translation of the input source code: it defines a
function `compare_levels`, and, in `sort_price_levels_c`, just tail-calls `qsort` with a pointer to
`compare_levels` shoved into the appropriate register.

And therein lies our performance problem: it means that for every comparison, we not only need to
call a function pointer (already problematic), but that the sorting function has in no way been
optimized for the type of comparison being done. This means that while binary size will be nice and
small, performance won’t exactly be the best.

Now let’s take a look at our [C++](https://godbolt.org/z/YzqrWfbK7) and
[Rust](https://godbolt.org/z/oa4q7PYoW) assembly, with similar compiler settings. It's unpleasant to
look at, so I’m not going to copy it in here. But it is pleasant to run!

So what’s the difference? Well in both C++ and Rust, the sorting functions we used were generic:
they take in a datatype and comparison implementation, and, for each set of input parameters, are
_monomorphized_ into a completely separate function. This function can then be optimized taking into
account the particular characteristics of the data type and comparison method used, most
importantly, the comparison function used can be _inlined_, both removing function call overhead and
enabling further optimization.

## Better Benchmarking

There’s a serious issue with this benchmark: the data is completely unrealistic: both prices and
quantities are simply random u32s, which not only leads to unrealistic values, but means it’s quite
unlikely that two price levels having the same price will be generated[^8], let alone two price
levels with the same price and quantity[^9] but potentially different order and exchange IDs.

To make this slightly more realistic, let’s write a new benchmark which generates random prices and
quantities between 0 and 99. We just need to add the following to benches/sorting.rs:
```rust
// --- snip ---

pub fn criterion_benchmark(c: &mut Criterion) {
    // --- snip ---
    c.bench_function("sort clamped c", |b| {
        b.iter(|| unsafe { benchmark_clamped_sorter(sort_price_levels_c, &mut buf, &mut rng) })
    });
    c.bench_function("sort clamped cpp", |b| {
        b.iter(|| unsafe { benchmark_clamped_sorter(sort_price_levels_cpp, &mut buf, &mut rng) })
    });
    c.bench_function("sort clamped c cpp", |b| {
        b.iter(|| unsafe { benchmark_clamped_sorter(sort_price_levels_c_cpp, &mut buf, &mut rng) })
    });
    c.bench_function("sort clamped rust", |b| {
        b.iter(|| unsafe { benchmark_clamped_sorter(sort_price_levels_rust, &mut buf, &mut rng) })
    });
}

// --- snip ---

unsafe fn benchmark_clamped_sorter(
    sorter: unsafe extern "C" fn(*mut PriceLevel, usize),
    buf: &mut Vec<PriceLevel>,
    rng: &mut impl Rng,
) {
    buf.clear();
    buf.extend((0..BENCHMARK_LEN).map(|_| PriceLevel {
        price: rng.gen::<u32>() % 100,
        quantity: rng.gen::<u32>() % 100,
        exchange_id: rng.gen(),
        order_id: rng.gen(),
    }));
    unsafe { sorter(buf.as_mut_ptr(), BENCHMARK_LEN) }
    for i in 1..BENCHMARK_LEN {
        assert!((buf[i - 1].price, buf[i - 1].quantity) <= (buf[i].price, buf[i].quantity))
    }
}
```
Running our benchmarks again, we obtain
```
sort c                  time:   [386.22 µs 386.28 µs 386.35 µs]                   

sort cpp                time:   [193.35 µs 193.38 µs 193.41 µs]                     

sort c cpp              time:   [218.47 µs 218.52 µs 218.57 µs]                       

sort rust               time:   [192.55 µs 192.61 µs 192.70 µs]                      

sort clamped c          time:   [420.81 µs 420.90 µs 421.00 µs]                           

sort clamped cpp        time:   [240.43 µs 240.50 µs 240.57 µs]                             

sort clamped c cpp      time:   [265.13 µs 265.17 µs 265.21 µs]                               

sort clamped rust       time:   [203.35 µs 203.42 µs 203.51 µs]        
```
We see that the data follows roughly the same pattern as before, though performance is overall
worse. Interestingly, Rust now performs better than C++. More importantly, however, we can conclude
our performance differences are not _completely_ dependent on the structure of our benchmark.

# Conclusion

So what’s the takeaway here? Well, of the three languages tested, C is often considered the “lowest
level”, yet C is the _slowest_. However, this doesn’t have to be the case: I could instantiate the
special-cased code the C++ or Rust compilers would generate manually in C myself and have code that
performs the same (or even better, if I proceed to further optimize it by hand!) than either of the
original solutions. The question is, will I? And the answer is probably no, for a variety of
reasons:

- This sorting operation is unlikely to be the bottleneck of my application
- Manually instantiating a sorting algorithm is going to take far more time, and Googling, than just
  using the standard library
- There’s a far higher chance of bugs, and the code is much less readable. Especially for trading
  code, simple bugs in something like a sorting algorithm [can _really_
  hurt](https://web.archive.org/web/20221027164429/https://lucisqr.substack.com/p/the-blowout-of-knight-capital).

In short, while, I can hand-optimize performance bottlenecks I’ve discovered via profiling, but the
baseline performance of my application will often be determined by the performance of, well,
_everything_. The overall quality of that “everything,” then, as well as the architecture I choose
to organize it, is heavily influenced by my choice of language _and by the ecosystem of libraries
available in that language_. It’s very much like the [Sapir-Whorf
hypothesis](https://en.wikipedia.org/wiki/Linguistic_relativity), but for code: some languages just
make fast code more natural to write.

[^1]: See the [benchmarks
    game](https://benchmarksgame-team.pages.debian.net/benchmarksgame/index.html) for fun examples

[^2]: Of course, the same program compiled by different compilers can also vary in performance. That
    said, different compilers for the same language (e.g. GCC vs clang vs MSVC) tend to have much
    closer performance to each other than to compilers for different languages (e.g. GHC), which
    tells us at least that programming language design has an impact on how easy it is to write a
    good compiler. 

[^3]: I am reminded of this [Stack Overflow
    post](https://stackoverflow.com/questions/40354978/why-does-c-code-for-testing-the-collatz-conjecture-run-faster-than-hand-writte),
    in which a questioner is confused that their assembly code is slower than an equivalent C++
    program, the aforementioned assembly being completely unoptimized (a 64-bit division instruction
    was used to divide by 2).

[^4]: Note, in particular, especially since everything is going through FFI and all the compilers
    we’ll be using are LLVM-based, each of Rust, C, or C++ should be theoretically able to express
    equivalent solutions to this problem. Hence, what we're testing here is which solutions are most
    _natural_ to express.

[^5]: Some call it “decorating,” but it’s not pretty.

[^6]: Unlike C, Rust does not have a stable ABI. As for C++,
    [well...](https://stackoverflow.com/questions/67839008/please-explain-the-c-abi)

[^7]: All benchmarks are extracted from separate runs of an executable containing all final
    benchmarks on my desktop (an Intel Core i9-9900-KF running Linux).

 <!-- TODO: fix unicode escape expected nonsense -->

[^8]: Due to the [birthday paradox](https://en.wikipedia.org/wiki/Birthday_problem), the probability
    is 
    $$ 
    p_{\text{collision}} \approx \frac{n_{\text{samples}}^2}{2n_{\text{prices}}} = \frac{4096^2}{2 \cdot 2^{32}} \approx 0.19\% 
    $$ 
    which, while low, is a lot higher than you’d expect considering we’re dealing
    with 4294967296 distinct possible prices.

[^9]: Which would have a probability of
    $$ 
    p_{\text{collision}} \approx \frac{4096^2}{2 \cdot 2^{64}} \approx 4.5 \cdot 10^{-13} 
    $$
    For comparison, let's say I've uniformly selected a person on Earth. Assuming there's
    about 8 billion people on Earth, and that the person chosen is equally likely to be born on
    any given day, your chance of guessing who I've selected, and simultaneously guessing their 
    birthday, is about the same: 
    $$ 
    \frac{1}{8000000000} \cdot \frac{1}{365} \approx 3.4 \cdot 10^{-13} 
    $$