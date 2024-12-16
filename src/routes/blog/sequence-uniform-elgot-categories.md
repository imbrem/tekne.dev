---
title: Sequence-Uniform Elgot Categories
published: '2024-12-16'
---

A lot of my research focuses on giving categorical semantics to imperative, rather than functional,
computations. Taking inspiration from Levy and Goncharov's paper [_Coinductive Resumption Monads:
Guarded Iterative and Guarded
Elgot_](https://drops.dagstuhl.de/storage/00lipics/lipics-vol139-calco2019/LIPIcs.CALCO.2019.13/LIPIcs.CALCO.2019.13.pdf),
I use what I call Elgot categories to give a complete categorical semantics for SSA in my arXiv
preprint [_The Denotational Semantics of SSA_](https://arxiv.org/abs/2411.09347). I realized I
needed to write down some of my musings about what compiler optimizations we can justify using these
and related gadgets, so here goes.

Consider a category $\mathcal{C}$ equipped with coproducts. We say $\mathcal{C}$ is _pre-iterative_
if it is equipped with an iteration operator $(\cdot)^\dagger$ taking morphisms $f : C \to B + C$ to
their fixpoints $f^\dagger : C \to B$ satisfying the _fixpoint axiom_

$$
f^\dagger = f ; [\mathsf{id}, f^\dagger]
$$

For the programmers in the audience, we can think of the sum type $B + C$ in the target of `f` as
corresponding to Rust's [`ControlFlow<B,
C>`](https://doc.rust-lang.org/std/ops/enum.ControlFlow.html#variant.Continue) type, which has the
intuitively named variants

- `Continue(C)`: perform another iteration with data `C`
- `Break(B)`: return early with value `B`

These conveniently integrate with Rust's try-operator `?` such that `Continue(c)?` evaluates to `c`,
while `Break(b)?` immediately returns `Break(b)`. We're going to abuse syntax and allow `Break(b)?`
to just return `b`, as well.

The iteration operator then is just a way to turn a function `f : C -> ControlFlow<B, C>` to a
function `iterate(f) : C -> B` satisfying the following program equivalence:

```rust
return iterate(f)(c)
===
match f(c) { 
    Break(b) => return b, 
    Continue(c) => return iterate(f)(c) 
}
```
With our syntax abuse, we can write this more concisely as
```rust
let c = f(c)?;
return iterate(f)(c)
```

This hints that we can express iteration at a given point as follows:
```rust
return iterate(f)(a)
===
let mut x = a;
loop {
    match f(x) {
        Break(b) => return b,
        Continue(a) => x = a 
    }
}
===
let mut x = a;
loop {
    x = f(x)?;
}
```

We'll call this iteration operator a _Conway iteration operator_ if, additionally, it satisfies
- _Naturality_: given $f : A \to B + A$ and $g : B \to C$, we have
    $$
    (f ; g + B)^\dagger = f^\dagger ; g
    $$
    i.e., the fact that
    ```rust
    let mut x = a;
    loop {
        match f(x) {
            Break(b) => return g(b),
            Continue(a) => x = a
        }
    }
    ===
    let mut x = a;
    let b = loop {
        match f(x) {
            Break(b) => break b,
            Continue(a) => x = a
        }
    };
    return g(b)
    ```
- _Dinaturality_: given $g : A \to B + C$ and $h : C \to B + A$, we have
    $$
    (g ; [\iota_l, h])^\dagger = g ; [\mathsf{id}, (h; [\iota_l, g])^\dagger]
    $$
    This one makes a lot more sense if we write it as the somewhat convoluted, but, if you squint,
    obviously valid program equivalence
    ```rust
    let mut x = a;
    loop {
        match g(x) {
            Break(b) => return b,
            Continue(c) => match h(c) {
                Break(b) => return b,
                Continue(a) => x = a
            }
        }
    }
    ===
    match g(a) {
        Break(b) => return b,
        Continue(c) => {
            let mut y = c;
            loop {
                match h(y) {
                    Break(b) => return b,
                    Continue(a) => match g(a) {
                        Break(b) => return b,
                        Continue(c) => y = c
                    }
                }
            }
        }
    }
    ```
    This is a bit cleaner if we express it using our abuse-of-?-syntax as follows:
    ```rust
    let mut x = a;
    loop {
        let c = g(x)?;
        x = h(c)?;
    }
    ===
    let mut y = g(a)?;
    loop {
        let a = h(y)?;
        y = g(a)?;
    }
    ```
    It's even cleaner if we write it out as a control-flow diagram, but for now I'm leaving that
    as an exercise to the reader as I've misplaced my graphics tablet.
- _Codiagonal_: given $f : A \to (B + A) + A$, we have
    $$
    (f^\dagger)^\dagger = (f ; [\mathsf{id}, \iota_r])^\dagger
    $$
    i.e. the fact that
    ```rust
    let mut x = a;
    loop {
        let mut y = x;
        match loop {
            match f(y) {
                Break(b) => break b,
                Continue(a) => y = a
            }
        } {
            Break(b) => return b,
            Continue(a) => x = a
        }
    }
    ===
    let mut x = a;
    loop {
        match f(x) {
            Break(Break(b)) => return b,
            Break(Continue(a)) 
            | Continue(a) => x = a
        }
    }
    ```

If we have a category with such an operator, we can reason about iteration (the operator also needs
to be _strong_ to play nice with variables, but we don't need to worry about this for now)

- TODO: $\mathcal{K}$-uniformity

- TODO: explain uniformity, "printing is not uniform"

- TODO: uniformity on inj+, codiagonal, naturality $\implies$ dinaturality

- TODO: sequence optimization lore