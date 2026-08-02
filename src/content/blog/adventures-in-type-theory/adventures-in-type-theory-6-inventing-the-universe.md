---
title: Adventures in Type Theory 6 -- Inventing the Universe
published: '2026-08-02'
categories: []
series: Adventures in Type Theory
uuid: 69ead7ec-f66c-44ad-9387-146a7ebffd96
---

_Time_: 2026-08-02T15:26Z

_Location_: Westminster, London, United Kingdom

_“If you wish to make an apple pie from scratch, you must first invent the universe.”_ -- Carl Sagan

The proof of Cantor's Theorem by diagonalization is definitely a [proof from THE BOOK](https://en.wikipedia.org/wiki/Proofs_from_THE_BOOK).

We'll begin by recalling a simple exposition of the concrete case for the natural numbers $\nats$
-- adapted from my memory of 
[Faith Ellen](https://www.cs.toronto.edu/~faith/)'s 
[CSC240](https://web.archive.org/web/20161023150544/http://calendar.artsci.utoronto.ca/crs_csc.htm#CSC240H1) lectures at the University of Toronto
-- both to fix notations and to repair the world.

We want to show that the natural numbers $\nats$ is _strictly_ smaller 
than $\nats \to \mb{2}$ .

Recall that $\nats \to \mb{2}$ can equivalently be viewed as:

- The set of functions from $\nats$ to the booleans

- The set of (infinite) bitstreams 011000111...

- The set of all subsets of $\nats$, $\mc{P}(\nats)$

When we say $\nats \to \mb{2}$ is _strictly_ larger than $\nats$, 
what we mean is that there's no way to _number_ the bitstreams[^1]
-- i.e., to put them in a table

| id | bits                                                         |
|----|--------------------------------------------------------------|
| 0: | 011011000110000101110010011100100111100100100000011100000... |
| 1: | 110000101110101011011000111001101101111011011100010000001... |
| 2: | 110111011000010111001100100000011100100110100101100111011... |
| 3: | 010000111010000000000000000000000000000000000000000000000... |
| 4: | ...                                                          |

such that: 

- every bitstream appears in the table _at least_ once  (duplicates are allowed)

- every row has a unique `id` 

We call a set $A$ which can't be numbered _uncountable_
-- since we call a set which _can_ be numbered _countable_.

So the simplest possible statement of Cantor's Theorem is:
_there exists an uncountable set_ --
and we can to prove this by showing that set of bitstreams $\nats \to \mb{2}$
is in fact uncountable -- an example of particular interest to computer scientists.

- TODO: proof by diagonalization

- TODO: some other uncountable sets, comparing the size of sets

    - TODO: pull down comparison footnote[^2] to here when we discuss how to compare the size of sets

- TODO: generalize to $\mc{P}(A)$

- TODO: introduce $\beth$-hierarchy

    - TODO: footnote about $\aleph$-hierarchy?

- TODO: define $\beth_\omega := \sup_{n \in \nats} \beth_n$

- TODO: show $\beth_\omega$ is interesting because 
    it's a semantics for the simply typed lambda calculus with $\nats$
    which doesn't need a typing universe $\mc{U}$

    Use this to define the ring operations on $\beth_\omega$!

    Progression probably looks like:

    1. Define STLC

    2. Give trivial semantics in terms of $\mc{U}$
       -- note that universe level is irritating 
       since it means type semantics 
       $\ms{Ty} \to \mc{U}_\ell$ must live in $\mc{U}_{\ell + 1}$
       -- which causes pain

       - Let's also consider (to demonstrate, perhaps):

            - simple generics

            - higher-kinded types

            - staged lambda calculi?

    3. If we don't have a $\nats$ type, 
       we can encode our _semantic_ types as subsets of $\nats$
       -- something something "domain"

       We can define a structure like a universe by

       - taking a semiring + exponentiation

       - giving it a map to the universe which

       - respects these operations

       Note:

       - this is just a _concrete CCC!_

    4. If we _do_ have a $\nats$ type,
       how can we encode our types?

       As subsets of $\beth_\omega$, naturally!

        - Let's also consider:

            - `bool` vs. `coprod` 

            - Least Fixpoints $\mu$

            - Greatest Fixpoints $\nu$

- TODO: so now, consider HOL

    - Without $\nats$ -- finite model theory, lives in $\nats$

    - With $\nats$ -- good-old-fashioned HOL, lives in $\beth_\omega$

- TODO: interesting question for future exploration -- what about: 
    - MLTT?
    - MLTT with a single typing universe $\mc{U}$?

- TODO: but now, what about -- HOL-$\omega$?

    - Without $\nats$ -- still finite model theory, lives in $\nats$

    - With $\nats$ -- good-old-fashioned HOL-$\omega$, lives in $\beth_\omega$

- TODO: I like soundness, but what about _completeness_?

    - TODO: is finite-HOL _complete_? I think so -- prove conjecture

    - TODO: _future work_:

        - TODO: for infinite HOL, 
            Gödel's Incompleteness Theorem says we can't do this naively...
            but...

        - TODO: is infinite HOL complete if we add an oracle for:
            
            - $\nats$-sentences?
                My _guess_ is no 
                -- due to problems lifting statements about 
                ($\nats \to \mb{2}$)-sentences -- i.e. about _second order arithmetic_

            - ($\nats \to \mb{2}$)-sentences?
                My _guess_ is no (Copilot fills in "yes")
                -- due to problems lifting statements about 
                ($(\nats \to \mb{2}) \to \mb{2}$)-sentences

            - $\beth_\omega$-sentences?
                My _guess_ is yes
                -- since we match the size of the semantic set.

                This might even be pretty easy,
                depending on our definition of "oracle"

[^1]: This way of comparing sets 
-- by asking whether there exists a surjection from one to another
-- corresponds directly to how we compare the sizes of finite sets
in everyday life.

For example, imagine we had sets
$$
\begin{array}{rl}
\ms{Motorcycles} := &
\{
    \text{``KTM 125 Duke"}, 
    \text{``Kawasaki Z650"}, 
    \text{``Suzuki Gladius 650"}
\} \\
\ms{Parking} := &
\{
    \text{``William Gates Building"},
    \text{``Parking Spot 6789"}
\}
\end{array}
$$
there are (at least) _as many_ motorcycles as parking locations
-- a fact we can constructively exhibit 
by providing the following table the _witness_:

| motorcycle | parking |
|-|-|
| KTM 125 Duke | Parking Spot 6789 |
| Kawasaki Z650 | William Gates Building |
| Suzuki Gladius 650 | William Gates Building |

That is: 
there is some way to park each motorcycle so that each parking spot
contains at least one motorcycle.

We'll write this as
$$
|\ms{Parking}| \leq |\ms{Motorcycles}|
$$

On the other hand, there are _not as many_ parking locations as motorcycles
-- to see this, 
it suffices to show that
we can't build a table which maps every parking spot to its unique occupant,
since

| parking | motorcycle |
|-|-|
| William Gates Building | (Motorcycle #1) |
| Parking Spot 6789 | (Motorcycle #2) |

can only ever cover two motorcycles 
-- so there can't be as many parking locations as motorcycles
-- that is:

$$
\lnot (|\ms{Motorcycles}| \leq |\ms{Parking}|)
$$

We can therefore say there are _strictly more_ 
motorcycles than parking locations 
-- which we'll write
$$
|\ms{Parking}| < |\ms{Motorcycles}|
$$
since

- There are as many motorcycles as parking locations 
  -- $|\ms{Motorcycles}| \leq |\ms{Parking}|$, and

- There are not as many parking locations as motorcycles
  -- $\lnot (|\ms{Motorcycles}| \leq |\ms{Parking}|)$

That is -- when comparing the cardinalities of sets $A, B$, we define[^3]

$$
|A| < |B| := (|A| \leq |B|) \land \lnot (|B| \leq |A|)
$$

It turns out that, to deduce that $|A| < |B|$,
it is sufficient to prove that $\lnot (|B| \leq |A|)$:
as may be expected given our experience with finite sets,
if there are not as many elements of $B$ as there are elements of $A$, 
then there must be as many elements of $A$ as there are elements of $B$.

For arbitrary sets, 
this is a consequence that the cardinality order is a _total preorder_[^2] 
-- a fact which follows from the [Schröder–Bernstein theorem](https://en.wikipedia.org/wiki/Schr%C3%B6der%E2%80%93Bernstein_theorem)

[^2]: This is the standard definition for $<$ in a preorder[^3] $\leq$
 -- see e.g. the Mathlib definition for 
 [`Preorder`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/PartialOrder.html#Preorder),
 which requires axiom 
 [`lt_iff_le_not_ge`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/PartialOrder.html#Preorder.lt_iff_le_not_ge).

[^3]: A _preorder_ is a binary relation $\leq$ which is:

- Reflexive: $\forall a . a \leq a$ 
  -- that is, every element is less than or equal to itself

- Transitive: $\forall a, b, c . (a \leq b) \implies (b \leq c) \implies (a \leq c)$ -- that is, 
    1. if $a$ is less than or equal to $b$, 
    2. then whenever $b$ is less than or equal to $c$, 
    3. $a$ must also be less than or equal to $c$.
 
The comparison relation $\leq$ 
on the natural numbers $\nats$ are an everyday example of a preorder 
which is in fact a _total order_ since it is:

- Antisymmetric: $\forall a, b . (a \leq b) \land (b \leq a) \implies a = b$
  -- in general, a preorder which is antisymmetric is called a _partial order_

- Total: $\forall a, b . (a \leq b) \lor (b \leq a)$

On the other hand -- the cardinality order 
$(|\cdot| \leq |\cdot|)$
on sets is _not_ a partial order, since, 
$$
|\{\text{``a"}, \text{``b"}, \text{``c"}\}| = |\{1, 2, 3\}|
$$
-- that is,
$$
|\{\text{``a"}, \text{``b"}, \text{``c"}\}| \leq |\{1, 2, 3\}|
\land
|\{1, 2, 3\}| \leq |\{\text{``a"}, \text{``b"}, \text{``c"}\}|
$$
but
$$
|\{\text{``a"}, \text{``b"}, \text{``c"}\}| \neq |\{1, 2, 3\}|
$$

However, as a consequence of the [Schröder–Bernstein theorem](https://en.wikipedia.org/wiki/Schr%C3%B6der%E2%80%93Bernstein_theorem), it _is_ total,
making it a _total preorder_.