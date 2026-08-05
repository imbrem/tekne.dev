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

- The set of functions $f : \nats \to \mb{2}$ 
  taking each natural number $n \in \nats$ 
  to a boolean $b \in \{0, 1\}$

- The set of (infinite) bitstreams 011000111...
  -- we might write this 
  
  - $\mb{2}^\nats$ (since function types are exponential objects) 
  
  - $\mb{2}^\omega$ (invoking cardinalities)
  
  - $\mb{2}^*$ (invoking regular expressions)

- The set of all subsets of $\nats$, $\mc{P}(\nats)$[^0]

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

More formally, we want to show that there's no _surjection_ 
$F: \nats \to (\nats \to \mb{2})$
-- i.e., no function $F$ such that 

1. for all functions $f \in \nats \to \mb{2}$ (i.e. for all bitstreams)

2. there exists at least one $i \in \nats$ such that $F(i) = f$

i.e. where every bitstream $f$ appears in $F$ when visualized as a table.

We call a set $A$ which can't be numbered 
-- i.e., one in which there is no surjection $f: \nats \to A$
-- _uncountable_ -- since we call a set which _can_ be numbered _countable_.

We now get to the proof of Cantor's Theorem: 
we show that $\nats \to \mb{2}$ is uncountable by _diagonalization_:

1. Assume we are given an _arbitrary_ function $F : \nats \to (\nats \to \mb{2})$
   -- we wish to show $F$ is not a surjection

2. Consider the function
    $$
        g(i) = \lnot F(i)(i)
    $$
    where $\lnot b$ denotes the _logical negation_ of the bit $b$
    -- i.e. $\lnot 0 = 1$ and $\lnot 1 = 0$.

3.  We have that, for all $i \in \nats$,
    $F(i)(i) = \lnot g(i) \neq g(i)$,
    and hence $F(i) \neq g$
    
4. Therefore, there is no $i$ such that $F(i) = g$ 
    -- and hence $F$ cannot be a surjection

The reason the above proof technique is called _diagonalization_ is because
we construct $g$ by flipping each bit on the *diagonal* of 
$F$ -- as visualized below:

| id | bits                                                         |
|----|--------------------------------------------------------------|
| 0: | `- 0 -`11011000110000101110010011100100111100100100000011100000... |
| 1: | 1`- 1 -`0000101110101011011000111001101101111011011100010000001... |
| 2: | 11`- 0 -`111011000010111001100100000011100100110100101100111011... |
| 3: | 010`- 0 -`00111010000000000000000000000000000000000000000000000... |
| 4: | ...                                                          |

One nice thing about the proof above is it works just as well for 
arbitrary sets $A$. Let's repeat it to see what I mean:

_Theorem_ (Cantor): For any set $A$, 
there is no surjection $F : A \to (A \to \mb{2})$.

1. Assume we are given an _arbitrary_ function $F : A \to (A \to \mb{2})$
   -- we wish to show $F$ is not a surjection

2. Consider the function
    $$
        g(i) = \lnot F(i)(i)
    $$
    where $\lnot b$ denotes the _logical negation_ of the bit $b$
    -- i.e. $\lnot 0 = 1$ and $\lnot 1 = 0$.

3.  We have that, for all $i \in A$,
    $F(i)(i) = \lnot g(i) \neq g(i)$,
    and hence $F(i) \neq g$
    
4. Therefore, there is no $i$ such that $F(i) = g$ 
    -- and hence $F$ cannot be a surjection

It follows that, for an _arbitrary_ set $A$, there is no surjection 
$F : A \to (A \to \mb{2})$.

In general, we say that the _cardinality_ of a set $A$ is 
_greater than or equal to_ than that of a set $B$ 
if there exists a surjection
$A \to B$ -- we write this as $|A| \geq |B|$.

For more intuition on why this definition works, see [^1].

In particular, if there does _not_ exist a surjection from $A \to B$, 
we write
$$
|A| < |B| := \lnot (|A| \geq |B|)
$$

This induces a _preorder_[^2] on the cardinalities of sets, 
with some useful properties:

- $|A| \leq |B| := |B| \geq |A|$ iff there exists an _injection_ $f : A \to B$
  -- i.e., a function $f$ such that
  $\forall a_1, a_2 . f(a_1) = f(a_2) \implies a_1 = a_2$
  
  -- this is due to the [Schröder–Bernstein theorem](https://en.wikipedia.org/wiki/Schr%C3%B6der%E2%80%93Bernstein_theorem)

- For any sets $A, B$, either $|A| \leq |B|$ or $|B| \leq |A|$ 
  -- i.e., the cardinality order is _total_

- $|A| < |B|$ iff there is no injection $|B| \to |A|$

- $|A| = |B| := (|A| \leq |B|) \land (|B| \leq |A|)$
  iff there exists a _bijection_ $f : A \to B$
  -- i.e. a function $f$ which equivalently:

  - is both an injection and a surjection

  - has an inverse $f^{-1} : B \to A$ such that

    - $\forall a \in A, f^{-1}(f(a)) = a$ -- i.e. $f ; f^{-1} = \ms{id}_A$
    
    - $\forall b \in B, f(f^{-1}(b)) = b$ -- i.e. $f^{-1} ; f = \ms{id}_B$

In particular, we may hence state Cantor's Theorem as follows:

_Theorem_ (Cantor): For any set $A$, $|A| < |\mc{P}(A)|$

We say a set $A$ is _finite_ 
if and only if one of the following equivalent conditions holds:

1. $\exists k \in \nats . |A| = |\ms{Fin}(k)|$ where 
   $\ms{Fin}(k) := \{n \mid n < k\}$ 
  -- in which case we abuse notation and write $|A| = k$
  -- i.e. $A$ contains exactly $k$ elements

2. $|A| < \nats$ -- i.e.

3. There is no surjection $A \to \nats$

4. There is no injection $A \to \nats$

5. Every injection $A \to A$ is a surjection

We'll call a class of sets of the same size a _cardinal_
-- hence, 
the _smallest_ cardinal is the class of sets which are in bijection with $\nats$
-- $\aleph_0 := |\nats|$.

Likewise, we can define the basic operations of _cardinal arithmetic_ as follows:

- $|B|^{|A|} := |A \to B|$ -- and hence in particular $2^{|A|} := |\mc{P}(A)|$

  Note that
  $$
  |\ms{Fin}(b)|^{|\ms{Fin}(a)|} 
  = |\ms{Fin}(a) \to \ms{Fin}(b)| 
  = |\ms{Fin}(b^a)| 
  = b^a
  $$

- $|A| \cdot |B| := |A \times B|$
  -- where $A \times B$ denotes the _(cartesian) product_ of sets $A, B$
  -- i.e. the set of pairs ${(a, b) \mid a \in A, b \in B}$

  Note that
  $$
  |\ms{Fin}(n)| \cdot |\ms{Fin}(m)|
  = |\ms{Fin}(n) \times \ms{Fin}(m)|
  = |\ms{Fin}(n \cdot m)|
  = n \cdot m
  $$


- $|A| + |B| := |A + B|$ 
  -- where $A + B$ denotes the _coproduct_ or _disjoint union_ of sets $A, B$

  Note that
  $$
  |\ms{Fin}(n)| + |\ms{Fin}(m)| 
  = |\ms{Fin}(n) + \ms{Fin}(m)| 
  = |\ms{Fin}(n + m)|
  = n + m
  $$
Taking the standard definitions 
$\mb{0} := \empty$ and $\mb{1} := \{\ast\}$,
these equip the cardinalities with the structure of a _commutative ordered semiring_ -- i.e. it satisfies

- $|A| + |B| = |B| + |A|$ -- commutativity ($+$)

- $|A| \cdot |B| = |B| \cdot |A|$ -- commutativity ($\cdot$)

- $|A| + (|B| + |C|) = (|A| + |B|) + |C|$ -- associativity ($+$)

- $|A| \cdot (|B| \cdot |C|) = (|A| \cdot |B|) \cdot |C|$ -- associativity ($\cdot$)

- $|A| \cdot (|B| + |C|) = (|A| \cdot |B|) + (|A| \cdot |C|)$ -- distributivity

- $|A| + \mb{0} = |A|$ -- additive identity

- $|A| \cdot \mb{1} = |A|$ -- multiplicative identity

- $|A| \cdot \mb{0} = \mb{0}$ -- multiplicative annihilation

- $|A| \leq |B| \implies |A| + |C| \leq |B| + |C|$ -- monotonicity ($+$)

- $|A| \leq |B| \implies |A| \cdot |C| \leq |B| \cdot |C|$ -- monotonicity ($\cdot$)

as well as the usual arithmetic properties of exponentiation:

- $|A|^{|B| + |C|} = |A|^{|B|} \cdot |A|^{|C|}$

- $|A|^{|B| \cdot |C|} = (|A|^{|B|})^{|C|}$


We say $A$ is _infinite_ if it is not finite
-- or, equivalently, if $|\nats| \leq |A|$.

In particular this $\nats$ is the _smallest_ infinite set
-- and hence that its cardinality 
$\aleph_0 := |\nats|$ is the _smallest_ infinite cardinal.

Some useful properties of infinite cardinals (which are excellent exercises to prove!) include:

- If $\kappa, \lambda$ are cardinals with $\kappa$ infinite, then

  - $\kappa + \lambda = \kappa \cdot \lambda = \max(\kappa, \lambda)$

  - $\kappa^\lambda = \kappa$ if $\lambda < \kappa$

On the other hand 
-- Cantor's theorem implies not only 
that there is an infinite set larger than $\nats$ 
(namely $\mc{P}(\nats)$),
but in fact that there is an infinite _hierarchy_ of ever-larger infinite sets:

$$
\nats, 
\qquad \mc{P}(\nats), 
\qquad \mc{P}(\mc{P}(\nats)), 
\qquad \mc{P}(\mc{P}(\mc{P}(\nats))),
\qquad \ldots
$$

or, by induction,

$$
\ms{Beth}_0 := \nats,
\qquad \ms{Beth}_{n+1} := \mc{P}(\ms{Beth}_n)
$$

and therefore an infinite set of increasing cardinalities[^4]
$$
\beth_n = |\ms{Beth}_n|
$$

or, equivalently, defined by induction

$$
\beth_0 := \aleph_0,
\qquad \beth_{n+1} := 2^{\beth_n}
$$



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

[^0]: In general, 
we can put $\mc{P}(A)$ and $A \to \mb{2}$ in bijection
by mapping:

- A set $S \subseteq A$ to its characteristic function $\chi_S : A \to \mb{2}$ defined by
$$
\chi_S(a) :=
\begin{cases}
1 & \text{if } a \in S \\
0 & \text{if } a \notin S
\end{cases}
$$

- A function $f : A \to \mb{2}$ to the set $S_f := \{ a \in A \mid f(a) = 1\}$

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

[^4]: TODO: add a footnote about $\aleph$ vs. $\beth$ and the [(generalized) continuum hypothesis](https://en.wikipedia.org/wiki/Continuum_hypothesis#Generalized_continuum_hypothesis)