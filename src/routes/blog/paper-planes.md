---
title: Adventures in Type Theory 5 — Paper Planes
published: '2025-10-07'
---

_Time_: 2025-10-07T21:36Z

_Location_: High above a vast, fractured disc of light, wreathed in subtle glowing mist. #PC5170

Let's recap the story of our POPL submission. We develop λiter: the standard `WHILE` imperatibe
language recast as an expression language, with the obvious grammar:
```text
a, b, c ::= | x         # variables
            | f a       # instructions
            | (a, b)    # pairs
            | ()        # unit
            | ι₁ a      # left injection
            | ι₂ a      # right injection
            # case expressions
            | case a (ι₁ x => b) (ι₂ y => c) 
            | abort a   # empty type elim
            # iteration expressions
            | iter a (ι₂ x => b)
```
In particular, note that:
- We emulate `n`-tuples with nullary and binary tuples
    - A zero-tuple is `()`
    - A one-tuple is just `a`
    - An `n + 1`-tuple is `(a, t)`, where `t` is an `n`-tuple. 
      Of course, we can just as well recurse on the left.
- Likewise, instructions are always unary; an `n`-ary instruction is just a unary instruction taking
  an `n`-tuple. In particular, a constant `c` is a nullary instruction `c ()`
- We use `case` rather than `if`; an `if`-statement is a `case` on `1 + 1`
- Likewise than iterate using a loop of the form `do { body } while P`, we have an iteration
  expresion `iter a (ι₂ x => b)`.
  
  Semantically, this evalutes an expression `b` with a hole of type `A` to produce an expression of
  type `B + A`, and recurses on the left.

  This of course requires us to provide an initial value `a : A`.

  We also provide an eliminator `abort` for the empty type.

Now, this is basically a direct syntactic translation of an Elgot category. We tell the story of how
λssa, a lexically scoped version of SSA, is in bijection with λiter up to a complete set of directed
rewrite rules, giving a complete theory of substructural SSA. We then give a few models, for good
measure.

The issue with this, and with our TOPLAS submission, is that it's _very_ hard to get this story to
_bite_. _Why_ all this is useful is buried under piles of technical jargon, that I myself had to
wade through for quite a while before believing my _own_ work is useful. So how can I expect the
poor reviewer to do so?

Moreover, the major achievements of the paper are technical, with the concepts (_purposefully_) very
familiar. For example, the coherence theorem for λiter in the presence of substructural types,
formalized in Lean 4, is thousands of lines of rewriting of Elgot categories, which required
extensive experimentation with formalization techniques and encodings of premonoidal categories in
Lean 4. But both the statement and use of the theorem are trivial: "it doesn't matter what the
derivation is, as long as there is one."

A big reason that these theorems were as difficult to prove as they were was that we simultaneously
were developing a somewhat novel semantic setting to deal with general _substructural_ types, rather
than the usual intuitionistic types (which live in a Freyd category) or linear types (which live in
a general symmetric monoidal category). So we had to figure out not only how to do rewriting in the
setting where copy-delete structure is tied to types rather than natural on objects, _but_ the
things we had to rewrite were themselves more complex since context-splitting was no longer a simple
duplication of the context's denotation `⟦Γ⟧` but rather a complex usage-sensitive assembly of
drops, duplications, left moves and right moves which we had to prove _irrelevant_ (i.e., whichever
one you use, you'll get the same answer, as long as its valid). That's hard when the results don't
have the same type, in general.

Another major, related issue was that our treatment of λssa was very rushed; it turns out that
cleanly generalizing the work in our TOPLAS submission to the substructural setting is hard. It
generalizes, but our label-contexts become quantity-annotated messes.

Neel and I are hopefully going to upload what we have soon to the arXiv, so I can stick a link here.
But for PLDI, we need to rework our narrative.

And I've been thinking. Thankfully, I just cannot sleep on a plane.

Those were two big design choices, there:

- Make the type system _fully_ substructural, in that types could be substructural too. This didn't
  make the rules for λiter that much more complicated, but dramatically increased the complexity of
  both the semantics and both the rules and _judgements_ for λssa

- Make our syntax highly regular, and in particular, choose binary-nullary encodings for both
  products and coproducts, in the spirit of
  `HasFiniteProducts`-is-`HasBinaryProducts`-and-`HasTerminalObject`.

These both had reasons, and were not _bad_ choices per-se, but they complicated things, and are also
farther from traditional SSA.

And moreover, farther from MLIR. And that's where a lot of the interest is!

MLIR is theoretically very interesting because they give a _framework_ for using _dialects_ of
(generalized) SSA to tackle problems. All kinds of problems!

- Classical compilation problems; MLIR is a dialect!

- Code-generation problems; RISC-V is a dialect with and without instructions!

- Machine-learning problems; tensor operations are a dialect!

- Meta-problems: function definitions and even MLIR dialects are themselves a dialect; features like
  _graph regions_ let us tackle problems which the standard SSACFG MLIR regions are ill-equipped to
  represent

- Exciting, experimental problems like Ye Olde Weird Quantum Stuff and hardware synthesis

So... one language, which seems to be able to be equipped with a lot of different domain-specific
models.

Yet, MLIR allows these different languages to _share_ optimizations and analysis passes, as well as
provide a standard way of reasoning about and transforming programs both within a dialect and in
general. In particular,

- We can annotate instructions in a dialect with _traits_, like commutativity, which tell us how we
  can optimize them

- We can use a set of dialect-specific valid _rewriting rules_, such as `n + 0 = n`

- We can traverse over the MLIR data-structure itself, telling us that lots of problems can be
  naturally (or at least _usefully_) structured in an MLIR-friendly format

- We can mix our specific dialect and its specific instructions with general control-flow and
  data-flow primitives with well-understood behaviour, for things like:

  - Structured control-flow (if-statements, while-loops, and for-loops can all be instructions!)

  - Unstructured control-flow (SSACFG regions with unstructured branch instructions)

  - Vectorization and pairing

- We can relate dialects to each other, and in particular have _lowering_ and _legalization_ passes
  operating on dialects and mixes-of-dialects.

The point is MLIR sounds a lot like what Neel would call a _domain nonspecific language_, which is
what we are most interested in researching. 

I, a brash youngling, simply go ahead and call it a _category_.

Let's spend some time thinking about what a functional specification of a fragment of MLIR might
look like.

## Regions

The classical definition of a _region_ in a control-flow graph $G$ is a _single-entry, single-exit_
or _SESE region_: a cluster of nodes $N$ with a distinguished entry node $e_{in}$ and exit node
$e_{out}$. The idea is that:

- Every path in the control-flow graph touching $n ∈ N$ must go through the entry node $e_{in}$

- Before we leave $N$, we must go through $e_{out}$, and, in particular

- Every (normally) _terminating_ path in the control-flow graph (i.e. we return) must go through the
  exit node $e_{out}$

If we represent returning by jumping to a distinguished, global exit node $E_{out}$, and we have the
usual single entry point to the function $E_{in}$, then this is like a little fractal sub-function,
we could even _outline_ it into a separate function, if we were desperate to reduce code-size.

This is what LLVM's good old fashioned [region
pass](https://llvm.org/docs/Passes.html#regions-detect-single-entry-single-exit-regions) computes.

But we often want multiple exit points. And we might even want some of those exit points to be
within $N$.

So what about a _single-entry, multiple-exit_ or _SEME region_? It's quite a bit simpler: just a
cluster of nodes $N$ with entry node $e$ such that $e$ _dominates_ $N$; i.e., condition 1 above:

- Every path in the control-flow graph touching $n ∈ N$ must go through the entry node $e$

In particular, the _dominance tree_ of a CFG $G$ splits up $G$ into subregions; each subtree is
precisely a subregion with the root as entry node.

If you read this blog, or have spent any amount of time talking to me, you've probably heard me
explain this a billion times now, with varying degrees of coherence.

The reason why this was important for my _papers_ is that this lets us lexically scope SSA: build a
tree of regions and scope with those. It's still SSA, because the dominance tree establishes an
isomorphism up to topological sort, and the order of blocks in a CFG should not affect its
semantics.

But why is this important for MLIR. MLIR still uses dominance-based scoping, after all, yet it
nevertheless introduces nested structure based on regions. So what gives?

Well, remember our typing judgement for regions,
$$
Γ ⊢ r \rhd \mathsf{L}
$$
Took a while for Neel to learn to love contexts on both sides.

So that's a context because we want to support weakening and label-substitution, two powerful
workhorses of optimization. But if we don't care about that, well... it's basically a type.

I mean, semantically, 
<!--  -->
$$ 
⟦Γ ⊢ a : A⟧ : ⟦Γ⟧ → ⟦A⟧ \qquad ⟦Γ ⊢ r \rhd \mathsf{L}⟧ : ⟦Γ⟧ → ⟦\mathsf{L}⟧
$$ 
<!--  -->
They're of the same sort. In fact, the difference is the type is just slightly more _general_, since
$⟦\mathsf{L}⟧$ needs a $0$ on the LHS of the sum if we're being strict.

So... that means we _might_ be able to treat regions like values.

In fact, with $n$-ary products to destructure the binder $x$, regions _could_ look a lot like the
$(λx . a)$ expressions that show up all throughout our proof of completeness in the POPL
submission's appendix, except with more general control-flow...

Which are of course just open terms in the locally-nameless tradition. Things of type `Tm 1`, or, if
we go $n$-ary, `Tm n`.

What this is hinting at is my hypothesis that:

- We can support instructions which parametrize by regions

- We can do this _without_ changing our underlying semantics; in particular, we don't _in general_
  need higher order structures.

So, why do we care? Well,

- Everyone believes MLIR is SSA, because lots of SSA things like LLVM are just MLIR SSACFG dialects

- So if we model MLIR using regions...

- And we model the expression-ified version of this, which I conjecture is just terms with $n$-ary
  `Tm 1` term-with-hole arguments to instructions...

Then we can tell our story like we're categorically modelling the soundness of

- Directed dialect-specific rewrites

- Traits on instructions in a dialect

We might also ask questions about the semantics of:

- Mixtures of dialects

- Translations and lowerings between dialects

- Dialects supporting structured vs. unstructured control-flow

Though I have spent a lot of time thinking about graph regions, we want to restrict our attention to
SSACFG regions for now, since the semantics of the former are _complex_.

I've tried this many times before, of course. But I think there's both a story here and an exciting
locally-nameless formalization. But I need to figure out what it is, and I've got 11% battery
remaining...

A possible sketch of what this might look like is:

- Figure out λiter-with-region-parameters (λiter' for now); again; I'm thinking $n$ `Tm 0`
  parameters and $k$ `Tm 1` parameters. Formalize the _syntax_ in Lean.

- Figure out the appropriate rewrite rules, which modulo instructions should be the same.
  
  Go and formalize these, and some of their basic properties.

- Figure out λssa-with-region-parameters (λmlir?), and formalize this syntax too.

  Try to formalize the isomorphism with λiter'. Time permitting, formalize isomorphisms with other
  syntactic forms, too.

- Do soundness and completeness proofs, and semantics, _on paper_.

This avoids spending months on completeness proofs (a talk with Vikraman, and a great Attitude
Adjustment, shifted my philosophy on this), hopefully, since the meat should be the same as before,
while making sure that neither our syntax, isomorphisms, or type-systems are ill-defined since those
are properly formalized.

With the power of Locally Nameless, we can also hope to

- Write down and formalize the exact same things; named calculus is now just syntax sugar. This is
  important for a paper-Lean hybrid work.

- Actually get a usable rewriting theory, hopefully, maybe. Please no de-Bruijn shuffling...

- Be able to use this theory to reason about symbolic equality of programs in Lean, which by faith
  in paper become real equalities in category land, without needing to wait on mathlib landing
  premonoidal support or using `discretion` and associated hax. That fight goes on...

But now, back to the task at hand: putting together a decent presentation for HOPE.