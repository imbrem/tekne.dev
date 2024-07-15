---
title: An Inductive Representation of SSA
published: '2024-07-15'
---

[Static Single Assignment form](https://en.wikipedia.org/wiki/Static_single-assignment_form), or
SSA, is the intermediate representation of choice for designing compilers for a vast variety of
languages and platforms. This article consists of some brief notes on how one might represent SSA
effectively inside a theorem prover, such as [Lean](https://lean-lang.org/), with a view towards
proving the correctness of rewrites and optimization passes. In particular, we will cover the data
structures formalized in the [debruijn-ssa](https://github.com/imbrem/debruijn-ssa) repository and
some of the tradeoffs and design decisions made within.

- Research context; category theory
- Warnings
- Skip for final rules

<!-- More interestingly, the [MLIR](https://mlir.llvm.org/) project aims
 to formulate SSA as a re-usable data structure. This data structure is parametrized by _dialects_,
 which provide instructions (including control-flow primitives) which satisfy _interfaces_ telling
 optimization passes how they may be manipulated, allowing optimization passes to work with a wide
 variety of different dialects all from different groups of authors. This enables, in theory,
 various interoperable applications and extensions such as [automatic
 differentiation](https://enzyme.mit.edu/), [hardware design](https://circt.llvm.org/), and, of
 course, [quantum
 computing](https://docs.pennylane.ai/projects/catalyst/en/latest/modules/mlir.html) to evolve
 concurrently within an integrated ecosystem. But it also hints that SSA... -->

## Classical SSA

### 3-address code

- Function-by-function
- A function is a control-flow graph
- A CFG is made of basic blocks
- A basic block is made of _instructions_, and is followed by a _terminator_
- Fun question: undefined variables?

<img src={basic_blocks}/>


### SSA

- Can be viewed as a property of 3-address code: each variable is defined exactly once
- so basic blocks need parameters
- scoping is complicated, and based on _dominator trees_

### Formalization

- Go link to [freyd-ssa](https://github.com/imbrem/freyd-ssa)

## Inductive SSA

### Explicit Scoping

- Want a sane way to do induction on programs, decomposing them into smaller pieces
- Want to know exactly what is in scope at any given point
- These are related problems
- Let's think carefully about dominator trees...
- Bracketing determines variable scoping
- This is _because_ bracketing determines label scoping

### De-Bruijn Indices

- So we can introduce de-Bruijn indices for variables...
- And for labels too!
- But we'll write our typing rules with names, for now!

### Formal Typing Rules

- Operations
- Bodies
- Blocks
- Terminators
- _Regions_

### How to Recover SSA

- Erase the brackets: no more regions
- Some notes on what we want to allow as terminators
- We want cases for Reasons (TM)... this will be important later...

### Formalization

- This is the `BBRegion` data structure in [debruijn-ssa](https://github.com/imbrem/debruijn-ssa);
  see also `Block`, `Body`, `Terminator`. We use `Term` rather than operations or expressions,
  though; see `Term` section.

## Induction Instruction-By-Instruction

- Problem: lots of things, lots of inductions
- Pros and cons
- Want to reason instruction-by-instruction? Hard. Separate layers for everything!
- Can remove bodies and blocks to alleviate this...

### Formal Typing Rules

- Operations
- Terminators
- Regions

### How to Recover SSA

- Every region has a _distinguished_ entry body/block: can trivially be extracted by induction
- Just make it and go inductively!

## Basic Structured Control-Flow

- MLIR supports it!
- Not too complicated, just stick regions in the terminators...
- But just a tiny bit harder to explain...

### Formal Typing Rules

- Operations
- Terminators
- Regions

### How to Recover SSA

- Rough translation to single-terminator is pretty simple; you nest CFGs for sharing purposes

### Formalization

- This is the `TRegion` data structure in [debruijn-ssa](https://github.com/imbrem/debruijn-ssa)

## Fusing Regions and Terminators

- Mutual induction: very sad :(
- Some duplication now with case appearing twice...
- Can fix that by merging things!

### Formal Typing Rules

- Operators
- Regions

### How to Recover SSA

- Can just send to nested CFGs for sharing purposes

### Alternative Design: overloaded `br`

- Closer to MLIR, maybe?
- Much simpler to explain: `br` to a branch
- _But_: more painful for expressing certain !FUN! rewrite rules
- _Also_: actually, more painful to lower, too
- And introduces spurious basic blocks jumping straight to control flow, very sad...

## Introducing a Term Language

- Want to express:
- Splitting an instruction into multiple
- Fusing instructions
- Etc etc...
- Really, _substitution_ as a generalization of constant propagation
- Also want control-flow in here

### Formal Typing Rules

- Terms
- Regions

### How to Recover SSA

- Ye Olde Rewrite Rules

### Formalization

- This is the Region data structure in [debruijn-ssa](https://github.com/imbrem/debruijn-ssa)

## Next Steps

- Giving an equational theory
- Connecting to categorical semantics

## Future Work

### Linearity

- Working on prototype
- Have old name-based version

### Fusing Terms and Regions

- Cool idea!
- Allows advanced structured control flow, e.g. a `for` instruction like MLIR
- Easier to work with than SSA, maybe
- Effective effect handlers, maybe
- Once this paper is done...

<script>
    import basic_blocks from "$lib/assets/inductive-ssa/basic_blocks.svg"
</script>