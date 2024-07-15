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

## Classical SSA

We will begin with a brief overview of what SSA is usually taken to mean, to compare and contrast
with our various inductive definitions.

### 3-address code

In _3 address code_, a program is decomposed into a _control-flow graph_ made up of _basic blocks_,
defined as a segment of code such that all instructions except the first have a single predecessor,
and all instructions except the last have a single successor. This last instruction is called the
_terminator_, and is responsible for returning from the function or jumping to the next basic block,
as appropriate. For example, the program
```c
int f(int a, int b, int c) {
    int p = a + 5;
    int q = b + p;
    for (int i = 0; i < q; i++) {
        p += i + c;
        if (p % 3 == 0) {
            p += 2;
        }
    }
    return p;
}
```
might become
```
^entry:
    p = a + 5;
    q = b + p;
    i = 0;
    br ^head
^head:
    cond_br (i < q) ^exit ^body
^body:
    i = i + 1; 
    t = i + c;
    p = p + t;
    cond_br (p % 3) ^tt ^head
^tt:
    p = p + 2;
    br ^head
^exit:
    ret p
```

### SSA

3-address code is said to be in _SSA form_ if every variable is assigned to exactly once. Conversion
to SSA form, for straight-line code, is just variable renaming: 
```
x = x + 3;
y = x + 2;
x = 3 + y;
y = x + y;
```
becomes 
```
x1 = x0 + 3;
y0 = x1 + 2;
x2 = 3 + y0;
y1 = x2 + y0;
```
This property allows for _substitution_: we can safely substitute all occurences of `x2` with `3 +
y0`, for example, whereas previously we would have to keep control-flow in mind. In the presence of
branching, however, converting to SSA gets a bit more complicated: given
```
^entry:
    x = 5;
    cond_br p ^left ^right
^left:
    x = 3 + x
    br ^end
^right: 
    x = 4
    br ^end
^end:
    x = 3 + x
```
trying to simply number our variables leaves us with the following:
```
^entry:
    x0 = 5;    
    cond_br p ^left ^right
^left:
    x1 = 3 + x0
    br ^end
^right: 
    x2 = 4
    br ^end
^end:
    x3 = 3 + x?
```
In particular, it is dependent on control-flow whether `x1` or `x2` is used in the definition of
`x3`. The solution to this issue is to introduce _parameters_ for basic blocks, as follows [^1]
```
^entry:
    x0 = 5;    
    cond_br p ^left ^right
^left:
    x1 = 3 + x0
    br ^end(x1)
^right: 
    x2 = 4
    br ^end(x2)
^end(x3):
    x4 = 3 + x3?
```

[^1]: Traditionally, this is implemented using a
    [Φ-node](https://www.llvmpy.org/llvmpy-doc/dev/doc/llvm_concepts.html) to carry the argument,
    but this is isomorphic to the more modern basic-blocks-with-arguments approach.

### Formalization

It is possible, though cumbersome, to formalize three-address code using names for both labels and
variables; a work in progress formalization can be found at
[freyd-ssa](https://github.com/imbrem/freyd-ssa).

- TODO: note binary vs. n-ary syntax...

- TODO: ite vs case

- TODO: what is a typing context?

- TODO: state actual judgement, $\Gamma$ is live variables, effect $\epsilon$...

We begin by defining _expressions_ inductively as follows:
$$
\frac{\Gamma \leq x : A_\epsilon}{\Gamma \vdash x : A_\epsilon} \qquad
\frac{
    f : A \to_\epsilon B \quad 
    \Gamma \vdash a : A_\epsilon}
    {\Gamma \vdash f\;a : B_\epsilon} \qquad
\frac
    {\forall i, \Gamma \vdash a_i : (A_i)_\epsilon}
    {\Gamma \vdash (a_1,...,a_n) : (A_1 \times ... \times A_n)_\epsilon}
$$

- TODO: note slightly generalizes operations in 3-address code; allows to state substitution more
    easily, and is also cleaner

- TODO: bodies, judgement is live variables $\Gamma$ on input to $\Delta$ on output...

$$
\frac{\Gamma \leq \Delta}{\Gamma \vdash \cdot : \Delta} \qquad
\frac
    {\Gamma \vdash a : A_\epsilon \quad \Gamma, x: A_\bot \vdash b : \Delta}
    {\Gamma \vdash \mathsf{let}\;x = a; b : \Delta} \qquad
\frac
    {\Gamma \vdash a : (A_1 \times ... \times A_n)_\epsilon \quad 
    \Gamma, x_1 : (A_1)_\bot,..., x_n : (A_n)_\bot \vdash b : \Delta}
    {\Gamma \vdash \mathsf{let}\;(x_1,...,x_n) = a; b : \Delta}
$$

- TODO: weakening $\Gamma \leq \Delta$

- TODO: terminators, judgement is live variables $\Gamma$ on input to targets $L$ on output...

$$
\frac
    {\Gamma \vdash a : A_\bot \quad \ell[\Gamma](A) \leq L}
    {\Gamma \vdash \mathsf{br}\;\ell\;a \rhd L}
\qquad
\frac
    {\Gamma \vdash e : (A + B)_\bot \quad \Gamma, x : A_\bot \vdash s \rhd L 
    \quad \Gamma, y : B_\bot \vdash t \rhd L}
    {\Gamma \vdash \mathsf{case}\;e\;(x \Rightarrow s)\;(y \Rightarrow t) \rhd L}
$$

- TODO: blocks, which is a body and a terminator

$$
\frac{\Gamma \vdash b : \Delta \quad \Gamma \vdash t \rhd L}{\Gamma \vdash b; t \rhd L}
$$

- CFGs: which is inputs to outputs

$$
\frac{...}{...}
$$

A substitution theorem can be stated and proved, but fiddling with names is quite painful!

- TODO: only pure substitutions are valid

## Inductive SSA

### Explicit Scoping

- Want a sane way to do induction on programs, decomposing them into smaller pieces
- Want to know exactly what is in scope at any given point
- These are related problems
- Let's think carefully about [dominator
  trees](https://en.wikipedia.org/wiki/Dominator_(graph_theory))...
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