---
title: Towards An Inductive Representation of SSA
published: '2024-07-15'
---

[Static Single Assignment form](https://en.wikipedia.org/wiki/Static_single-assignment_form), or
SSA, is the intermediate representation of choice for designing compilers for a vast variety of
languages and platforms. This article consists of some brief notes on how one might represent SSA
effectively inside a theorem prover, such as [Lean](https://lean-lang.org/), with a view towards
proving the correctness of rewrites and optimization passes. In particular, we will cover the story
of the [debruijn-ssa](https://github.com/imbrem/debruijn-ssa) project so far and some of the
tradeoffs and design decisions made within, starting from our original
[freyd-ssa](https://github.com/imbrem/freyd-ssa) formalization project.

## Classical SSA

We begin by telling the story of [freyd-ssa](https://github.com/imbrem/freyd-ssa), our attempt to
formalize classical SSA mostly as is and prove some theorems. This is still very work-in-progress
and mostly abandoned, but it is `sorry`-free, and while it does not by any means follow best
practices, designing it was very educational in figuring out what a good representation of SSA for
use in theorem proving should look like. In general, this section should also lay out the
terminology we will be using when talking about SSA in the rest of this article.

### A Type System for 3-address code

In _3 address code_, a program is decomposed into a _control-flow graph_ made up of _basic blocks_.
For example, this:
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
    ite (i < q) ^exit ^body
^body:
    i = i + 1; 
    t = i + c;
    p = p + t;
    ite (p % 3) ^tt ^head
^tt:
    p = p + 2;
    br ^head
^exit:
    ret p
```
A _basic block_ is defined as a linear sequence of _instructions_, the _body_, followed by a
_terminator_, which either returns or jumps to the next basic block in program execution. 

More formally, let's consider instructions $f: A_1 \times ... \times A_n \to B_1 \times ... \times
B_m$ taking in $n$ parameters $a_1,...,a_n$ and returning $m$ outputs of type $B_1,..., B_m$. For
convenience, we will simply write such bundles of parameters as $f : (A_i)_i \to (B_j)_j$.

We might begin a formal account of three-address code by defining the following typing judgement for
a **body**:

$$
\boxed{\Gamma \vdash b : \Delta}
$$

This says that if the variables in the context $\Gamma$ are live on input to $b$, then the variables
in the context $\Delta$ will be live once the instructions in $b$ are finished executing. 

**TODO: put drawing here**

A **context**, for now, will just be a (finitely-supported) partial function from variables to
types; the domain of this function is our _live variable set_.

We can give typing rules

$$
\frac{\Gamma \leq \Delta}{\Gamma \vdash \cdot : \Delta}
\qquad \qquad
\frac
    {
        \forall i, \Gamma(x_i) = A_i \quad f : (A_i)_i \to (B_j)_j 
        \quad \Gamma, (y_j : B_j)_j \vdash b : \Delta
    }{
        \Gamma \vdash \mathsf{let}\;(y_j)_j = f (a_i)_i;\; b : \Delta
    }
$$

Let's break this down:
- $\Gamma \leq \Delta$ denotes that $\Gamma$ _weakens_ $\Delta$, i.e., that if $\Gamma(x) = A$, then
    $\Delta(x) = A$. So the first rule says that the empty body, $\cdot$, which just does nothing,
    is allowed to throw away unused live variables in the input, but that's it.
- $\Gamma, x: A$ denotes updating $\Gamma(x)$ to $A$ (whether or not it was previously defined). So
    the second rule says that if $b$ takes inputs $\Gamma, (y_j : B_j)_j$ to $\Delta$, then first
    updating $(y_j)_j$ to be the outputs of $f (x_i)_i$ and then executing $b$ takes $\Gamma$ to 
    $\Delta$, assuming that $\Gamma$ types each $x_i$ correctly to be an input of $f$.

A **basic block**, given a set of live variables on input, executes its body and then jumps to
another basic block via its **terminator** (for simplicity, we can model returns as jumping to a
special "return" label). We might represent this using the judgement

$$
\boxed{\Gamma \vdash \beta : \mathcal{L}} 
$$

Just like before, $\Gamma$ is the set of live variables on entry to the basic block $\beta$. On the
other hand, $\mathcal{L}$ is a **label context**: a finitely supported map from **labels** $\ell$ to
contexts $\Gamma$, which represent the variables which must be live on entry to $\ell$.

TODO: insert picture here

We might give the following simple typing rules for basic blocks

$$
\frac
    {\Gamma \vdash b : \Delta \qquad \Delta \leq \mathcal{L}(\ell)}
    {\Gamma \vdash b ; \mathsf{br}\;\ell \rhd \mathcal{L}}
\qquad
\frac
    {\Gamma \vdash b : \Delta 
        \qquad \Delta(b) = \mathbf{2} 
        \qquad \Delta \leq \mathcal{L}(\ell), \mathcal{L}(\ell')}
    {\Gamma \vdash b ; \mathsf{ite}\;b\;\ell\;\ell' \rhd \mathcal{L}}
$$

TODO: Explanation

The astute reader might notice that it would be perfectly equivalent, up to isomorphism, to elide
the syntactic category of bodies altogether, and give typing rules for basic blocks as follows:

$$
\frac
    {\Gamma \leq \mathcal{L}(\ell)}
    {\Gamma \vdash \mathsf{br}\;\ell \rhd \mathcal{L}}
\qquad
\frac
    {\Gamma(b) = \mathbf{2} 
        \qquad \Gamma \leq \mathcal{L}(\ell), \mathcal{L}(\ell')}
    {\Gamma \vdash \mathsf{ite}\;b\;\ell\;\ell' \rhd \mathcal{L}}
\qquad
\frac
    {
        \forall i, \Gamma(x_i) = A_i \quad f : (A_i)_i \to (B_j)_j 
        \quad \Gamma, (y_j : B_j)_j \vdash b \rhd \mathcal{L}
    }{
        \Gamma \vdash \mathsf{let}\;(y_j)_j = f (a_i)_i;\; \beta \rhd \mathcal{L}
    }
$$

It can often be useful to switch between these two ways of reasoning about basic blocks, as we will
see throughout this article.

Finally, a **control-flow graph** $G$ can be viewed as a set of mutually-recursive basic blocks
taking a label context of entry points $\mathcal{L}$ to a label context of exit points
$\mathcal{K}$, as in the following picture:

TODO: insert picture here


Representing $G$ as a finitely-supported map from labels $\ell$ to basic blocks $\beta$, the
judgement for this might look like the following:

$$
\boxed{\mathcal{L} \vdash G \rhd \mathcal{K}}
$$

with a typing rule of the form

$$
\frac{\exists \mathcal{R} \geq \mathcal{L}, [\forall \ell \in G, 
    \mathcal{R}(\ell) \vdash G(\ell) \rhd \mathcal{R}] 
    \land [\forall \ell \in \mathcal{R}, \ell \notin G 
        \implies \mathcal{R}(\ell) \leq \mathcal{K}(\ell)]}
    {\mathcal{L} \vdash G \rhd \mathcal{K}}
$$

This rule is a bit complex, so let's break it down:
- The existential... Here, $\mathcal{L}$ weakens $\mathcal{R}$ when...
- The first $\forall$...
- The second $\forall$...

In particular, we can break this into two rules by defining $\mathcal{R} \vdash' G \rhd \mathcal{K}$
as follows:

$$
\frac{[\forall \ell \in G, \mathcal{R}(\ell) \vdash G(\ell) \rhd \mathcal{R}] 
    \land [\forall \ell \in \mathcal{R}, \ell \notin G 
        \implies \mathcal{R}(\ell) \leq \mathcal{K}(\ell)]}{\mathcal{R} \vdash' G \rhd \mathcal{K}}
\qquad
\frac{\mathcal{L} \leq \mathcal{R} \qquad \mathcal{R} \vdash' G \rhd \mathcal{K}}
     {\mathcal{L} \vdash G \rhd \mathcal{K}}
$$


#### A Note on Scoping

Note that every well-typed program in the above system never uses a variable in an ill-typed way,
including using a variable before it has been initialized with a value of the appropriate type,
assuming that all live variables are so initialized (uninitialized values, of course, can be
simulated by initializing with `undef` or similar). But our type system is necessarily conservative;
there are some programs with this property that are nevertheless ill-typed, such as
```
^entry:
    br p ^left ^right
^left:
    x = 5
    br ^exit
^right:
    x = "hello"
    br ^exit
^exit:
    x = 3 + x
    ...
```
where `p` is known to be `true`. This in general raises the question of what system of scoping we
can use to describe what programs we accept as well-formed in perhaps a more intuitive manner. This
is slightly difficult when the types of variables are allowed to change, as in the above language,
but a program with SSA form does not have this issue, allowing us to trivially introduce _dominance
tree based scoping_, which we will do in later sections as part of our quest for an inductive
representation of SSA.

### SSA

We can now define _SSA form_ as a property of 3-address code: a piece of 3-address code is said to
be in _SSA form_ if every variable is assigned to exactly once. 

Conversion to SSA form, for straight-line code, is just variable renaming: 
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
y0`, for example, whereas previously we would have to keep control-flow in mind. In general, the
ability to analyze the previous values of variables, and do algebra with them, makes a huge class
of analysis passes and optimizations _much_ easier to implement.

In the presence of branching, however, converting to SSA gets a bit more complicated: given
```
^entry:
    x = 5;
    ite p ^left ^right
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
    ite p ^left ^right
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
    ite p ^left ^right
^left:
    x1 = 3 + x0
    br ^end(x1)
^right: 
    x2 = 4
    br ^end(x2)
^end(x3):
    x4 = 3 + x3?
```

To take into account parameters, we can change our definition of label contexts to map labels $\ell$
to pairs $(\Gamma, (A_i)_i)$ of contexts $\Gamma$ and tuples of parameters $A_i$.

We might then modify our typing judgement for blocks as follows:

$$
\frac
    {\Gamma \vdash b : \Delta 
        \qquad (\Delta, (A_i)_i) \leq \mathcal{L}(\ell) 
        \qquad \forall i, \Delta(x_i) = A_i}
    {\Gamma \vdash b ; \mathsf{br}\;\ell\;(a_i)_i \rhd \mathcal{L}}
\qquad
\frac
    {\Gamma \vdash b : \Delta 
        \qquad \Delta(b) = \mathbf{2} 
        \qquad \Delta \leq \mathcal{L}(\ell), \mathcal{L}(\ell')}
    {\Gamma \vdash b ; \mathsf{ite}\;b\;\ell\;\ell' \rhd \mathcal{L}}
$$

Here, we define $(\Gamma, (A_i)_i) \leq (\Delta, (B_i)_i) \iff \Gamma \leq \Delta \land \forall i,
A_i = B_i$.

Similarly, control flow graphs must be modified to map labels $\ell$ to pairs $((x_i)_i, \beta)$ of
fresh variable names $x_i$ and basic blocks $\beta$.[^2]

The typing rule then looks roughly like:

$$
\frac{[\forall (\ell, (x_i)_i, \beta) \in G, 
    \mathcal{R}(\ell) = (\Gamma, (A_i)_i) \land \Gamma, (x_i : A_i)_i \vdash \beta \rhd \mathcal{R}] 
    \land [\forall \ell \in \mathcal{R}, 
        \ell \notin G \implies \mathcal{R}(\ell) \leq \mathcal{K}(\ell)]}
    {\mathcal{R} \vdash' G \rhd \mathcal{K}}
\qquad
\frac{\mathcal{L} \leq \mathcal{R} \qquad \mathcal{R} \vdash' G \rhd \mathcal{K}}
    {\mathcal{L} \vdash G \rhd \mathcal{K}}
$$

Note that these typing rules are still for 3-address code (extended with basic block parameters),
and well-typed programs do not necessarily have to be in SSA.

[^1]: Traditionally, this is implemented using a
    [Φ-node](https://www.llvmpy.org/llvmpy-doc/dev/doc/llvm_concepts.html) to carry the argument,
    but this is isomorphic to the more modern basic-blocks-with-arguments approach.

[^2]: In reality, dealing with freshness is quite complicated, but can be done

### Formalizing Substitution

At this stage, we can define a predicate determining whether a program is in SSA form quite easily:
all we need to do is check that for every basic block $\Gamma, (x_i : A_i)_i \vdash \beta \rhd
\mathcal{L}$, $\beta$ does _not_ overwrite any variables which were live on input to $\beta$, i.e.,
in $\Gamma$ or $\{x_i\}$. What we now want is to _use_ SSA form to prove some useful properties
about programs. Unfortunately, writing down equations for SSA is still somewhat painful in our
setting. For example:
- Propagating a constant binding $\mathsf{let}\;x = c$ knowing that $x$ is not redefined is sound
  (the program being in SSA implying _no_ variable is redefined), since constants cannot appear as
  arguments to functions in our simple grammar, we need to instead create many constant bindings
  $\mathsf{let}\;x_u = c;$ for each use $u$ of $x$ we want to replace, which at least temporarily
  just seems to make our program more complicated. We also, of course, need to deal with fresh
  variables.
- We have to suffer a bit to perform algebraic optimizations such as simplifying $x = y -
  5; z = x + 5$ to $x = y - 5; z = x$, since we cannot directly rename variables.
- We don't know which operations we can safely substitute: an `add` is fine, but a call to
  `print` isn't... and oftentimes, neither is a `div` due to risk of undefined behaviour on division
  by zero.
- We might want to detect more complicated multi-layer patterns, using advanced techniques such as
  E-graph rewriting

In short, introducing instructions is a pain, and matching patterns of pure operations is a pain.
This in particular makes writing a formal substitution theorem a pain. To address this, we can
introduce a simple _expression language_, to replace operations, having the following typing
judgement

$$
\boxed{\Gamma \vdash_\epsilon a : A}
$$

In particular, to effectively deal with multiple return values, we can simply ban them and instead
introduce product types $(A_1 \times ... \times A_n)$, which we will write $\Pi_i A_i$. We also
_annotate_ each expression with an effect $\epsilon$. In general, our effects form a lattice, but
for now, it is enough to consider pure expressions with effect $\bot$ and impure expressions with
effect $\top$. Finally, we can annotate our contexts with effects $\epsilon$ for each variable, to
allow reasoning about impure rewrites.

We then obtain typing rules:

$$
\frac{\Gamma(x) \leq (A, \epsilon)}{\Gamma \vdash_\epsilon x : A}
\qquad
\frac{\forall i, \Gamma \vdash_\epsilon a_i : A_i}{\Gamma \vdash_\epsilon (a_i)_i : \Pi_iA_i}
\qquad
\frac{f : A \to_\epsilon B \qquad \Gamma \vdash_\epsilon a : A}{\Gamma \vdash_\epsilon f\;a : B}
$$
In particular, constants can be modeled as functions from $\mathbf{1} = \Pi[]$ to $C$.

Now, all that is necessary is to modify our typing judgement for bodies to differentiate between
binding a variable and unpacking:

$$
\frac{\Gamma \leq \Delta}{\Gamma \vdash \cdot : \Delta}
\qquad \qquad
\frac
    {
        \forall i, \Gamma(x_i) = A_i \quad f : (A_i)_i \to (B_j)_j 
        \quad \Gamma, (y_j : B_j)_j \vdash b : \Delta
    }{
        \Gamma \vdash \mathsf{let}\;(y_j)_j = f (a_i)_i;\; b : \Delta
    }
$$

and our judgement for blocks and control-flow graphs to deal with the fact that only single 
arguments are now permitted

$$
\frac
    {\Gamma \vdash b : \Delta 
        \qquad (\Delta, A) \leq \mathcal{L}(\ell) 
        \qquad \Delta(x) = A}
    {\Gamma \vdash b ; \mathsf{br}\;\ell\;a \rhd \mathcal{L}}
\qquad
\frac
    {\Gamma \vdash b : \Delta 
        \qquad \Delta(b) = \mathbf{2} 
        \qquad \Delta \leq \mathcal{L}(\ell), \mathcal{L}(\ell')}
    {\Gamma \vdash b ; \mathsf{ite}\;b\;\ell\;\ell' \rhd \mathcal{L}}
$$

where, of course, label contexts $\mathcal{L}$ are now mappings $\ell \to (\Gamma, A)$.


Note that this is isomorphic to our original system: we can simply, always choosing fresh variables,
perform rewrites like
$$
\mathsf{let}\;x = y; \beta \to [y/x]\beta \qquad
\mathsf{let}\;(x_i)_i = (a_i)_i; \beta \to (\mathsf{let}\;x_i = a_i)_i; \beta;
$$
to obtain a program performing only unpackings of operations, just like was originally permitted.[^3]

[^3]: Note, that when not using the fused body-block typing rules, we define $\mathsf{let}\;x = y;
    (b; t) = (\mathsf{let}\;x = y;b); t$

We have now obtained a system which is essentially the same as that formalized in
[freyd-ssa](https://github.com/imbrem/freyd-ssa), except for the following details:
- For simplicity, we only define pairs of types $A \times B$, and an explicit unary type
  $\mathbf{1}$; these can simulate $n$-ary pairs $\Pi_i A_i$ by defining, e.g., $\Pi_{i = 1}^nA_i =
  A_1 \times \Pi_{i = 2}A_i$
- Similarly, we append an explicit Boolean type $\mathbf{2}$ for if-then-else rewrites
- Our rules for CFGs are a little bit more convoluted: we define $\mathcal{L} \vdash' G \rhd
  \mathcal{K}$ using the following much less intuitive rules:
  
  $$
  \frac{}{\mathcal{L} \vdash' \cdot \rhd \mathcal{L}} \qquad
  \frac{
    \mathcal{L} \vdash' G \rhd \mathcal{K}, (\ell \mapsto \Gamma, A) \quad
    \ell \notin \mathcal{K} \quad
    \Gamma, x : A \vdash \beta \rhd \mathcal{L} \quad
    \mathcal{L} \vdash' G, \ell(x) \Rightarrow \beta \rhd \mathcal{K}
    }{} \qquad
  \frac{\mathcal{L} \vdash' G \rhd \mathcal{K}, \quad \ell \notin \mathcal{L}}
        {\mathcal{L} \vdash' G \rhd \mathcal{K}, (\ell \mapsto \Gamma, A)}
  $$

  The reason for this had to do with wanting a more inductive semantics; in retrospect, I can't
  think of why exactly we went for this this at the moment, but that's what was formalized and we
  have to be honest! This also provides a bit more power, since "dead" code, i.e. $\ell$ not
  reachable from the entry context, does not need to typecheck.

The main theorem in this development is _substitution_: given a finitely supported map $\sigma$ from
a variables to terms and a label context $\mathcal{L}'$ with the same labels and parameters as
$\mathcal{L}$ (but not necessarily the same associated contexts!), if
 
$$
\forall (\ell, \Delta, A) \in \mathcal{L}, 
    \mathcal{L}'(\ell) = (\Gamma, A) \land
    \forall x,
    \Delta(x) = (B, \epsilon) \implies
    \Gamma \vdash_\epsilon \sigma(x) : B
$$

and the CFG $G$ is in SSA, then the obvious substitution

$$
\mathcal{L}' \vdash' [\sigma]G \rhd \mathcal{K}'
$$

is well-typed, where $\mathcal{K}'$ denotes $\mathcal{L}'$ restricted to the support of
$\mathcal{K}$.

That's powerful, and allows a lot of reasoning about rewriting. On paper, we also show that given
our semantics, every _pure_ such substitution is _sound_, i.e. semantics preserving, where a
substitution is pure if all $\sigma(x) \neq x$ can be typed with effect $\bot$. It's also
_incredibly_ cumbersome to state, and even more difficult to use. And hence the beginning of the
quest for an inductive definition of SSA, where hopefully we can actually state more complicated
optimizations, such as control-flow rewrites, in a more convenient fashion.

### Alternative Design: Global Label/Variable Name Maps

One alternative point in the design space is to have a global map $\Gamma$ from variable names to
types and a global map $\mathcal{L}$ from labels to parameter types which we can type programs with
respect to. Combinators can be used to combine programs while maintaining freshness at a global
level (say, by using integer indices and storing names only as metadata). This presents various
difficulties w.r.t scoping, but provides a natural setting to state many analyses, such as some
dataflow passes. We have not yet explored this portion of the design space.

## Explicit Scoping and De-Bruijn Indices

- Want a sane way to do induction on programs, decomposing them into smaller pieces
- Want to know exactly what is in scope at any given point
- These are related problems
- Let's think carefully about [dominator
  trees](https://en.wikipedia.org/wiki/Dominator_(graph_theory))...
- Bracketing determines variable scoping
- This is _because_ bracketing determines label scoping

### Formal Typing Rules

- Operations
- Bodies
- Blocks
- Terminators
- _Regions_

### Adding Cases

- Why
- Pls trust me categories good enums good

### De-Bruijn Indices

- So we can introduce de-Bruijn indices for variables...
- And for labels too!
- But we'll write our typing rules with names, for now!

### How to Recover SSA

- Erase the brackets: no more regions
- Some notes on what we want to allow as terminators
- We want cases for Reasons (TM)... this will be important later...

### Formalization

- This is the `BBRegion` data structure in [debruijn-ssa](https://github.com/imbrem/debruijn-ssa);
  see also `Block`, `Body`, `Terminator`. We use `Term` rather than operations or expressions,
  though; see `Term` and cases

### Removing Bodies

- Operations
- Terminators
- Regions
- This gives us the `TRegion` data structure; but again see `Term` and cases

### How to Recover SSA

- Every region has a _distinguished_ entry body/block: can trivially be extracted by induction
- Just make it and go inductively!

## Structured Branching Control-Flow

- MLIR supports it!
- Let's start by generalizing terms

### Formal Typing Rules

- Terms

### Why Introduce a Term Language

- Many rewrite reasons
- But!

### Fusing Regions and Terminators

- Recovering SSA is a tad ugly
- Mutual induction: very sad :(
- Can fix that by merging things!

### Formal Typing Rules

- Operators
- Regions

### How to Recover SSA

- Can now use ye olde rewrite rules nicely
- Can just send to nested CFGs for sharing purposes, recovering old ugly rules

### Alternative Design: overloaded `br`

- Closer to MLIR, maybe?
- Much simpler to explain: `br` to a branch
- _But_: more painful for expressing certain !FUN! rewrite rules
- _Also_: actually, more painful to lower, too
- And introduces spurious basic blocks jumping straight to control flow, very sad...

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