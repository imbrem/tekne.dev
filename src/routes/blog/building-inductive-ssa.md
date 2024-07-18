---
title: Building An Inductive Representation of SSA
published: '2024-07-15'
---

[Static Single Assignment form](https://en.wikipedia.org/wiki/Static_single-assignment_form), or
SSA, is the intermediate representation of choice for designing compilers for a vast variety of
languages and platforms. SSA, however, is usually cast in a very "imperative" style, making it
difficult to take advantage of functional programming when writing optimizations and analyses, and
extremely cumbersome to reason about effectively in a theorem prover. In this article, we discuss
how we might work towards a more "functional," and in particular _inductive_, representation of SSA.
In particular, we will discuss representations of SSA inside the [Lean](https://lean-lang.org/)
theorem prover which I have developed over the course of my research, from a formalization of
"vanilla" 3-address code and SSA in [freyd-ssa](https://github.com/imbrem/freyd-ssa) to my work on
inductive representations of SSA in [debruijn-ssa](https://github.com/imbrem/debruijn-ssa).

## Classical SSA

We begin by telling the story of [freyd-ssa](https://github.com/imbrem/freyd-ssa), our attempt to
formalize classical SSA mostly as is and prove some theorems. This is still very work-in-progress
and mostly abandoned, but it is `sorry`-free, and while it does not by any means follow best
practices, designing it was very educational in figuring out what a good representation of SSA for
use in theorem proving should look like. In general, this section should also lay out the
terminology we will be using when talking about SSA in the rest of this article.

### A Type System for 3-address code

In _3 address code_, a program is decomposed into a _control-flow graph_ made up of _basic blocks_.
For example, this C program:
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
or, drawn as a graph,

<img src={program_cfg} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="The above program's CFG drawn as a graph">

In general, a program in three-adress code is composed of:
- A **control-flow graph**, composed from a set of entries, exists, and
- **Basic blocks**, which are defined as a linear sequence of **instructions** (the **body**)
  followed by a **terminator**.

More formally, let's consider instructions $f: A_1 \times ... \times A_n \to B_1 \times ... \times
B_m$ taking in $n$ parameters $a_1,...,a_n$ and returning $m$ outputs of type $B_1,..., B_m$. For
convenience, we will simply write such bundles of parameters as $f : (A_i)_i \to (B_j)_j$.

We might begin by giving a typing judgement for **bodies**:

$$
\boxed{\Gamma \vdash b : \Delta}
$$

$\Gamma \vdash b : \Delta$ means that if the variables in the context $\Gamma$ are live on input to
$b$, then the variables in the context $\Delta$ will be live once the instructions in $b$ are
finished executing.

<img src={body_live} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of the live variables on entry and exit to a basic block's body">

Here, a **context** is just a (finitely-supported) partial function from variables to types; the
domain of this function is our _live variable set_.

We can give typing rules

$$
\frac{\Gamma \leq \Delta}{\Gamma \vdash \cdot : \Delta}
\qquad \qquad
\frac
    {
        \forall i. \Gamma(x_i) = A_i \quad f : (A_i)_i \to (B_j)_j 
        \quad \Gamma, (y_j : B_j)_j \vdash b : \Delta
    }{
        \Gamma \vdash \mathsf{let}\;(y_j)_j = f (x_i)_i;\; b : \Delta
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

For a quick sanity check, we can verify that this definition satisfies _weakening_ on both the
left and right:

$$
\frac{\Gamma' \leq \Gamma \quad \Gamma \vdash b : \Delta \quad \Delta \leq \Delta'}
    {\Gamma' \vdash b : \Delta'}
$$

We can also prove a variant of the _frame rule_ (assuming all variables in $\Xi$ are fresh!):

$$
\frac{\Gamma \vdash b : \Delta}{(\Gamma \sqcup \Xi) \vdash b : (\Delta \sqcup \Xi)}
$$

A **basic block**, given a set of live variables on input, executes its body and then jumps to
another basic block via its **terminator** (for simplicity, we can model returns as jumping to a
special "return" label). We might represent this using the judgement

$$
\boxed{\Gamma \vdash \beta : \mathcal{L}} 
$$

Just like before, $\Gamma$ is the set of live variables on entry to the basic block $\beta$. On the
other hand, $\mathcal{L}$ is a **label context**: a finitely supported map from **labels** $\ell$ to
contexts $\Gamma$, which represent the variables which must be live on entry to $\ell$, as below:

<img src={block_live} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of live variables on entry and exit to a basic block">

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

In other words, as one would expect, a basic block consists of a _body_ followed by a _terminator_;
with the latter being either an _unconditional branch_ ($\mathsf{br}$) or a _conditional branch_
($\mathsf{ite}$). The body transforms the variables required live on input, $\Gamma$, into the
variables guaranteed live on output, $\Delta$; the conditions for terminators state that, for all
possible output labels $\ell$, $\Delta$ is a weakening of the variables required for a branch to
that label, that is, $\mathcal{L}(\ell)$

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
        \forall i. \Gamma(x_i) = A_i \quad f : (A_i)_i \to (B_j)_j 
        \quad \Gamma, (y_j : B_j)_j \vdash b \rhd \mathcal{L}
    }{
        \Gamma \vdash \mathsf{let}\;(y_j)_j = f (a_i)_i;\; \beta \rhd \mathcal{L}
    }
$$

It can often be useful to switch between these two ways of reasoning about basic blocks, as we will
see throughout this article.

Similarly, we can sanity-check our typing rules here by making sure weakenings hold. In particular,
we can define 

$$
\mathcal{L} \leq \mathcal{K} 
\iff \forall (\ell, \Gamma) \in \mathcal{L}. \Gamma \leq \mathcal{K}(\ell)
$$

Note that here $\mathcal{K}$ is allowed to have _more_ labels than $\mathcal{L}$ (but not less),
however it must have _less_ variables in the contexts associated with shared labels (whereas labels
not in $\mathcal{L}$ may be mapped to arbitrary contexts!) We then have the following theorem:

$$
\frac{
        \Gamma' \leq \Gamma \quad 
        \Gamma \vdash \beta \rhd \mathcal{L} 
        \quad \mathcal{L} \leq \mathcal{L}'
    }{\Gamma' \vdash \beta \rhd \mathcal{L}'}
$$

Finally, a **control-flow graph** $G$ can be viewed as a set of mutually-recursive basic blocks
taking a label context of entry points $\mathcal{L}$ to a label context of exit points
$\mathcal{K}$, as in the following picture:

<img src={cfg_live} 
    style="max-width:30em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

Representing $G$ as a finitely-supported map from labels $\ell$ to basic blocks $\beta$, the
judgement for this might look like the following:

$$
\boxed{\mathcal{L} \vdash G \rhd \mathcal{K}}
$$

with a typing rule of the form

$$
\frac{
    \mathcal{L} \leq \mathcal{R} \qquad 
    \forall \ell \in G.
        \mathcal{R}(\ell) \vdash G(\ell) \rhd \mathcal{R} \qquad
    \forall \ell \notin G.
        \mathcal{R}(\ell) = \mathcal{K}(\ell)}
    {\mathcal{L} \vdash G \rhd \mathcal{K}}
$$

This rule is a bit complex, so let's break it down:
- We postulate the existence of a _recursive label context_ $\mathcal{R}$ such that:
- $\mathcal{L}$ weakens $\mathcal{R}$, i.e. for every label $\ell \in \mathcal{L}$,
  $\mathcal{L}(\ell) \leq \mathcal{R}(\ell)$. In particular, $\mathcal{R}$ is allowed to map labels
  not in $\mathcal{L}$ to *arbitrary* contexts.
- For every $ℓ$ in $G$, if $\mathcal{R}(\ell)$ are live on entry to $G(\ell)$ then all branches out
  of $G(\ell)$ have the appropriate contexts in $\mathcal{R}$ live.
- For every $ℓ$ in $\mathcal{R}$ not in $G$, $\mathcal{R}(\ell)$ is just a weakening of the
  corresponding output label $\mathcal{K}(\ell)$. Note the rule would be equally powerful if we
  required an equality $\mathcal{R}(\ell) = \mathcal{K}(\ell)$

We can similarly state a weakening lemma

$$
\frac{
        \mathcal{L}' \leq \mathcal{L} \quad 
        \mathcal{L} \vdash G \rhd \mathcal{K} \quad
        \mathcal{K} \leq \mathcal{K}'
    }{
        \mathcal{L}' \vdash G \rhd \mathcal{K}' \quad
    }
$$

and frame rule (assuming all labels in $\mathcal{N}$ are fresh!)

$$
\frac{
    \mathcal{L} \vdash G \rhd \mathcal{K}
}{
    (\mathcal{L} \sqcup \mathcal{N}) \vdash G \rhd (\mathcal{K} \sqcup \mathcal{N})
}
$$

<!-- #### A Note on Scoping

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
representation of SSA. -->

### SSA

So far, our type system and grammar applies to 3-address code in general, rather than SSA
specifically, and in particular much of our semantics work and optimizations work in this setting as
well. We can now define _SSA form_ as a property of 3-address code: a piece of 3-address code is
said to be in _SSA form_ if every variable is assigned to exactly once. 

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

The reason we are interested in SSA is that this property allows for _substitution_: we can safely
substitute all occurences of `x2` with `3 + y0`, for example, whereas previously we would have to
keep control-flow in mind. In general, the ability to analyze the previous values of variables, and
do algebra with them, makes a huge class of analysis passes and optimizations _much_ easier to
implement.

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
`x3`. The solution to this issue is to introduce _parameters_ for basic blocks, as follows
[^1]
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

[^1]: Traditionally, this is implemented using a
    [Φ-node](https://www.llvmpy.org/llvmpy-doc/dev/doc/llvm_concepts.html) to carry the argument,
    but this is isomorphic to the more modern basic-blocks-with-arguments approach.

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
tuples of variable names $(x_i)_i$ and basic blocks $\beta$ parametrized the $x_i$s.

Our typing rule for CFGs then becomes

$$
\frac{
        \forall (\ell, (x_i)_i, \beta) \in G.
            \exists (\Gamma, (A_i)_i) = \mathcal{R}(\ell).
            \Gamma, (x_i : A_i)_i \vdash \beta \rhd \mathcal{R}
        \qquad 
        \forall \ell \notin G. \mathcal{R}(\ell) \leq \mathcal{K}(\ell)
    }
    {\mathcal{R} \vdash' G \rhd \mathcal{K}}
$$

Note that these typing rules are still for 3-address code (extended with basic block parameters),
and well-typed programs do not necessarily have to be in SSA.

### Adding an Expression Language

At this stage, we can define a predicate determining whether a control-flow graph is in SSA form
quite easily: all we need to do is check that for every basic block $\Gamma, (x_i : A_i)_i \vdash
\beta \rhd \mathcal{L}$, $\beta$ does _not_ overwrite any variables which were live on input to
$\beta$, i.e., in $\Gamma$ or $\{x_i\}$. Unfortunately, writing down equations about substitutions
and rewrites, which was the point of moving to SSA in the first place, is still quite a pain in our
setting. For example:
- Propagating a constant binding $\mathsf{let}\;x = c$ knowing that $x$ is not redefined is sound
  (the program being in SSA implying _no_ variable is redefined), since constants cannot appear as
  arguments to functions in our simple grammar, we need to instead create many constant bindings
  $\mathsf{let}\;x_u = c;$ for each use $u$ of $x$ we want to replace, which at least temporarily
  just seems to make our program more complicated. We also, of course, need to deal with fresh
  variables.
- We have to suffer a bit to perform algebraic optimizations such as simplifying $x = y -
  5; z = x + 5$ to $x = y - 5; z = x$, since we cannot directly rename variables.
- We don't know which operations we can safely substitute: an `add` is fine, but a call to `print`
  isn't... and oftentimes, neither is a `div` due to risk of undefined behaviour on division by
  zero.
- We might want to detect more complicated multi-layer patterns, using advanced techniques such as
  E-graph rewriting

In short, introducing instructions is a pain, and matching patterns of pure operations is a pain.
This in particular makes writing a formal substitution theorem a pain. To address this, we can
introduce a simple _expression language_, to replace operations, having the following typing
judgement

$$
\boxed{\Gamma \vdash_\epsilon a : A}
$$

This judgement says that, in the context $\Gamma$, the _expression_ $a$ has type $A$ and _effect_
$\epsilon$.  In general, our effects form a lattice, but for now, it is enough to consider pure
expressions with effect $\bot$ and impure expressions with effect $\top$; only substitutions of the
latter are semantically sound! We will also extend contexts $\Gamma$ to map variables $x$ to pairs
$(A, \epsilon)$ of a type and an effect: this allows us to reason about terms, bodies, blocks, and
CFGs with free variables of impure type, allowing us to reason about the syntactic soundness of
rewrites. [^2]

[^2]: We could also use terms with holes, which are more general, however there are some potential
advantages to supporting _both_.

Note that, to effectively deal with multiple return values, we simply ban them, instead introducing
product types $(A_1 \times ... \times A_n)$, which we will write $\Pi_i A_i$. We also _annotate_
each expression with an effect $\epsilon$.

We postulate the expected typing rules:

$$
\frac{\Gamma(x) \leq (A, \epsilon)}{\Gamma \vdash_\epsilon x : A}
\qquad
\frac{\forall i, \Gamma \vdash_\epsilon a_i : A_i}{\Gamma \vdash_\epsilon (a_i)_i : \Pi_iA_i}
\qquad
\frac{f : A \to_\epsilon B \qquad \Gamma \vdash_\epsilon a : A}{\Gamma \vdash_\epsilon f\;a : B}
$$

These satisfy the expected weakening lemma

$$
\frac{\Gamma' \leq \Gamma \quad \Gamma \vdash_\epsilon a : A \quad \epsilon \leq \epsilon'}
     {\Gamma' \vdash_{\epsilon'} a : A }
$$

We must now modify our typing judgement for bodies to differentiate between
binding a variable and unpacking:

$$
\frac{
        \Gamma \vdash_\epsilon a : A \qquad \Gamma, x : A_\bot \vdash b : \Delta
    }{
        \Gamma \vdash_\epsilon \mathsf{let}\;x = a; b : \Delta
    }
\frac{
        \Gamma \vdash_\epsilon a : \Pi_iA_i \qquad
        \quad \Gamma, (x_j : {A_j}_\bot)_j \vdash b : \Delta
    }{
        \Gamma \vdash \mathsf{let}\;(x_j)_j = a : \Delta
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

Note that label contexts $\mathcal{L}$ are now mappings $\ell \mapsto (\Gamma, A)$, i.e., there is
now only a single parameter type. Similarly, we modify the rules for CFGs as follows:

$$
\frac{
        \forall (\ell, x, \beta) \in G.
            \exists (\Gamma, A) = \mathcal{R}(\ell).
            \Gamma, x : A \vdash \beta \rhd \mathcal{R}
        \qquad 
        \forall \ell \notin G. \mathcal{R}(\ell) \leq \mathcal{K}(\ell)
    }
    {\mathcal{R} \vdash' G \rhd \mathcal{K}}
$$

where control-flow graphs $G$ are now mappings $\ell \mapsto (x, \beta)$. Weakening and
label-weakening can be shown to hold exactly as before.

Note that this system is obviously isomorphic to the original, with expressions just introducing
anonymous temporary variable bindings and renamings.

### Adding a Terminator Language

Similarly, it greatly simplifies _label substitutions_ if we also have a language for _terminators_;
this also allows us to avoid introducing spurious basic blocks consisting only of conditional
branches, especially since we do not, in our simple language, have a switch-statement. In
particular, we introduce the following judgement, analogous to that for blocks, with the following
obvious rules:

$$
\boxed{\Gamma \vdash t \rhd \mathcal{L}}
$$

$$
\frac
    {\mathcal{L}(\ell) = A \quad \Gamma \vdash_\bot a : A}
    {\Gamma \vdash \mathsf{br}\;\ell\;a \rhd \mathcal{L}}
\qquad
\frac{
    \Gamma \vdash_\bot e : \mathbf{2} \qquad
    \Gamma \vdash s \rhd \mathcal{L} \qquad
    \Gamma \vdash t \rhd \mathcal{L}
}{
    \Gamma \vdash \mathsf{ite}\;e\;s\;t \rhd \mathcal{L}
}
$$

TODO: lore on weakening, label-weakening...

Blocks can then be typed as follows:

$$
\frac
    {\Gamma \vdash b : \Delta \quad \Delta \vdash t \rhd \mathcal{L}}
    {\Gamma \vdash b ; t \rhd \mathcal{L}}
$$

TODO: lore on weakening, label-weakening...

Once again, this change doesn't add any new expressive power to our system: we can convert a CFG in
the new system to a CFG in the old system by just introducing basic blocks with temporary names to
the CFG in the obvious way. One other useful property this system has is that it typechecks a strict
superset of the syntax the previous system does.

### Substitution

Now that we have an expression language, we can attempt to formalize _substitution_, which can then
be used to formalize a wide variety of optimizations such as loop hoisting and constant propagation.

We begin by defining a _substitution_ $\sigma : \Gamma \to \Delta$ to be a map from variables to
terms such that $\forall (x, A, \epsilon) \in \Delta. \Gamma \vdash_\epsilon \sigma(x) : A$. In
particular, we say $\sigma$ is _pure_ if $\forall (x, A, \epsilon) \in \Delta. \Gamma \vdash_\bot
\sigma(x) : A$.

Stating substitution for expressions is quite straightforward: if $\sigma : \Gamma \to \Delta$,
then

$$
\Delta \vdash_\epsilon a : A \implies \Gamma \vdash_\epsilon [\sigma]a : A
$$

with this substitution _semantically_ sound if $\sigma$ is pure. Unfortunately, even graduating to
bodies makes things a lot more complicated. One issue is that, since we are working in a named
setting, it is nontrivial implement capture-avoiding substitution, since the usual approach of
renaming bound variables to fresh names won't work if implemented  as the names of bound variables
are visible on the right-hand side of the judgement for bodies. More concretely, given the body

```rust
let z = 3;
let x = y;
```

and the substitution $y \mapsto 3 + z$, we might try writing the substitution as

```rust
let z0 = 3;
let x = y + z;
```

except now $z$ does not have the appropriate value ($3$) at the end of the body! So we instead need
to write something like

```rust
let z0 = 3;
let x = y + z;
let z = z0;
```

Instead, we'll do what real SSA-based compilers often do and simply use naive, _non_-capture
avoiding substitutions. This of course mans that a substitution is only valid if

$$
\forall x \in \mathsf{defs}(b), \sigma(x) = x
$$

Another complication is, considering the case where $\sigma : \Gamma' \to \Gamma$, it is unclear
what $\Delta'$ should be in

$$
\Gamma \vdash b : \Delta \implies \Gamma' \vdash [\sigma]b : \Delta'
$$

This is because some variables in $x \in \Delta$ may come from $\Gamma$ (rather than being newly
defined in the body), but not be contained in $\Gamma'$, being instead defined as $\sigma(x)$. 

We hence introduce a _new_ judgement

$$
\boxed{\Gamma \vdash' b : \Delta}
$$

where $\Delta$ consists of exactly the variables defined by $b$, with rules

$$
\frac{}{\Gamma \vdash' \cdot : \cdot} \qquad
\frac{\Gamma \vdash_\epsilon a : A \quad \Gamma, x : A \vdash' b : \Delta}
     {\Gamma \vdash' \mathsf{let}\;x = a; b : x : A, \Delta} \qquad
\frac{\Gamma \vdash_\epsilon a : \Pi_iA_i \quad \Gamma, (x_i : A_i)_i \vdash' b : \Delta}
     {\Gamma \vdash' \mathsf{let}\;x = a; b : (x_i : A_i)_i, \Delta}
$$

and note that

$$
\Gamma \vdash b : \Delta \iff \exists \Delta', 
    \Gamma \vdash' b : \Delta' \land
    \Gamma \sqcup \Delta' \leq \Delta 
$$

_This_ new judgement then respects substitution, with substitution lemma

$$
\Gamma \vdash' b : \Delta \implies \Gamma' \vdash [\sigma]b : \Delta
$$

We can proceed similarly for basic blocks and CFGs, but we have to do a whole lot more fiddling with
names, taking thousands of lines of Lean to formalize! It seems clear that, should we want to be
able to effectively state this and more complicated theorems (such as label-substitution), we will
need a more convenient representation of SSA.

### Formalization

We have now obtained a system which is essentially the same as that formalized in
[freyd-ssa](https://github.com/imbrem/freyd-ssa), except for a few small details, which we will go
over now.

[freyd-ssa](https://github.com/imbrem/freyd-ssa) defines types inductively as follows:
$$
A, B, C ::= X \;|\; A \times B \;|\; \mathbf{1} \;|\; \mathbf{2}
$$

In particular, types are generated freely from a set of base types $X$. For simplicity, we only
define pairs of types $A \times B$, and an explicit unary type $\mathbf{1}$; these can simulate
$n$-ary pairs $\Pi_i A_i$ by defining, e.g., $\Pi_{i = 1}^nA_i = A_1 \times \Pi_{i = 2}A_i$. We
also include a builtin boolean type $\mathbf{2}$.

Hence, in particular, our term language only defines binary pairs and a constant $()$ of type
$\mathbf{1}$:

$$
\frac{
        \Gamma \vdash_\epsilon a : A \qquad \Gamma \vdash_\epsilon b: B
    }{
        \Gamma \vdash_\epsilon (a, b) : A \times B
    } \qquad
\frac{}{\Gamma \vdash_\epsilon () : \mathbf{1}} \qquad
\frac{}{\Gamma \vdash_\epsilon \mathsf{tt} : \mathbf{2}} \qquad
\frac{}{\Gamma \vdash_\epsilon \mathsf{ff} : \mathbf{2}}
$$

Similarly, our grammar for bodies only allows binary destructuring:

$$
\frac{
        \Gamma \vdash_\epsilon a : A \times B \qquad
        \quad \Gamma, x : A_\bot, y : B_\bot \vdash b : \Delta
    }{
        \Gamma \vdash \mathsf{let}\;(x, y) = a : \Delta
    }
$$

One other change is that our rules for CFGs are a little bit more convoluted: we define $\mathcal{L}
\vdash' G \rhd \mathcal{K}$ using the following much less intuitive rules:
  
$$
\frac{}{\mathcal{L} \vdash' \cdot \rhd \mathcal{L}} \qquad
\frac{
\mathcal{L} \vdash' G \rhd \mathcal{K}, (\ell \mapsto \Gamma, A) \quad
\ell \notin \mathcal{K} \quad
\Gamma, x : A \vdash \beta \rhd \mathcal{L} \quad
}{
    \mathcal{L} \vdash' G, \ell(x) \Rightarrow \beta \rhd \mathcal{K}
} \qquad
\frac{\mathcal{L} \vdash' G \rhd \mathcal{K}, \quad \ell \notin \mathcal{L}}
    {\mathcal{L} \vdash' G \rhd \mathcal{K}, (\ell \mapsto \Gamma, A)}
$$

where $G, \ell(x) \Rightarrow \beta$, as expected, denotes changing $G(\ell)$ from undefined to $(x,
\beta)$, with CFG well-typedness then given by

$$
\frac{\mathcal{L} \leq \mathcal{R} \quad \mathcal{R} \vdash' G \rhd \mathcal{K}}
{\mathcal{L} \vdash G \rhd \mathcal{K}}
$$

The reason for this had to do with wanting a more inductive semantics; in retrospect, I can't think
of why exactly we went for this this at the moment, but that's what was formalized and we have to be
honest! This is roughly equivalent to the formulation given above, though it provides a bit more
power, since "dead" code, i.e. $\ell$ not reachable from the entry context, does not need to
typecheck.

### Adding Coproducts

One of the design goals for  [freyd-ssa](https://github.com/imbrem/freyd-ssa) was to keep things as
conventional as possible. Hence, we did not support coproducts, and instead only provided a Boolean
type $\mathbf{2}$. However, effectively reasoning about coproducts can not only allow us to perform
various interesting optimizations, especially when the source language supports them, but also makes
it a lot easier to prove category-theoretic properties of our semantics. So, in
[debruijn-ssa](https://github.com/imbrem/debruijn-ssa), we choose to support them.

In particular, our types are now given by the grammar

$$
A, B, C ::= X \;|\; A \times B \;|\; \mathbf{1} \;|\; A + B \;|\; \mathbf{0}
$$

and terms are extended in the obvious manner:

$$
\frac{\Gamma \vdash_\epsilon a : A}{\Gamma \vdash_\epsilon \mathsf{inl}\;a : A + B} \qquad
\frac{\Gamma \vdash_\epsilon b : B}{\Gamma \vdash_\epsilon \mathsf{inr}\;b : A + B} \qquad
\frac{\Gamma \vdash_\epsilon e : \mathbf{0}}{\Gamma \vdash_\epsilon \mathsf{abort}\;e : A}
$$

For control-flow, we replace $\mathsf{ite}$ with a $\mathsf{case}$ terminator, which binds
variables, similarly to pattern-matching:

$$
\frac{
    \Gamma \vdash_\epsilon e : A + B \quad 
    \Gamma, x : A \vdash s \rhd \mathcal{L} \quad
    \Gamma, y : B \vdash t \rhd \mathcal{L}
}{
    \Gamma \vdash \mathsf{case}\;e\;(x \Rightarrow s)\;(y \Rightarrow t) \rhd \mathcal{L}
}
$$

Note that we can easily simulate booleans in this setting by defining

$$
\mathbf{2} = \mathbf{1} + \mathbf{1} \qquad
\mathbf{tt} = \mathbf{inl}\;() \qquad
\mathbf{ff} = \mathbf{inr}\;() \qquad
\mathsf{ite}\;e\;s\;t = \mathsf{case}\;e\;(\cdot \Rightarrow s)\;(\cdot \Rightarrow t)
$$

## Explicit Scoping and De-Bruijn Indices

Now that we've seen how difficult it is to state substitution when using names as above, we want to
develop an inductive representation of SSA which is easier to reason about, while at the same time
isomorphic to our original language. To do this, we have to think carefully about how variables and
labels are scoped in SSA.

### Dominator Trees

- Want a sane way to do induction on programs, decomposing them into smaller pieces
- Want to know exactly what is in scope at any given point
- These are related problems
- Let's think carefully about [dominator
  trees](https://en.wikipedia.org/wiki/Dominator_(graph_theory))...


<img src={dominance_cfg} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

<img src={dominance_cfg_annotated} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

<img src={dominance_tree_explainer} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

<img src={dominance_tree_cfg} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

<img src={dominance_tree_add_good} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

<img src={dominance_tree_add_rec_good} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

<img src={dominance_tree_add_bad} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

<img src={dominance_scope_diagram} 
    style="max-width:40em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

<img src={dominance_scope_annotated} 
    style="max-width:40em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

<img src={region_diagram} 
    style="max-width:40em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

### Scoping Via Dominator Trees

- Bracketing determines variable scoping
- This is _because_ bracketing determines label scoping
- Single entrypoint lore...
- Expressions: same as before, but see `Term`
- Bodies: same as before
- Terminators: same as before
- Blocks: same as before
- _Regions_
    $$
    \boxed{\Gamma \vdash r \rhd \mathcal{L}}
    $$
    $$
    \frac{
        \Gamma \vdash b : \Delta \quad
        \Delta \vdash t \rhd (\mathcal{L} \sqcup \mathcal{R}) \quad
        \forall (ℓ, A) ∈ \mathcal{R}, 
            \Delta, x_\ell : A \vdash G_\ell \rhd \mathcal{L} \sqcup \mathcal{R} \quad
        \forall G_\ell, \ell ∈ \mathcal{R}
    }{
        \Gamma \vdash \mathsf{reg}\;(b;t)\;(\ell\;x_\ell \Rightarrow G_\ell)_\ell \rhd \mathcal{L}
    }
    $$

### De-Bruijn Indices

- The above rules are compatible with de-Bruijn indices for both variables and labels...
- So our formalization can just use that
- Bonus: α-conversion for free
- But we'll write our typing rules with names, for now!
- This is the `BBRegion` data structure in [debruijn-ssa](https://github.com/imbrem/debruijn-ssa);
  see also `Block`, `Body`, `Terminator`. We use `Term` rather than operations or expressions,
  though; see `Term`

### How to Recover SSA

<img src={dominance_cfg_scoped} 
    style="max-width:25em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

- Erase the brackets: no more regions
- Some notes on what we want to allow as terminators
- We want cases for Reasons (TM)... this will be important later...

### Removing Bodies and Blocks

TODO: loots of text...

TODO: text... looots of text...

$$
\frac{
    \Gamma \vdash t \rhd \mathcal{L} \sqcup \mathcal{R} \quad
    \forall (ℓ, A) ∈ \mathcal{R}, 
        \Delta, x_\ell : A \vdash G_\ell \rhd \mathcal{L} \sqcup \mathcal{R} \quad
    \forall G_\ell, \ell ∈ \mathcal{R}
}{
    \Gamma \vdash \mathsf{reg}\;t\;(\ell\;x_\ell \Rightarrow G_\ell)_\ell \rhd \mathcal{L}
}
$$
$$
\frac{
    \Gamma \vdash_\epsilon a : A \quad 
    \Gamma, x : A_\bot \vdash r \rhd \mathcal{L}
}{
    \Gamma \vdash \mathsf{let}\;x = a; r \rhd \mathcal{L}
} \quad
\frac{
    \Gamma \vdash_\epsilon a : A \times B \quad
    \Gamma, x : A_\bot, y : B_\bot \vdash r \rhd \mathcal{L}
}{
    \Gamma \vdash \mathsf{let}\;(x, y) = a; r \rhd \mathcal{L}
}
$$

TODO: yet more text

This gives us the `TRegion` data structure; but again see `Term`

### How to Recover SSA

TODO: segue...

- Isomorphic to the above by (trivial)
- Go over basic-block reconstruction in particular

## Structured Branching Control-Flow

- MLIR supports it!
- Two features: structured control-flow in terminators and structured control-flow in terms
- Easier to eliminate the latter into the former, and the former into SSA, so we'll work that way

### Structured Terminators

- Naive way: mutual recursion between terminators and regions needed

- Nicer way: fuse terminators and regions

<img src={region_diagram_gen} 
    style="max-width:40em;width:100%;display:block;margin-left: auto;margin-right: auto;"
    alt="A representation of a control-flow graph">

$$
\frac{
    \Gamma \vdash r \rhd \mathcal{L} \sqcup \mathcal{R} \quad
    \forall (ℓ, A) ∈ \mathcal{R}, 
        \Delta, x_\ell : A \vdash G_\ell \rhd \mathcal{L} \sqcup \mathcal{R} \quad
    \forall G_\ell, \ell ∈ \mathcal{R}
}{
    \Gamma \vdash \mathsf{reg}\;r\;(\ell\;x_\ell \Rightarrow G_\ell)_\ell \rhd \mathcal{L}
}
$$
$$
\frac{
    \Gamma \vdash_\epsilon a : A \quad 
    \Gamma, x : A_\bot \vdash r \rhd \mathcal{L}
}{
    \Gamma \vdash \mathsf{let}\;x = a; r \rhd \mathcal{L}
} \quad
\frac{
    \Gamma \vdash_\epsilon a : A \times B \quad
    \Gamma, x : A_\bot, y : B_\bot \vdash r \rhd \mathcal{L}
}{
    \Gamma \vdash \mathsf{let}\;(x, y) = a; r \rhd \mathcal{L}
}
$$
$$
\frac{
    \mathcal{L}(\ell) = A \quad 
    \Gamma \vdash_\bot a : A
}{
    \Gamma \vdash \mathsf{br}\;\ell\;a \rhd \mathcal{L}
}
\qquad
\frac{
    \Gamma \vdash_\epsilon e : A + B \quad
    \Gamma, x: A_\bot \vdash l \rhd \mathcal{L} \quad
    \Gamma, y: B_\bot \vdash r \rhd \mathcal{L}
}{
    \Gamma \vdash_\epsilon \mathsf{case}\;e\;(x \Rightarrow l)\;(y \Rightarrow r)
}
$$

- This is the Region data structure in [debruijn-ssa](https://github.com/imbrem/debruijn-ssa), but
  see `Term`

### How to Recover SSA

- Nice thing: Region can represent:
    - Terminators
    - Blocks
    - BBRegions
    - TRegions
    - That's why these are all written with $\rhd$!

- In particular, can get a `TRegion` pretty easily, via:

TODO: lowering text...

$$
\mathsf{case}\;e\;(x \Rightarrow l)\;(y \Rightarrow r) 
\to \mathsf{reg}\;(\mathsf{case}
    \;(x \Rightarrow \mathsf{br}\;\ell_l\;x)
    \;(y \Rightarrow \mathsf{br}\;\ell_r\;y))
    \;(ℓ_l\;x \Rightarrow l)
    \;(ℓ_r\;x \Rightarrow r)
$$

$$
\mathsf{br}\;\ell\;x 
\to \mathsf{reg}\;(\mathsf{br}\;ℓ\;x)
$$

$$
\mathsf{reg}\;(\mathsf{reg}\;\beta\;(\ell\;x_\ell \Rightarrow G_\ell)_\ell)
    \;(\kappa\;x_\kappa \Rightarrow H_\kappa)_\kappa
\to \mathsf{reg}\;\beta\;(\ell\;x_\ell \Rightarrow G_\ell)_\ell
    \;(\kappa\;x_\kappa \Rightarrow H_\kappa)_\kappa
$$

And already established that's isomorphic to SSA

### Introducing a Term Language

- Some cool optimizations we might like to do
- What we need; not particularly complicated...

$$
\frac{
    \Gamma \vdash_\epsilon a : A \quad
    \Gamma, x : A_\bot \vdash_\epsilon e : B
}{
    \Gamma \vdash_\epsilon \mathsf{let}\;x = a; e : B
} \quad
\frac{
    \Gamma \vdash_\epsilon a : A \times B \quad
    \Gamma, x : A_\bot, y : B_\bot \vdash_\epsilon e : C 
}{
    \Gamma \vdash_\epsilon \mathsf{let}\;(x, y) = a; e : C
}
$$

$$
\frac{\Gamma \vdash_\epsilon e : A + B 
    \quad \Gamma, x : A_\bot \vdash_\epsilon c_l : C 
    \quad \Gamma, y : B_\bot \vdash_\epsilon c_r : C
}{
    \Gamma \vdash \mathsf{case}\;e\;(x \Rightarrow c_l)\;(y \Rightarrow c_r)
}
$$

### How to Recover SSA

- Can now use ye olde rewrite rules nicely:

TODO: can do using repeated application of

$$
\mathsf{let}\;y = (\mathsf{let}\;x = a; e); r \to
\mathsf{let}\;x = a; \mathsf{let}\;y = e; r
$$

$$
\mathsf{let}\;z = (\mathsf{let}\;(x, y) = a; e); r \to
\mathsf{let}\;(x, y) = a; \mathsf{let}\;z = e; r
$$

$$
\mathsf{let}\;z = (\mathsf{case}\;e\;(x \Rightarrow c_l)\;(y \Rightarrow c_r)); r \to
\mathsf{case}\;e\;(x \Rightarrow \mathsf{let}\;z = c_l; r)\;(y \Rightarrow \mathsf{let}\;z = c_r; r)
$$

TODO: and likewise for let...

$$
\mathsf{let}\;(y, z) = (\mathsf{let}\;x = a; e); r \to
\mathsf{let}\;x = a; \mathsf{let}\;(y, z) = e; r
$$

$$
\mathsf{let}\;(z, w) = (\mathsf{let}\;(x, y) = a; e); r \to
\mathsf{let}\;(x, y) = a; \mathsf{let}\;(z, w) = e; r
$$

$$ \mathsf{let}\;(z, w) = (\mathsf{case}\;e\;(x \Rightarrow c_l)\;(y \Rightarrow c_r)); r \to
\mathsf{case}\;e\;(x \Rightarrow \mathsf{let}\;(z, w) = c_l; r)\;(y \Rightarrow \mathsf{let}\;(z, w)
= c_r; r) $$

TODO: and for case...

$$
\mathsf{case}\;(\mathsf{let}\;x = a; e)\;(y \Rightarrow l)\;(z \Rightarrow r) \to
\mathsf{let}\;x = a; \mathsf{case}\;e\;(y \Rightarrow l)\;(z \Rightarrow r)
$$

$$
\mathsf{case}\;(\mathsf{let}\;(x, y) = a; e)\;(z \Rightarrow l)\;(w \Rightarrow r) \to
\mathsf{let}\;(x, y) = a; \mathsf{case}\;e\;(z \Rightarrow l)\;(w \Rightarrow r)
$$

$$
\mathsf{case}\;(\mathsf{case}\;e\;(x \Rightarrow c_l)\;(y \Rightarrow c_r))
    \;(z \Rightarrow l)\;(w \Rightarrow r)
\to
\mathsf{case}\;e
    \;(x \Rightarrow \mathsf{case}\;c_l\;(z \Rightarrow l)\;(w \Rightarrow r))
    \;(y \Rightarrow \mathsf{case}\;c_r\;(z \Rightarrow l)\;(w \Rightarrow r))
$$

TODO: which may be derived from the validity of the $\eta$-expansions...

$$
\mathsf{let}\;(x, y) = e \to \mathsf{let}\;z = e;\mathsf{let}\;(x, y) = z
\qquad
\mathsf{case}\;e\;(x \Rightarrow l)\;(y \Rightarrow r) \to
\mathsf{let}\;z = e;\mathsf{case}\;z\;(x \Rightarrow l)\;(y \Rightarrow r)
$$

### Alternative Design: extended `br`


$$
\frac{
    (\mathcal{L} \sqcup \mathcal{R})(ℓ) = A \quad
    \Gamma \vdash_\bot a : A \quad
    \forall (ℓ, B) ∈ \mathcal{R}, 
        \Delta, x_\ell : B \vdash G_\ell \rhd \mathcal{L} \sqcup \mathcal{R} \quad
    \forall G_\ell, \ell ∈ \mathcal{R}
}{
    \Gamma \vdash \mathsf{br}\;\ell\;a\;(\ell\;x_\ell \Rightarrow G_\ell)_\ell \rhd \mathcal{L}
}
$$

- Closer to MLIR, maybe?

- Much simpler to explain: `br` to a branch
- _But_: more painful for expressing certain !FUN! rewrite rules, e.g.

$$
\mathsf{br}\;\ell\;a\;(\ell_1\;x \Rightarrow G_1)\;(\ell_2\;y \Rightarrow G_2)
\to \mathsf{let}\;x = a; G_1'
$$

where $G'$ is $G$ with all occurences of $\mathsf{br}\;\ell_i\;e\;(\kappa\;y \Rightarrow
J_\kappa)_\kappa$ are replaced with

$$
\mathsf{br}\;\ell_i\;e
    \;(\ell_1\;x \Rightarrow G_1)\;(\ell_2\;y \Rightarrow G_2)
    \;(\kappa\;y \Rightarrow J_\kappa)_\kappa
$$

This is both irritating to state and manipulate, and blows up the size of the program exponentially.
This representation also turns out to be more painful to lower, and often introduces spurious basic
blocks jumping straight to more control flow, especially when we try to address the aforementioned
blowup.

- Conclusion: not now, maybe later. And our representation is more general, since this can be
emulated precisely with

$$
\mathsf{br}\;\ell\;a\;(\ell\;x_\ell \Rightarrow G_\ell)_\ell 
:= \mathsf{reg}\;(\mathsf{br}\;\ell\;a)\;(\ell\;x_\ell \Rightarrow G_\ell)_\ell
$$

## An Inductive Representation of SSA

- Types: 
...
$$
A, B, C ::= X \;|\; A \times B \;|\; \mathbf{1} \;|\; A + B \;|\; \mathbf{0}
$$
...
- Syntax:
...
$$
a, b, c, d, e ::= x \;|\; \mathsf{let}\;x = a; e \;|\; f\;a 
    \;|\; (a, b) \;|\; \mathsf{let}\;(x, y) = a; e \;|\; ()
    \;|\; \mathsf{inl}\;a \;|\; \mathsf{inr}\;b \;|\; 
    \;|\; \mathsf{case}\;e\;(x \Rightarrow c_l)\;(y \Rightarrow c_r) 
    \;|\; \mathsf{abort}\;e
$$
...
$$
l, r ::= \mathsf{br}\;\ell\;a 
    \;|\; \mathsf{let}\;x = a; r 
    \;|\; \mathsf{let}\;(x, y) = a; r
    \;|\; \mathsf{case}\;e\;(x \Rightarrow l)\;(y \Rightarrow r)
    \;|\; \mathsf{reg}\;r\;(\ell\;x_\ell \Rightarrow G_\ell)_\ell
$$
...
- Term typing: 
...

$$
\frac{
        \Gamma \vdash_\epsilon a : A \qquad \Gamma \vdash_\epsilon b: B
    }{
        \Gamma \vdash_\epsilon (a, b) : A \times B
    } \qquad
\frac{}{\Gamma \vdash_\epsilon () : \mathbf{1}} \qquad
\frac{\Gamma \vdash_\epsilon a : A}{\Gamma \vdash_\epsilon \mathsf{inl}\;a : A + B} \qquad
\frac{\Gamma \vdash_\epsilon b : B}{\Gamma \vdash_\epsilon \mathsf{inr}\;b : A + B} \qquad
\frac{\Gamma \vdash_\epsilon e : \mathbf{0}}{\Gamma \vdash_\epsilon \mathsf{abort}\;e : A}
$$

$$
\frac{
    \Gamma \vdash_\epsilon a : A \quad
    \Gamma, x : A_\bot \vdash_\epsilon e : B
}{
    \Gamma \vdash_\epsilon \mathsf{let}\;x = a; e : B
} \quad
\frac{
    \Gamma \vdash_\epsilon a : A \times B \quad
    \Gamma, x : A_\bot, y : B_\bot \vdash_\epsilon e : C 
}{
    \Gamma \vdash_\epsilon \mathsf{let}\;(x, y) = a; e : C
}
$$

$$
\frac{\Gamma \vdash_\epsilon e : A + B 
    \quad \Gamma, x : A_\bot \vdash_\epsilon c_l : C 
    \quad \Gamma, y : B_\bot \vdash_\epsilon c_r : C
}{
    \Gamma \vdash \mathsf{case}\;e\;(x \Rightarrow c_l)\;(y \Rightarrow c_r)
}
$$

...
- Region typing: 
...

$$
\frac{
    \Gamma \vdash r \rhd \mathcal{L} \sqcup \mathcal{R} \quad
    \forall (ℓ, A) ∈ \mathcal{R}, 
        \Delta, x_\ell : A \vdash G_\ell \rhd \mathcal{L} \sqcup \mathcal{R} \quad
    \forall G_\ell, \ell ∈ \mathcal{R}
}{
    \Gamma \vdash \mathsf{reg}\;r\;(\ell\;x_\ell \Rightarrow G_\ell)_\ell \rhd \mathcal{L}
}
$$
$$
\frac{
    \Gamma \vdash_\epsilon a : A \quad 
    \Gamma, x : A_\bot \vdash r \rhd \mathcal{L}
}{
    \Gamma \vdash \mathsf{let}\;x = a; r \rhd \mathcal{L}
} \quad
\frac{
    \Gamma \vdash_\epsilon a : A \times B \quad
    \Gamma, x : A_\bot, y : B_\bot \vdash r \rhd \mathcal{L}
}{
    \Gamma \vdash \mathsf{let}\;(x, y) = a; r \rhd \mathcal{L}
}
$$
$$
\frac{
    \mathcal{L}(\ell) = A \quad 
    \Gamma \vdash_\bot a : A
}{
    \Gamma \vdash \mathsf{br}\;\ell\;a \rhd \mathcal{L}
}
\qquad
\frac{
    \Gamma \vdash_\epsilon e : A + B \quad
    \Gamma, x: A_\bot \vdash l \rhd \mathcal{L} \quad
    \Gamma, y: B_\bot \vdash r \rhd \mathcal{L}
}{
    \Gamma \vdash_\epsilon \mathsf{case}\;e\;(x \Rightarrow l)\;(y \Rightarrow r)
}
$$

...

### Next Steps:

- Denotational semantics in terms of !FUN! category theory! (done)
- Exciting models involving weak memory! (done)
- Equational theory! (done)
- WIP: proof of completeness for equational theory, implying initiality of model!

## Future Work

- First: making this $n$-ary
    - Didn't do at first for simplicity; having second thoughts...
    - Should allow us to remove $\mathbf{1}$, $\mathbf{0}$, $\mathsf{abort}$, and special case
      rewrite rules for $\mathbf{1}$
- Should play more nicely with: Linearity:
    - Working on prototype
    - Have old name-based version in failed PLDI submission (paper only)
    - Thinking of more advanced _resource algebra_ based formalization
- Mutual recursion
- Or, fusing terms and regions:
    - Cool idea!
    - Allows advanced structured control flow, e.g. a `for` instruction like MLIR
    - Easier to work with than SSA, maybe
    - Effective effect handlers, maybe
    - Once this paper is done...

## Edge Cases

### Jumps to the entry block

- can be done, just need to put things in a nested CFG

<script>
    import program_cfg from "$lib/assets/inductive-ssa/program_cfg.svg"
    import body_live from "$lib/assets/inductive-ssa/body_live.svg"
    import block_live from "$lib/assets/inductive-ssa/block_live.svg"
    import cfg_live from "$lib/assets/inductive-ssa/cfg_live.svg"
    import dominance_cfg from "$lib/assets/inductive-ssa/dominance_cfg.excalidraw.svg"
    import dominance_cfg_annotated from 
        "$lib/assets/inductive-ssa/dominance_cfg_annotated.excalidraw.svg"
    import dominance_tree_explainer from 
        "$lib/assets/inductive-ssa/dominance_tree_explainer.excalidraw.svg"
    import dominance_tree_cfg from 
        "$lib/assets/inductive-ssa/dominance_tree_cfg.excalidraw.svg"
    import dominance_tree_add_good from 
        "$lib/assets/inductive-ssa/dominance_tree_add_good.excalidraw.svg"
    import dominance_tree_add_rec_good from 
        "$lib/assets/inductive-ssa/dominance_tree_add_rec_good.excalidraw.svg"
    import dominance_tree_add_bad from 
        "$lib/assets/inductive-ssa/dominance_tree_add_bad.excalidraw.svg"
    import dominance_scope_diagram from 
        "$lib/assets/inductive-ssa/dominance_scope_diagram.excalidraw.svg"
    import dominance_scope_annotated from 
        "$lib/assets/inductive-ssa/dominance_scope_annotated.excalidraw.svg"
    import region_diagram from 
        "$lib/assets/inductive-ssa/region_diagram.excalidraw.svg"
    import dominance_cfg_scoped from 
        "$lib/assets/inductive-ssa/dominance_cfg_scoped.excalidraw.svg"
    import region_diagram_gen from 
        "$lib/assets/inductive-ssa/region_diagram_gen.excalidraw.svg"
</script>

<!-- TODO: fix annotations -->