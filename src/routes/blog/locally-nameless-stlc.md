---
title: Locally Nameless STLC in Lean
published: '2025-08-23'
---

I'm currently riding to Sicily, and, as I'm writing this, sitting in Dover Port waiting for my ferry
to Dunkirk in about 30 minutes. 

While my body undergoes this physical adventure, my mind has been thinking about
[`covalence-lean`](https://github.com/imbrem/covalence-lean), a Lean 4 formalization of extensional
MLTT in the locally-nameless style. Neel says I should write up some of what I learned about
formalizing locally-nameless type theories in Lean, so here I am, with a poor imitation of
[Charguéraud's locally nameless tutorial](https://chargueraud.org/research/2009/ln/main.pdf).

Let's get started.

# Project Setup

The Wi-Fi at the port's Costa is surprisingly good, so we can just go ahead and start with
```bash
# Create a new Lean 4 project, ln-stlc, with a mathlib dependency
lake +leanprover-community/mathlib4:lean-toolchain new ln-stlc math
# Open the folder created for the project
cd ln-stlc
# Check everything was set up correctly
lake build
```

# Syntax

## Definitions

We've got 15 minutes until we need to rush back over to the ferry, with some safety window. Let's
see if we can code up some syntax in that time. Opening up `LnStlc/Basic.lean`, we'll start with
our types:
```lean
/-- Simple types -/
inductive Ty : Type
/-- The unit type. -/
| unit
/-- A function type `A → B`. -/
| arr (A B : Ty)
/-- A product type `A × B`. -/
| prod (A B : Ty)
```
Let's throw in an import for ℕ syntax
```lean
import Mathlib.Data.Nat.Lattice
```
and we can go ahead and define the corresponding syntax as follows:
```lean
/-- Untyped STLC terms -/
inductive Tm : Type
/-- A named free variable. -/
| fv (x : String)
/-- A bound variable, represented using a de Bruijn index. -/
| bv (i : ℕ)
/-- The unique value of the unit type. -/
| null
/-- A lambda abstraction `λ (x : A). body`. -/
| abs (ty : Ty) (body : Tm)
/-- A pair `(a, b)`. -/
| pair (lhs rhs : Tm)
/-- The first projection of a pair. -/
| fst (p : Tm)
/-- The second projection of a pair. -/
| snd (p : Tm)
```
Alright, we've got 5 minutes left, we're really cutting it short, so as a sanity check let's define
the _closure level_ of a term and bounce. In English, the closure level of a term $t$ is a number
$n$ such that all unbound variables in $t$ have index $< n$. In particular, a term has closure level
$0$ if and only if it is locally closed. I tend to write this as `bvi` (*B*ound *V*ariable *I*ndex)
in my code:
```lean
/-- The _closure level_ of an STLC term `t` -/
def Tm.bvi : Tm → ℕ
| .fv _ => 0
| .bv i => i + 1
| .null => 0
| .abs _ body => bvi body - 1
| .pair lhs rhs => bvi lhs ⊔ bvi rhs
| .fst p => bvi p
| .snd p => bvi p
```
Alright, off we go, hope we don't miss the ferry.

Luckily, we arrived with time to spare, so I've got 20 minutes to keep hacking. Next up, we want to define the set of
_free variables_ which appears in our term. In general, our well-typed terms will be locally closed, and have only
free variables which appear in our context. We can use Mathlib's finite set machinery to great effect here; we begin by importing
```lean
import Mathlib.Data.Finset.Lattice.Basic
```
and then it's just a matter of writing down the obvious inductive definition
```lean
/-- The set of free variables appearing in an STLC term -/
def Term.fvs : Tm → Finset String
| .fv x => {x}
| .bv _ => ∅
| .null => ∅
| .abs _ body => fvs body
| .pair lhs rhs => fvs lhs ∪ fvs rhs
| .fst p | .snd p => fvs p
```

## Weakening and Substitution

To formalize the rules for our type theory, we'll need to define _substitution_, since our rule for
typing lambda abstractions will require an assumption of the form $b^x : B$. However, to define
substitution, we need to define weakening. There's two ways to go about (both) these things:
- Define weakening/substitution of a single variable, under `n` binders
- Define weakening/substitution using a map $ρ : ℕ → ℕ$/$σ : ℕ → \mathsf{Tm}$, and then specialize
I usually do the latter, since I like generality a little too much, but since my ferry is departing
in precisely 9 minutes, let's do the former first. We can always prove it equivalent to the latter,
which is a good sanity check.

So, we begin by defining `wkUnder`, which says "weaken by inserting a bound variable under $n$
binders" as follows:
```lean
/-- Weaken under `n` binders -/
def Term.wkUnder (n : ℕ) : Tm → Tm
| .fv x => .fv x
| .bv i => if i < n then .bv i else .bv (i + 1)
| .null => .null
| .abs ty body => .abs ty (wkUnder (n + 1) body)
| .pair lhs rhs => .pair (wkUnder n lhs) (wkUnder n rhs)
| .fst p => .fst (wkUnder n p)
| .snd p => .snd (wkUnder n p)
```
Man, time constraints are _really_ good at letting me not overcomplicate things. And letting me
avoid meta-tangents, too! So, this is a pretty simple function. We note that:
- When we weaken a bound variable,
    - If we're under `n`, we leave it alone
    - Otherwise, we increment it
- Every time we go under a binder, we increment the number of binders we're under by 1.
  Here, the only case where this happens is `.abs`
We'll introduce some syntax sugar $↑_0 t$ for weakening $t$ under no binders:
```lean
prefix:70 "↑0" => Term.wkUnder 0
```
And we can now, with just 2 minutes to spare, define substitution under $n$ binders
as follows:
```lean
def Term.substUnder (n : ℕ) (a : Tm) : Tm → Tm
| .fv x => .fv x
| .bv i => if i < n then .bv i else if i = n then a else .bv (i - 1)
| .null => .null
| .abs ty body => .abs ty (substUnder (n + 1) (↑0 a) body)
| .pair lhs rhs => .pair (substUnder n a lhs) (substUnder n a rhs)
| .fst p => .fst (substUnder n a p)
| .snd p => .snd (substUnder n a p)
```
Mmm, `n a p`. I do not like waking up early. But I digress! So again, similarly to for weakening
- When we substitute a bound variable
    - If we're under `n`, we leave it alone
    - If we're _at_ `n`, we replace it with `a`
    - Otherwise, we decrement it
- Every time we go under a binder, we increment the number of binders we're under by 1. We also
  weaken the value we're substituting, to avoid capturing variables from the binder!

And there we go! We've now got everything we need to give our typing rules. It's 14:03 and
the ferry still hasn't arrived, though they said it will be on time, so let's see how far
we can get until then. The power of locally nameless is truly immense!

# Typing Rules

So, we begin by defining contexts, which are just going to be lists of variables mapped to
types. It's an interesting question whether we want to allow duplicating variable names in our
contexts or not; if we do, we obviously want the _latest_ typing of a variable to hold.
Usually, I forbid this in the context well-formedness judgement, but this is a simple type
system, so there won't be a well-formedness judgement. Which means we need to do this in the
type or not at all. I don't want to complicate my types, and I trust in the magic of cofinite
quantification, so let's just not:
```lean
inductive Ctx : Type
| nil
| cons (Γ : Ctx) (x : String) (A : Ty)
```
Someone's just come by to collect my ticket, so the pressure's on! Let's define a judgement
for a variable's type, handling shadowing as discussed... and nope, it's time to go! Until next time!