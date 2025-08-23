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