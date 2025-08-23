---
title: Adventures in Type Theory -- Locally Nameless STLC (Part 1)
published: '2025-08-23'
---

It's been a long time!

As my PhD draws to a close, I decided to go on a few adventures while writing up my thesis. I've
also got a massive backlog of all kinds of other things I've wanted to write over the course of my
PhD, and while the best time to start was yesterday, the second best time to start is now. Hence,
_Adventures in Type Theory_.

We're beginning with a motorcycle ride from Cambridge to Sicily. It's going to be fun. Along the
way, we'll try to cover how to formalize locally nameless things in Lean in detail, which hopefully
we'll eventually condense into an ArXiv article or two without the associated travelogue. We're
starting from the basics with the simply typed lambda calculus, inspired by [Arthur Charguéraud's
excellent locally nameless tutorial](https://chargueraud.org/research/2009/ln/main.pdf).

To set the stage, this article begins with me sitting in Dover Port around 12:30 UK time, waiting
for my ferry to Dunkirk, which departed at 14:00. My laptop is open, but I can't find a charging
port. I am sipping the traditional hazelnut latte, remembering long-ago days in Beirut where I drank
the same thing at the ABC mall, before looking out a rain-streaked window at the Order of Engineers
in Tripoli and chipping away at an ever-shifting, perfectionistic implementation of
[ProTem](https://www.cs.toronto.edu/~hehner/PT.pdf), which is how I got into this mess.

Without further ado, let's get started.

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
def Tm.fvs : Tm → Finset String
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
def Tm.wkUnder (n : ℕ) : Tm → Tm
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
prefix:70 "↑₀" => Tm.wkUnder 0
```
And we can now, with just 2 minutes to spare, define substitution under $n$ binders
as follows:
```lean
def Tm.substUnder (n : ℕ) (a : Tm) : Tm → Tm
| .fv x => .fv x
| .bv i => if i < n then .bv i else if i = n then a else .bv (i - 1)
| .null => .null
| .abs ty body => .abs ty (substUnder (n + 1) (↑₀ a) body)
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
Someone's just come by to collect my ticket, so the pressure's on! Let's define a judgement for a
variable's type, handling shadowing as discussed... and nope, it's time to go!

...

As I was saying.
```lean
inductive Ctx.Var : Ctx → Ty → String → Type
| here {Γ : Ctx} {A : Ty} {x : String} : Ctx.Var (Ctx.cons Γ x A) A x
| there {Γ : Ctx} {A B : Ty} {x y : String}
  : x ≠ y → Ctx.Var Γ A x → Ctx.Var (Ctx.cons Γ y B) A x
```
We make this a _type_ rather than a _proposition_ since we might want to do induction on it later if
we get to a categorical semantics. But this is _essentially_ a proposition, since it is a
subsingleton:
```lean
instance Ctx.Var.instSubsingleton {Γ A x} : Subsingleton (Var Γ A x) where
  allEq a b := by
    induction a with
    | here => cases b with | here => rfl | there => contradiction
    | there _ _ I => cases b with
      | here => contradiction
      | there => exact (congrArg _ (I _))
```
It's also useful to know that every variable has at most one type:
```lean
theorem Ctx.Var.disjoint {Γ A B x} (hA : Var Γ A x) (hB : Var Γ B x) : A = B := by
  induction hA with
  | here => cases hB with | here => rfl | there => contradiction
  | there _ _ I => cases hB with 
    | here => contradiction 
    | there _ hB => exact I hB
```
Note the naming and the somewhat unintuitive parameter order `Var Γ A x`, where the type comes
first. That's because I'm thinking of this as the set of variables of type $A$ in $Γ$; it in fact
_be_ a Lean `Set` if we replaced `Type` with `Prop`.

We can now get to our typing rules. We start by, as usual, introducing a spot of notation
```lean
instance Tm.instPow : Pow Tm Tm where
  pow b a := substUnder 0 a b
```
and, while we're at it, to avoid typing `.fv` everywhere,
```lean
instance Tm.instCoeVar : Coe String Tm where
  coe x := .fv x

instance Tm.instPowVar : Pow Tm String where
  pow b x := b^(Tm.fv x)
```
Our typing judgement will take the form
```lean
inductive Ctx.Deriv : Ctx → Ty → Tm → Type
```
Again, we put the type first as we're thinking about "the set of terms of type $A$ in $Γ$", and also
because we're thinking about "a morphism from $Γ$ to $A$". And we return a `Type`, rather than a
`Prop`, in case we want to have fun with that aforementioned morphism idea; that's also why we call
it `Deriv` rather than `HasTy`. Anyways. I see land on the horizon. But we've got 45 minutes, I
think. So let's continue. 

I'll refer readers to [Charguéraud](https://chargueraud.org/research/2009/ln/main.pdf) for deeper
explanation of each of these typing rules, for now, just note that:
- Variables are typed using the obvious rule
  $$
  \frac{Γ(x) = A}{Γ ⊢ x : A}
  $$
- The unit value $*$ always has type $\mathbf{1}$, regardless of context
- We type _abstractions_ by using _cofinite quantification_; that is, our rule is
  $$
  \frac{∀ x ∉ L . Γ, x : A ⊢ b^x : B}{Γ ⊢ λ A . b : A → B}
  \qquad
  \text{where}
  \qquad
  L \in \mathcal{P}_{\mathsf{fin}}(\mathsf{String})
  \quad
  \text{is an arbitrary finite set}
  $$
  Note in particular that:
  - $b$ is _not_ necessarily locally closed, since we bind the $λ$ using a de-Bruijn index
  - But, we'll show by induction that $b^x$ _is_ always locally closed
  - However, the choice of $x$ "doesn't matter" due to quantification
  - But to deal with shadowing, we allow a finite set of exceptions where this can break
  - In real life, this is $\mathsf{vars}(Γ)$, but this has a bad induction property
  - We can equivalently ask the premise for just one _arbitrary_ $x ∉ \mathsf{vars}(Γ)$, but this
    _also_ has a bad induction property
  - So we use cofinite quantification, and it will turn out equivalent to what we want!
- Pairs and projections are typed in the obvious manner:
  $$
  \frac{Γ ⊢ a : A \qquad Γ ⊢ b : B}{Γ ⊢ (a, b) : A × B} \qquad
  \frac{Γ ⊢ p : A × B}{Γ ⊢ \mathsf{fst}(p) : A} \qquad
  \frac{Γ ⊢ p : A × B}{Γ ⊢ \mathsf{snd}(p) : B}
  $$
So, translated to Lean, that becomes
```lean
inductive Ctx.Deriv : Ctx → Ty → Tm → Type
  | var {Γ A x} : Var Γ A x → Deriv Γ A x
  | null {Γ} : Deriv Γ .unit .null
  | abs {Γ A B b} {L : Finset String}
    : (∀x ∉ L, Deriv (cons Γ x A) B (b^x))
    → Deriv Γ (.arr A B) (.abs A b)
  | pair {Γ A B a b}
    : Deriv Γ A a
    → Deriv Γ B b
    → Deriv Γ (.prod A B) (.pair a b)
  | fst {Γ A B p}
    : Deriv Γ (.prod A B) p
    → Deriv Γ A (.fst p)
  | snd {Γ A B p}
    : Deriv Γ (.prod A B) p
    → Deriv Γ B (.snd p)
```
A spot of notation:
```
notation Γ " ⊢ " a " : " A => Ctx.Deriv Γ A a
```
I am so glad that, now that I'm back on the boat, I have AI back. I've gotten into the unfortunate
habit of waiting a split second for a tab-completion, like I'm trying to penetrate a Holtzman shield
or something. 

But I digress. Our first sanity-check is verifying that well typed terms are always locally closed;
that is, we want
```lean
theorem Ctx.Deriv.lc {Γ a A} (ha : Γ ⊢ a : A) : a.bvi = 0
```
To prove this, we'll need some lemmas to relate $\mathsf{bvi}(a^x)$ and $\mathsf{bvi}(a)$. But I'm
running out of battery. Let's continue at the hotel...

- Rode out of the ship
- Clutch started slipping
- Stopped and tightened it, clutch lore is important, yo
- Rode onwards to hotel

We've arrived at [l'Emmanuella](https://www.lemmanuella.fr/), the host has given us some tea, and
it's time to get back to it. So.
```lean
theorem Tm.bvi_le_substUnder_var (n : ℕ) (x : String) (b : Tm)
  : bvi b ≤ (n + 1) ⊔ (bvi (substUnder n x b) + 1)
  := by induction b generalizing n <;> grind [bvi, substUnder, wkUnder]

theorem Tm.pow_def (b : Tm) (a : Tm) : b ^ a = substUnder 0 a b := rfl

theorem Tm.pow_var_def (x : String) (b : Tm) : b ^ x = substUnder 0 x b := rfl

theorem Tm.bvi_le_subst_var (x : String) (b : Tm)
  : bvi b ≤ bvi (b ^ x) + 1
  := by convert bvi_le_substUnder_var 0 x b using 1; simp [Tm.pow_var_def]

theorem Tm.bvi_substUnder_var_le (n : ℕ) (x : String) (b : Tm)
  : bvi (substUnder n x b) ≤ n ⊔ (bvi b - 1)
  := by induction b generalizing n <;> grind [bvi, substUnder, wkUnder]

theorem Tm.bvi_subst_var_le (x : String) (b : Tm) : bvi (b ^ x) ≤ bvi b - 1
  := by convert b.bvi_substUnder_var_le 0 x using 1; simp

theorem Tm.subst_var_lc {x : String} {b : Tm} : bvi (b ^ x) = 0 ↔ bvi b - 1 = 0
  := by have h := b.bvi_le_subst_var x; have h' := b.bvi_subst_var_le x; omega
```
I love the new `grind` tactic. Let's import some utilities to be able to instantiate elements which
are not members of a finite subset of an infinite set:
```lean
import Mathlib.Data.Set.Finite.Basic
```
and
```lean
theorem Tm.subst_var_lc_cf {L : Finset String} {b : Tm} : (∀x ∉ L, bvi (b ^ x) = 0) ↔ bvi b - 1 = 0
  := by
  simp only [subst_var_lc]
  exact ⟨fun h => have ⟨x, hx⟩ := L.exists_notMem; h x hx, fun h _ _ => h⟩

theorem Ctx.Deriv.lc {Γ a A} (ha : Γ ⊢ a : A) : a.bvi = 0
  := by induction ha with
  | _ =>
    (try simp only [Tm.subst_var_lc_cf] at *)
    grind [Tm.bvi]
```
I _really_ love the new `grind` tactic.

It's about 9:43 PM, and I need to fill in the photos and travel bits, give this article some AI
✨polish✨ and get to sleep, since I'm attempting to fix my sleep schedule using one of the more
exciting methodologies. I've also got to look into accomodation for tomorrow, and continue planning
my journey. So let's.

Our current commit is
(c97481b)[https://github.com/imbrem/ln-stlc/commit/c97481b5c8d99664b798d9df49b9c68d46e586c9], tagged
as [`stlc-part-1`](https://github.com/imbrem/ln-stlc/releases/tag/stlc-part-1) on GitHub.

Toodles.