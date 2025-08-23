---
title: Adventures in Type Theory -- Locally Nameless STLC (Part 1)
published: '2025-08-24'
---

It’s been a while. 

As I wrap up my PhD, I decided to take on a few side adventures while writing the thesis. I’ve also
built up a backlog of things I’ve wanted to write, and while the best time to start was yesterday,
the second-best is now.

We're beginning with a motorcycle ride from Cambridge to Termini Imerese in Sicily, covering about
2700 kilometers. It's going to be fun. 

Along the way, we'll try to cover how to formalize locally nameless things in Lean in detail, which
hopefully we'll eventually condense into an ArXiv article or two without the associated travelogue.
We're starting from the basics with the simply typed lambda calculus, inspired by [Arthur
Charguéraud's excellent locally nameless
tutorial](https://chargueraud.org/research/2009/ln/main.pdf).

Without further ado, let's get started.

# Project Setup

_Location_: [Costa Coffee at Dover Port](https://maps.app.goo.gl/oCjnigXkBzY5CwH56)
            (51.12508, 1.33273)

_Time_: 2025-08-23T12:30+1

My laptop is open, but I can't find a charging port. I am sipping the traditional hazelnut latte,
remembering long-ago days in Beirut where I drank the same thing at the ABC mall, before looking out
a rain-streaked window at the Order of Engineers in Tripoli and chipping away at an ever-shifting,
perfectionistic implementation of [ProTem](https://www.cs.toronto.edu/~hehner/PT.pdf), which is how
I got into this mess.

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

The ferry is leaving at 14:00; we've got about 15 minutes until we need to rush back over. Let's see
if we can code up some syntax. Opening up `LnStlc/Basic.lean`, we'll start with our types:
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
Let's throw in an import for $ℕ$ syntax
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
5 minutes left. As a sanity check, let's define the _binding depth_ of a term and bounce[^1].
```lean
/-- The _binding depth_ of an STLC term `t`

    This is defined to be the minimal `k` such that `t` is closed at level `k`.
    
    We say `t` is closed at level `k` if and only if all unbound de Bruijn indices in `t` are `< n`.
    In particular, the following are equivalent:
    - `t` is locally closed
    - `t` is closed at level 0,  i.e. it does not contain any unbound de Bruijn indices.
    - `t` has binding depth 0-/
def Tm.bvi : Tm → ℕ
| .fv _ => 0
| .bv i => i + 1
| .null => 0
| .abs _ body => bvi body - 1
| .pair lhs rhs => bvi lhs ⊔ bvi rhs
| .fst p => bvi p
| .snd p => bvi p
```
Let's get to the ferry...

<div style="text-align: center">
<img src={motorbike_laptop} alt="My laptop perched on my motorbike, along with a coffee cup, my
  keys, and my gloves." style="max-width: 70%" />
</div>

Luckily, we arrived with time to spare, so I've got 20 minutes to keep hacking. 

We can now define the set of _free variables_ which appears in our term in the obvious manner. We
begin by importing the type of _finite sets_,
[`Finset`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Defs.html#Finset),
from mathlib, along with some lemmas:
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
This corresponds exactly to the function $\mathsf{fv}$ from [page 9 of the
tutorial](https://www.chargueraud.org/research/2009/ln/main.pdf).

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
Man, time constraints are an _excellent_ tool for avoiding premature optimization. And
meta-tangents, hopefully.

So, this is a pretty simple function. We note that:
- When we weaken a bound variable,
    - If we're under `n`, we leave it alone
    - Otherwise, we increment it
- Every time we go under a binder, we increment the number of binders we're under by 1.
  Here, the only case where this happens is `.abs`
We'll introduce some syntax sugar $↑_0 t$ for weakening $t$ under no binders:
```lean
prefix:70 "↑₀" => Tm.wkUnder 0
```
And we can now, with just 2 minutes to spare, define substitution under $n$ binders as follows:
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
Mmm, `n a p`. I do not like waking up early. 

But I digress! So again, similarly to weakening:
- When we substitute a bound variable
    - If we're under `n`, we leave it alone
    - If we're _at_ `n`, we replace it with `a`
    - Otherwise, we decrement it
- Every time we go under a binder, we increment the number of binders we're under by 1. We also
  weaken the value we're substituting, to avoid capturing variables from the binder!

And there we go! We've now got everything we need to give our typing rules. It's 14:03 and the ferry
still hasn't arrived, though they said it will be on time, so let's see how far we can get until
then. The power of locally nameless is truly immense!

# Typing Rules

_Location:_ somewhere in the Strait of Dover, on the way to Dunkirk

_Time:_ 2025-08-23T15:30+1

Just as I got to defining contexts, someone came to collect my ticket, and it was time to ride off.
I boarded the ferry and strapped down the Gladius:
<div style="text-align: center">
<img src={motorbike_ferry} alt="My motorbike strapped down on the ferry" style="max-width: 70%" />
</div>
While someone strapped it down for me, when it came time to _unstrap_ it, I was glad I had learned
how to use a ratchet strap during my Z650 recovery adventure. But that's a story for another time.
We bid the white cliffs of Dover farewell
<div style="text-align: center">
<img src={dover_cliffs} alt="The white cliffs of Dover visible as we exit the port" style="max-width: 70%" />
</div>
and sit down to continue working with an exceedingly overpriced (I think it was £14.99) plate of 
fish and chips. I was hungry, to be fair.
<div style="text-align: center">
<img src={ship_office} alt="My laptop, and some overpriced fish and chips, on the ferry to Dunkirk" style="max-width: 70%" />
</div>

So. Contexts. 

Which are just going to be lists of variables mapped to types. 

It's an interesting question whether we want to allow duplicating variable names in our contexts or
not; if we do, we obviously want the _latest_ typing of a variable to hold. Usually, I forbid this
in the context well-formedness judgement[^2], but this is a simple type system, so there won't be a
well-formedness judgement. Which means we need to do this in the type or not at all. 

I don't want to complicate my types, and I trust in the magic of cofinite quantification, so let's
just not:
```lean
inductive Ctx : Type
| nil
| cons (Γ : Ctx) (x : String) (A : Ty)
```
We can now define a judgement for a variable's type as follows:
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
first. That's because I'm thinking of this as the set of variables of type $A$ in $Γ$; it would in
fact _be_ a Lean `Set` if we replaced `Type` with `Prop`.

We can now get to our typing rules. We start by, as usual, introducing a spot of notation, this time
using the [`Pow`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Pow)
typeclass to overload the `^` operator:
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
Our primary typing judgement will take the form
```lean
inductive Ctx.Deriv : Ctx → Ty → Tm → Type
```
Again, we put the type first as we're thinking about "the set of terms of type $A$ in $Γ$", and also
because we're thinking about "a morphism from $Γ$ to $A$". 

And we return a `Type`, rather than a `Prop`, in case we want to have fun with that aforementioned
morphism idea; that's also why we call it `Deriv` rather than `HasTy`. 

I see land on the horizon. But we've got 45 minutes, I think. So let's continue. 

Our typing rules are exceedingly standard:
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
  - $b$ is _not_ necessarily locally closed, since we bind the $λ$ using a de Bruijn index
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

Translated to Lean, that all becomes
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
You know, I am so glad that, now that I'm back on the boat, I have AI back. I've gotten into the
unfortunate habit of waiting a split second for a tab-completion, like I'm trying to penetrate a
Holtzman shield or something. On second thought, perhaps that's not ideal.

We add a dash of notation:
```lean
notation Γ " ⊢ " a " : " A => Ctx.Deriv Γ A a
```

# Well-Typed Terms are Locally Closed

_Location:_ [L'Emanuella](https://www.lemmanuella.fr/), Isbergues (50.61313, 2.45165)

_Time:_ 2025-08-23T20:45+2

As I began to prove some properties of well-typed terms, my laptop ran out of battery, and I
realized that I had forgotten my European-to-UK adapters, and all the plugs on the ferry were EU. I
also realized all three of my phones were running out of battery, most worryingly, including the
navigation phone. This would be fun. And no adapters on board. Obviously. I'm surprised they didn't
try to sell me one, seems like it would be a win-win.

I ride off the ferry and, after filling up, notice that my clutch is slipping again—despite having
just replaced it. The lever had no free play — the cable was taut. Easy fix: I stopped at a
supermarket and tightened it with the inline adjuster near the frame, since the lever adjuster was
already maxed out. Thankfully, no need to touch the engine-side adjuster hidden behind a plate.
Picture attached.

<div style="text-align: center">
<img src={clutch_adjustment} alt="Adjusting the clutch cable on the Gladius." style="max-width: 40%" />
</div>

Anyway, I finally arrive at the hotel, and after putting my stuff away, am treated to a nice tea by
the wonderful host, with whom I practice my French. Definitely getting an excellent review[^4].

So. Type theory.

Our first sanity-check is verifying that well-typed terms are always locally closed; that is, we
want
```lean
theorem Ctx.Deriv.lc {Γ a A} (ha : Γ ⊢ a : A) : a.bvi = 0
```
To prove this, we'll need some lemmas to relate $\mathsf{bvi}(a^x)$ and $\mathsf{bvi}(a)$. Let's
keep it simple: it's obvious that
$$
\mathsf{bvi}(b^x) = 0 \iff \mathsf{bvi}(b) \leq 1
$$
We'll write this as `bvi b - 1 = 0`, using saturating subtraction on $ℕ$, to play nicely with 
`grind`.

We want to prove this by induction, so we want to figure out the corresponding fact about
`substUnder` (with a variable argument $x$). The obvious thing to do is to try comparing `bvi b` and
`bvi (substUnder n x b)` directly, but that doesn't _quite_ work, since
- For the substituted variable $i = n$, `bvi b = n + 1`, which is not $≤$ `bvi (substUnder n x b) +
  1 = bvi x + 1 = 1`
- For variables $i < n$, `bvi (substUnder n x b) = bvi b`, which is not $≤$ `bvi b - 1` for 
  `bvi b ≠ 0`
So, we instead do
```lean
theorem Tm.bvi_le_substUnder_var (n : ℕ) (x : String) (b : Tm)
  : bvi b ≤ (n + 1) ⊔ (bvi (substUnder n x b) + 1)
  := by induction b generalizing n <;> grind [bvi, substUnder, wkUnder]

theorem Tm.bvi_substUnder_var_le (n : ℕ) (x : String) (b : Tm)
  : bvi (substUnder n x b) ≤ n ⊔ (bvi b - 1)
  := by induction b generalizing n <;> grind [bvi, substUnder, wkUnder]
```
Man, I love `grind`. 

This specializes to $b^x$ in the obvious manner:
```lean
theorem Tm.pow_def (b : Tm) (a : Tm) : b ^ a = substUnder 0 a b := rfl

theorem Tm.pow_var_def (x : String) (b : Tm) : b ^ x = substUnder 0 x b := rfl

theorem Tm.bvi_le_subst_var (x : String) (b : Tm)
  : bvi b ≤ bvi (b ^ x) + 1
  := by convert bvi_le_substUnder_var 0 x b using 1; simp [Tm.pow_var_def]

theorem Tm.bvi_subst_var_le (x : String) (b : Tm) : bvi (b ^ x) ≤ bvi b - 1
  := by convert b.bvi_substUnder_var_le 0 x using 1; simp
```
giving us the desired result immediately
```lean
theorem Tm.subst_var_lc {x : String} {b : Tm} : bvi (b ^ x) = 0 ↔ bvi b - 1 = 0
  := by have h := b.bvi_le_subst_var x; have h' := b.bvi_subst_var_le x; omega
```
To be able to prove our desired result conveniently, we want to rephrase this to talk about the
cofinite quantification $∀x ∉ L . \mathsf{bvi}(b^x) = 0$, corresponding to the inductive hypothesis
for the `abs` case. We import some utilities:
```lean
import Mathlib.Data.Set.Finite.Basic
```
and prove
```lean
theorem Tm.subst_var_lc_cf {L : Finset String} {b : Tm} : (∀x ∉ L, bvi (b ^ x) = 0) ↔ bvi b - 1 = 0
  := by
  simp only [subst_var_lc]
  exact ⟨fun h => have ⟨x, hx⟩ := L.exists_notMem; h x hx, fun h _ _ => h⟩
```
The actual theorem is then as simple as
```lean
theorem Ctx.Deriv.lc {Γ a A} (ha : Γ ⊢ a : A) : a.bvi = 0
  := by induction ha with
  | _ =>
    (try simp only [Tm.subst_var_lc_cf] at *)
    grind [Tm.bvi]
```
I _really_ love `grind`.

It's about 9:43 PM, and I need to fill in the photos and travel bits, give this article some AI
✨polish✨ and, finally, fall into hypersleep. So let's call it a day

# Conclusion

 [L'Emanuella](https://www.lemmanuella.fr/), Isbergues (50.61313, 2.45165)

_Time:_ 2025-08-24T00:04+2

Next time, we'll begin to tackle weakening and substitutions. This article's code can be found
[on Github](https://github.com/imbrem/ln-stlc/releases/tag/stlc-part-1m), at commit
[c97481b](https://github.com/imbrem/ln-stlc/commit/c97481b5c8d99664b798d9df49b9c68d46e586c9).

My plan for the _Adventures in Type Theory_ series is:
- Write each article on the road; you can see the live commits to the text on [my
  GitHub](https://github.com/imbrem/tekne.dev)
- Polish and publish during downtime; this may be irregular, because riding, and also thesis.
  And also [covalence](https://github.com/imbrem/covalence).
  A lot of the writing may very well be about thesis/covalence, and related musings.

Now, it's time to catch up on sleep, perhaps after a bit of polish, because we've got a lot of
planning to do tomorrow! And we've got to find accommodation. Fight perfectionism! Just upload it.

Toodles.

[^1]: I tend to write this as `bvi` (*B*ound *V*ariable *I*ndex) in my code

[^2]: In fact, [the tutorial](https://www.chargueraud.org/research/2009/ln/main.pdf) uses a
    well-formedness judgement on page 19 to do exactly that

[^3]: That solved it. I mention this because I once destroyed the clutch on my KTM125 riding back
  from Paris, because I didn't actually know what a slipping clutch was. The speed-to-RPM ratio had
  gone nonlinear, it wasn't accelerating properly, and I didn't know what could be wrong except that
  I had overfilled the oil —it felt like riding with the clutch half-pulled (duh), but I didn't put
  it that succinctly to ChatGPT, and so it did not inform me my clutch was slipping. £500 later, the
  moral of the story: if your speed doesn’t match your RPMs, check your clutch cable, and make sure
  your lever has some free play. Adjusting it is easy.

[^4]: And they're good with bikes, too! They've got secure storage in the back, though overall it's
      a secure area and paranoid as I am I was too lazy to unlock it so they could move it in. Owner
      rides a 500cc Honda. Very based.

<script>
    import motorbike_laptop from "$lib/assets/locally-nameless-stlc/motorbike_laptop.jpg"
    import motorbike_ferry from "$lib/assets/locally-nameless-stlc/motorbike_ferry.jpg"
    import dover_cliffs from "$lib/assets/locally-nameless-stlc/dover_cliffs.jpg"
    import ship_office from "$lib/assets/locally-nameless-stlc/ship_office.jpg"
    import clutch_adjustment from "$lib/assets/locally-nameless-stlc/clutch_adjustment.jpg"
</script>