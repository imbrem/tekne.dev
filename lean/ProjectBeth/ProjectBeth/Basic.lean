import Mathlib.Data.Nat.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.Subtype
import Mathlib.Data.Set.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Lattice.Nat


/-!
Basic theory of ℶω and STLC
-/

inductive HTm (τ : Type _) (ν : ℕ → Type _) : ℕ → Type _
| inj : ν n → HTm τ ν n
| app : HTm τ ν n → HTm τ ν n → HTm τ ν n
| lam : HTm τ ν (n + 1) → HTm τ ν n

def HTm.map₂ (f : τ → τ') (g : ∀ {n}, ν n → ν' n)
: HTm τ ν n → HTm τ' ν' n
| .inj x => .inj (g x)
| .app t₁ t₂ => .app (map₂ f g t₁) (map₂ f g t₂)
| .lam t => .lam (map₂ f g t)

def HTm.erase (t : HTm τ ν n) : HTm Unit ν n
  := t.map₂ (fun _ => ()) id

inductive STy (τ : Type _) : Type _
| inj : τ → STy τ
| arr : STy τ → STy τ → STy τ

def STy.map (f : τ → τ') : STy τ → STy τ'
| .inj x => .inj (f x)
| .arr t₁ t₂ => .arr (map f t₁) (map f t₂)

def STy.shape (t : STy τ) : STy Unit := t.map (fun _ => ())

inductive VCtx (τ : Type _) : ℕ → Type _
| nil : VCtx τ 0
| snoc : VCtx τ n → τ → VCtx τ (n + 1)

namespace VCtx

def len (_ : VCtx τ n) : ℕ := n

def castLen {n m} (h : n = m) (Γ : VCtx τ n) : VCtx τ m := h ▸ Γ

@[simp]
theorem castLen_refl {n} (Γ : VCtx τ n) : castLen rfl Γ = Γ := rfl

@[simp]
theorem castLen_castLen {n m k} (h₁ : n = m) (h₂ : m = k) (Γ : VCtx τ n)
  : castLen h₂ (castLen h₁ Γ) = castLen (h₁.trans h₂) Γ
  := by cases h₁; cases h₂; rfl

def Atom (_ : VCtx τ n) : Type := τ

def map (f : τ → τ') : VCtx τ n → VCtx τ' n
| .nil => .nil
| .snoc Γ τ => .snoc (map f Γ) (f τ)

theorem castLen_map {n m} (h : n = m) (f : τ → τ') (Γ : VCtx τ n)
  : castLen h (map f Γ) = map f (castLen h Γ)
  := by cases h; rfl

def toList : VCtx τ n → List τ
| .nil => []
| .snoc Γ τ => toList Γ ++ [τ]

@[simp]
theorem castLen_toList {n m} (h : n = m) (Γ : VCtx τ n)
  : (castLen h Γ).toList = Γ.toList
  := by cases h; rfl

def toType [Hτ : CoeSort τ (Type u)] : VCtx τ n → Type u
| .nil => PUnit
| .snoc Γ τ => (toType Γ) × (τ : Type u)

@[simp]
theorem castLen_toType {n m} [Hτ : CoeSort τ (Type u)] (h : n = m) (Γ : VCtx τ n)
  : (castLen h Γ).toType = Γ.toType
  := by cases h; rfl

instance instCoeList {τ} : CoeOut (VCtx τ n) (List τ) where
  coe v := v.toList

instance instCoeSort {τ} [Hτ : CoeSort τ (Type u)]
  : CoeSort (VCtx τ n) (Type u) where
  coe v := v.toType

inductive Wk {τ : Type _} : ∀ {n m}, VCtx τ n → VCtx τ m → Type _
| nil : VCtx.Wk .nil .nil
| lift : ∀ {n m} {Γ : VCtx τ n} {Δ : VCtx τ m} {t : τ},
  VCtx.Wk Γ Δ → VCtx.Wk (VCtx.snoc Γ t) (VCtx.snoc Δ t)
| skip : ∀ {n m} {Γ : VCtx τ n} {Δ : VCtx τ m} {t : τ},
  Wk Γ Δ → Wk (Γ.snoc t) Δ

namespace Wk

@[simp]
theorem len_le {Γ : VCtx τ n} {Δ : VCtx τ m} (w : Wk Γ Δ) : m ≤ n :=
  by induction w <;> omega

def refl {τ : Type _} {n} : (Γ : VCtx τ n) → VCtx.Wk Γ Γ
| .nil => .nil
| .snoc Γ τ => .lift (refl Γ)

theorem lift_refl {τ : Type _} {n t}
  {Γ : VCtx τ n}
  : Wk.lift (t := t) (.refl Γ) = .refl (Γ.snoc t) := rfl

theorem eq_castLen_of_len_eq {n m} {Γ : VCtx τ n} {Δ : VCtx τ m}
  (w : Wk Γ Δ) (h : m = n) : Γ = Δ.castLen h
  := by
  induction w with
  | nil => rfl
  | lift w ih => cases h; simp only [castLen_refl, ih]
  | skip w ih => have hw := w.len_le; omega

def castSrcLen {n n' m}
  {Γ : VCtx τ n} {Δ : VCtx τ m} (w : Wk Γ Δ) (h : n = n')
  : Wk (castLen h Γ) Δ := by cases h; exact w

def castTrgLen {n m m'}
  {Γ : VCtx τ n} {Δ : VCtx τ m} (w : Wk Γ Δ) (h : m = m')
  : Wk Γ (castLen h Δ) := by cases h; exact w

def castLen {n n' m m'}
  {Γ : VCtx τ n} {Δ : VCtx τ m}
  (w : Wk Γ Δ) (h₁ : n = n') (h₂ : m = m')
  : Wk (castLen h₁ Γ) (castLen h₂ Δ) := (w.castSrcLen h₁).castTrgLen h₂

def comp {τ : Type _} {n m k}
  {Γ : VCtx τ n} {Δ : VCtx τ m} {Θ : VCtx τ k}
  : Wk Γ Δ → Wk Δ Θ → Wk Γ Θ
  | .nil, .nil => .nil
  | .lift w₁, .lift w₂ => .lift (comp w₁ w₂)
  | .lift w₁, .skip w₂ => .skip (comp w₁ w₂)
  | .skip w₁, w₂ => .skip (comp w₁ w₂)

theorem refl_unique {τ : Type _} {n}
  {Γ : VCtx τ n} (w : Wk Γ Γ)
  : w = Wk.refl Γ := match w with
  | .nil => rfl
  | .lift w => by rw [refl, w.refl_unique]
  | .skip w => by have hw := w.len_le; omega

theorem comp_refl {τ : Type _} {n m}
  {Γ : VCtx τ n} {Δ : VCtx τ m}
  (w : Wk Γ Δ)
  : Wk.comp w (Wk.refl Δ) = w := by
  induction w with | _ => simp [comp, refl, *]

theorem refl_comp {τ : Type _} {n m}
  {Γ : VCtx τ n} {Δ : VCtx τ m}
  (w : Wk Γ Δ)
  : Wk.comp (Wk.refl Γ) w = w := by
  induction w with | _ => simp [comp, refl, *]

@[simp]
theorem comp_refl' {τ : Type _} {n m}
  {Γ : VCtx τ n} {Δ : VCtx τ m}
  (w : Wk Γ Δ) (rΔ : Wk Δ Δ)
  : Wk.comp w rΔ = w
  := by rw [refl_unique rΔ, comp_refl]

@[simp]
theorem refl_comp' {τ : Type _} {n m}
  {Γ : VCtx τ n} {Δ : VCtx τ m}
  (rΓ : Wk Γ Γ) (w : Wk Γ Δ)
  : Wk.comp rΓ w = w
  := by rw [refl_unique rΓ, refl_comp]

end Wk

end VCtx

/--
Coding as a type
-/
structure Code (α : Type u) (κ : Type v) : Type (max u v) where
  code : α → κ
  car : Set κ := Set.range code
  code_inj : code.Injective
  car_eq_range : car = Set.range code := by rfl

attribute [simp] Code.code_inj

instance Code.instCoe {α κ}
  : CoeOut (Code α κ) (Set κ) where
  coe := Code.car

@[simp]
theorem Code.mem_code_iff {α κ} (coding : Code α κ) (i : κ)
  : i ∈ (coding : Set κ) ↔ ∃a, coding.code a = i
  := by rw [coding.car_eq_range, Set.mem_range]

def Code.refl {κ : Type u} : Code κ κ where
  code := id
  car := Set.univ
  code_inj := Function.injective_id
  car_eq_range := by simp [Set.range]

@[simp]
theorem Code.car_refl {κ : Type u}
  : (Code.refl (κ := κ) : Set κ) = Set.univ
  := rfl

def Code.inj {α κ} (coding : Code α κ) : Code coding κ where
  code i := i.val
  car := coding
  code_inj := Subtype.coe_injective
  car_eq_range := by apply Set.ext; simp

@[simp]
theorem Code.car_inj {α κ} (coding : Code α κ)
  : (Code.inj coding : Set κ) = coding
  := rfl

def Code.emb {F α κ} [hF : FunLike F α κ]
  [hFE : EmbeddingLike F α κ] (f : F) : Code α κ where
  code a := f a
  car := Set.range f
  code_inj := hFE.injective f
  car_eq_range := by apply Set.ext; simp

@[simp]
theorem Code.car_emb {F α κ} [hF : FunLike F α κ]
  [hFE : EmbeddingLike F α κ] (f : F)
  : (Code.emb f : Set κ) = Set.range f
  := rfl

def Code.eqv {F α κ} [hF : EquivLike F α κ] (f : F) : Code α κ where
  code a := f a
  car := Set.univ
  code_inj := hF.injective f
  car_eq_range := Eq.symm <| by simp only [Set.range_eq_univ, EquivLike.surjective]

def Code.comp {α κ κ'}
  (code₁ : Code α κ) (code₂ : Code κ κ') : Code α κ' where
  code a := code₂.code (code₁.code a)
  car := code₂.code '' code₁.car
  code_inj := code₂.code_inj.comp code₁.code_inj
  car_eq_range := by apply Set.ext; simp

@[simp]
theorem Code.car_comp {α κ κ'} (code₁ : Code α κ) (code₂ : Code κ κ')
  : (Code.comp code₁ code₂ : Set κ') = code₂.code '' code₁.car
  := rfl

def Code.mapIn
  {F α β} [hF : FunLike F α β] [hFE : EmbeddingLike F α β] (f : F)
  (coding : Code β κ) : Code α κ
  := (Code.emb f).comp coding

@[simp]
theorem Code.car_mapIn {F α β} [hF : FunLike F α β] [hFE : EmbeddingLike F α β] (f : F)
  (coding : Code β κ)
  : (Code.mapIn f coding : Set κ) = coding.code '' Set.range f
  := rfl

def Code.mapCar
  {F κ κ'} [hF : FunLike F κ κ'] [hFE : EmbeddingLike F κ κ'] (f : F)
  (coding : Code α κ) : Code α κ'
  := coding.comp (Code.emb f)

@[simp]
theorem Code.car_mapCar {F κ κ'} [hF : FunLike F κ κ'] [hFE : EmbeddingLike F κ κ'] (f : F)
  (coding : Code α κ)
  : (Code.mapCar f coding : Set κ') = f '' coding.car
  := rfl

abbrev SumCode (α : Type u) (β : Type v) (κ : Type w) : Type (max u v w) := Code (α ⊕ β) κ

def Code.sum {α κα β κβ : Type _}
  (lcode : Code α κα) (rcode : Code β κβ)
  : SumCode α β (κα ⊕ κβ) where
  code := Sum.map lcode.code rcode.code
  code_inj := by simp

abbrev ProdCode (α : Type u) (β : Type v) (κ : Type w) : Type (max u v w) := Code (α × β) κ

def Code.prod {α κα β κβ : Type _}
  (lcode : Code α κα) (rcode : Code β κβ)
  : ProdCode α β (κα × κβ) where
  code := Prod.map lcode.code rcode.code
  code_inj
  | (a, b), (a', b'), h => by
    simp only [Prod.map_apply, Prod.mk.injEq] at *
    cases h
    constructor <;> apply Code.code_inj <;> assumption

abbrev SetCode (α : Type u) (κ : Type v) : Type (max u v) := Code (Set α) κ

abbrev FunCode (α : Type u) (β : Type v) (κ : Type w) : Type (max u v w) := Code (α → β) κ

abbrev RelCode (α : Type u) (β : Type v) (κ : Type w) : Type (max u v w) := Code (α → β → Prop) κ

class PropCode (κ : Type u) extends Code Prop κ where

instance PropCode.prop : PropCode Prop where
  toCode := Code.refl

noncomputable instance PropCode.nat : PropCode ℕ where
  code i := open Classical in if i then 1 else 0
  code_inj p q := by simp only [eq_iff_iff]; split_ifs <;> simp [*]

instance PropCode.set {κ : Type u} [Inhabited κ] : PropCode (Set κ) where
  code p := {i | p}
  code_inj p q := by simp [Set.ext_iff]

class CopyCode (κ : Type u) extends SumCode κ κ κ where
  car_eq_univ : (toCode : Set κ) = Set.univ := by rfl

instance CopyCode.nat : CopyCode ℕ where
  code := Sum.elim (fun i => 2 * i) (fun i => 2 * i + 1)
  car := Set.univ
  code_inj a b := by cases a <;> cases b <;> simp <;> omega
  car_eq_range := by
    apply Set.ext; intro x;
    simp [x.even_or_odd]

def Code.copy {α β κ : Type _} [Hκ : CopyCode κ]
  (lcode : Code α κ) (rcode : Code β κ) : SumCode α β κ
  := (lcode.sum rcode).comp Hκ.toCode

class PairCode (κ : Type u) extends ProdCode κ κ κ where
  -- car_eq_univ : (toCode : Set κ) = Set.univ := by rfl

instance PairCode.nat : PairCode ℕ where
  toCode := Code.eqv Nat.pairEquiv

def Code.pair {α β κ : Type _} [Hκ : PairCode κ]
  (lcode : Code α κ) (rcode : Code β κ) : ProdCode α β κ
  := (lcode.prod rcode).comp Hκ.toCode

def FunCode.graph₂ {α β : Type _} : FunCode α β (Set (α × β)) where
  code f := { (a, b) | f a = b }
  code_inj p q := by simp [Set.ext_iff, funext_iff]

def RelCode.graph₂ {α β : Type _} : RelCode α β (Set (α × β)) where
  code r := { (a, b) | r a b }
  car := Set.univ
  code_inj p q := by simp [Set.ext_iff, funext_iff]
  car_eq_range := by
    apply Set.ext; simp only [Set.mem_univ, Set.range, Set.mem_setOf_eq, true_iff]
    intro s
    simp only [Set.ext_iff, Set.mem_setOf_eq, Prod.forall]
    exists (fun a b => (a, b) ∈ s)
    simp

def Code.set {α κ : Type _}
  (coding : Code α κ) : Code (Set α) (Set κ) where
  code s := coding.code '' s
  code_inj := by simp [Set.image_injective]

instance PairCode.set {κ : Type _} [Hκ : PairCode κ] : PairCode (Set κ) where
  code | (sa, sb) => Hκ.code '' (Set.prod sa sb)
  code_inj := sorry
  car_eq_range := sorry

def FunCode.graph {α β κ : Type _}
  (lcode : Code α κ) (rcode : Code β κ)
  [PairCode κ] : FunCode α β (Set κ)
  := FunCode.graph₂.comp (lcode.pair rcode).set

def RelCode.graph {α β κ : Type _}
  (lcode : Code α κ) (rcode : Code β κ)
  [PairCode κ] : RelCode α β (Set κ)
  := RelCode.graph₂.comp (lcode.pair rcode).set

class Canon (α κ : Type _) extends Code α κ where

instance Canon.refl {κ : Type u} : Canon κ κ where
  toCode := Code.refl

instance Canon.inj {α κ} (coding : Code α κ) : Canon coding κ where
  toCode := Code.inj coding

def Code.finAdd {n m} : Code (Fin n) (Fin (n + m)) where
  code := Fin.castAdd m
  code_inj := Fin.castAdd_injective n m

instance Canon.finAdd {n m} : Canon (Fin n) (Fin (n + m)) where
  toCode := Code.finAdd

def Code.fin {n} : Code (Fin n) ℕ where
  code := Fin.val
  car := Set.Iio n
  code_inj := Fin.val_injective
  car_eq_range := by apply Set.ext; simp [Fin.exists_iff]

instance Canon.fin {n} : Canon (Fin n) ℕ where
  toCode := Code.fin

def Code.index {κ : Type u} : Code κ (Set κ) where
  code := fun a => {a}
  code_inj := fun _ _ h => by simp only [Set.singleton_eq_singleton_iff] at h; exact h

instance Canon.index {κ : Type u} : Canon κ (Set κ) where
  toCode := Code.index

/--
Type of ℶ cardinals
-/
def ℶ : ℕ → Type
| 0 => ℕ
| n + 1 => Set (ℶ n)

instance ℶ.instLattice {n} : Lattice (ℶ n)
  := match n with
  | 0 => inferInstanceAs (Lattice ℕ)
  | n + 1 => inferInstanceAs (Lattice (Set (ℶ n)))

instance ℶ.instCompleteLattice {n} : CompleteLattice (ℶ (n + 1))
  := inferInstanceAs (CompleteLattice (Set (ℶ n)))

instance ℶ.instLinearOrder : LinearOrder (ℶ 0)
  := inferInstanceAs (LinearOrder ℕ)

def ℶ.toNat (i : ℶ 0) : ℕ := i

@[match_pattern]
def ℶ.set {n} (s : Set (ℶ n)) : ℶ (n + 1) := s

def ℶ.lo {n} (i : ℶ n) : ℶ (n + 1) := .set (Set.Iio i)

def ℶ.toSet {n} (i : ℶ (n + 1)) : Set (ℶ n) := i

theorem ℶ.le_iff_zero (i j : ℶ 0) : i ≤ j ↔ i.toNat ≤ j.toNat
  := Iff.rfl

theorem ℶ.lt_iff_zero (i j : ℶ 0) : i < j ↔ i.toNat < j.toNat
  := Iff.rfl

theorem ℶ.le_iff_succ {n} (i j : ℶ (n + 1)) : i ≤ j ↔ i.toSet ⊆ j.toSet
  := Iff.rfl

theorem ℶ.lt_iff_succ {n} (i j : ℶ (n + 1)) : i < j ↔ i.toSet ⊂ j.toSet
  := Iff.rfl

@[simp]
theorem ℶ.toSet_lo {n} (i : ℶ n) : ℶ.toSet (ℶ.lo i) = Set.Iio i := rfl

theorem ℶ.lo_mono {n} {i j : ℶ n} (h : i ≤ j) : ℶ.lo i ≤ ℶ.lo j
  := by intro x h'; exact lt_of_lt_of_le h' h

def ℶ.hi {n} (i : ℶ n) : ℶ (n + 1) := .set (Set.Ioi i)

@[simp]
theorem ℶ.toSet_hi {n} (i : ℶ n) : ℶ.toSet (ℶ.hi i) = Set.Ioi i := rfl

-- TODO: hi is mono as well

-- TODO: lo and hi are disjoint

def ℶ.toType : ∀{n}, ℶ n → Type
| 0 => Fin
| _ + 1 => fun s => s.toSet

instance ℶ.instSetLike {n} : SetLike (ℶ (n + 1)) (ℶ n) where
  coe := ℶ.toSet
  coe_injective := fun _ _ h => h

@[simp]
theorem ℶ.mem_set_iff {n} (i : ℶ n) (s : Set (ℶ n)) : i ∈ ℶ.set s ↔ i ∈ s
  := Iff.rfl

@[simp]
theorem ℶ.mem_lo_iff (i j : ℶ n) : i ∈ ℶ.lo j ↔ i < j
  := by simp [ℶ.lo]

@[simp]
theorem ℶ.mem_hi_iff (i j : ℶ n) : i ∈ ℶ.hi j ↔ i > j
  := by simp [ℶ.hi]

theorem ℶ.not_mem_lo {n} (i : ℶ n) : i ∉ ℶ.lo i := by simp

theorem ℶ.not_mem_hi {n} (i : ℶ n) : i ∉ ℶ.hi i := by simp

theorem ℶ.lo_zero_inj : Function.Injective (ℶ.lo : ℶ 0 → ℶ 1)
  := by apply Set.Iio_injective

instance ℶ.instSetLikeZero : SetLike (ℶ 0) ℕ where
  coe := ℶ.lo
  coe_injective := lo_zero_inj

@[simp]
theorem ℶ.set_toSet {n} (i : ℶ (n + 1)) : ℶ.set i.toSet = i := rfl

@[simp]
theorem ℶ.toSet_set {n} (s : Set (ℶ n)) : ℶ.toSet (ℶ.set s) = s := rfl

def ℶ.ix {n} (i : ℶ n) : ℶ (n + 1) := .set {i}

@[simp]
theorem ℶ.ix_toSet {n} (i : ℶ n) : ℶ.toSet (ℶ.ix i) = {i} := rfl

theorem ℶ.lo_inj_0 : Function.Injective (ℶ.lo : ℶ 0 → ℶ 1)
  := by apply Set.Iio_injective

-- theorem ℶ.lo_inj_succ : Function.Injective (ℶ.lo : ℶ (n + 1) → ℶ (n + 2)) := by
--   intro a b h
--   apply Set.ext
--   intro x
--   constructor
--   · intro h
--     sorry
--   sorry

instance ℶ.coeSucc {n} : CoeOut (ℶ n) (ℶ (n + 1)) where
  coe := lo

@[simp]
theorem ℶ.coe_toSet {n} (i : ℶ n) : ℶ.toSet (i : ℶ (n + 1)) = Set.Iio i := rfl

def ℶ.num (i : ℕ) : ℶ 0 := i

@[simp]
theorem ℶ.ix_inj {n : ℕ} : Function.Injective (ℶ.ix : ℶ n → ℶ (n + 1)) := by
  apply Set.singleton_injective

instance ℶ.instCoeSort {n} : CoeSort (ℶ n) Type where
  coe := ℶ.toType

class Canonℶ (α : Type _) (n : ℕ) extends Canon α (ℶ n)

instance Canonℶ.nat : Canonℶ ℕ 0 where
  toCanon := inferInstanceAs (Canon ℕ ℕ)

instance Canonℶ.refl {n} : Canonℶ (ℶ n) n where
  toCanon := inferInstanceAs (Canon (ℶ n) (ℶ n))

-- TODO: change to lo?
instance Canonℶ.succ {n} [Hn : Canonℶ α n] : Canonℶ α (n + 1) where
  code := ℶ.ix ∘ Hn.code
  code_inj := ℶ.ix_inj.comp Hn.code_inj

@[instance_reducible]
def ℶ.pairCodeZero : PairCode (ℶ 0) := inferInstanceAs (PairCode ℕ)

-- @[instance_reducible]
-- def ℶ.pairCodeSucc {n} : PairCode (ℶ (n + 1)) := inferInstanceAs (PairCode (Set (ℶ n)))

-- instance ℶ.instPairCode {n} : PairCode (ℶ n) where
--   toCode := Code.eqv Nat.pairEquiv

-- instance Canonℶ.pair {n}
--   [Hn : Canonℶ α n] [Hm : Canonℶ β n] : Canonℶ (α × β) n
--   where
--   toCode := Code.pair Hn Hm

/--
ℶω := ⊔_n ℶ n
-/
def ℶω : Type := Σ (n : ℕ), ℶ n

-- def ℶω.base (k : ℕ) (i : ℕ) : ℶω := ⟨k, ℶ.num i⟩

-- def ℶω.num (i : ℕ) : ℶω := .base 0 i

instance ℶω.instCoeFin {n} : CoeOut (Fin n) ℶω where
  coe x := ⟨0, x.val⟩

instance ℶω.instCoeNat : CoeOut ℕ ℶω where
  coe x := ⟨0, .num x⟩

instance ℶω.instCoeℶ {n} : CoeOut (ℶ n) ℶω where
  coe x := ⟨n, x⟩

/--
Hierarchy of cardinalities smaller than ℶω
-/
inductive ℶC : Type
| fin : ℕ → ℶC
| beth : ℕ → ℶC

instance ℶC.instCoeSort : CoeSort ℶC Type where
  coe
  | .fin n => Fin n
  | .beth n => ℶ n

structure ℶC.Code (α : Type u) (κ : ℶC) : Type u where
  code : α → κ
  code_inj : code.Injective

def ℶC.Code.Car {α κ} (coding : ℶC.Code α κ) : Type
  := { i : κ // ∃ a, coding.code a = i }

def ℶC.Code.refl {κ : ℶC} : ℶC.Code κ κ where
  code := id
  code_inj := Function.injective_id

def ℶC.Code.car {α κ} (coding : ℶC.Code α κ) : ℶC.Code (ℶC.Code.Car coding) κ where
  code i := i.val
  code_inj := Subtype.coe_injective

def ℶC.Code.fin {n} : ℶC.Code (Fin n) (.fin n) := refl (κ := .fin n)

def ℶC.Code.nat : ℶC.Code ℕ (.beth 0) := refl (κ := .beth 0)

def ℶC.Code.beth {n} : ℶC.Code (ℶ n) (.beth n) := refl (κ := .beth n)

def ℶC.Code.map
  {F α β} [hF : FunLike F α β] [hFE : EmbeddingLike F α β] (f : F)
  (coding : ℶC.Code β κ) : ℶC.Code α κ where
  code a := coding.code (f a)
  code_inj := coding.code_inj.comp (hFE.injective f)

instance ℶC.instCoeω {κ : ℶC} : CoeOut κ ℶω where
  coe := match κ with
  | .fin _ => ℶω.instCoeFin.coe
  | .beth _ => ℶω.instCoeℶ.coe
