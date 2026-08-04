import ProjectBeth.Defs.STLC.Variants
import ProjectBeth.Defs.PowerTower

/-! Relational and partial-equivalence-relation semantics for STLC fragments. -/

universe u v w

namespace ProjectBeth.STLC.Relational

abbrev Rel (α : Type u) (β : Type v) := α → β → Prop

def Rel.id : Rel α α := Eq
def Rel.comp (R : Rel α β) (S : Rel β γ) : Rel α γ :=
  fun x z => ∃ y, R x y ∧ S y z
def Rel.prod (R : Rel α β) (S : Rel γ δ) : Rel (α × γ) (β × δ) :=
  fun x y => R x.1 y.1 ∧ S x.2 y.2
def Rel.sum (R : Rel α β) (S : Rel γ δ) : Rel (α ⊕ γ) (β ⊕ δ)
  | .inl x, .inl y => R x y
  | .inr x, .inr y => S x y
  | _, _ => False
def Rel.arrow (R : Rel α β) (S : Rel γ δ) : Rel (α → γ) (β → δ) :=
  fun f g => ∀ x y, R x y → S (f x) (g y)

theorem Rel.comp_id_left (R : Rel α β) : Rel.comp Rel.id R = R := by
  funext x y; apply propext; constructor
  · rintro ⟨z, rfl, h⟩; exact h
  · intro h; exact ⟨x, rfl, h⟩

theorem Rel.comp_id_right (R : Rel α β) : Rel.comp R Rel.id = R := by
  funext x y; apply propext; constructor
  · rintro ⟨z, h, rfl⟩; exact h
  · intro h; exact ⟨y, h, rfl⟩

theorem Rel.comp_assoc (R : Rel α β) (S : Rel β γ) (T : Rel γ δ) :
    Rel.comp (Rel.comp R S) T = Rel.comp R (Rel.comp S T) := by
  funext x y; apply propext; constructor
  · rintro ⟨z, ⟨q, hR, hS⟩, hT⟩; exact ⟨q, hR, z, hS, hT⟩
  · rintro ⟨q, hR, z, hS, hT⟩; exact ⟨z, ⟨q, hR, hS⟩, hT⟩

/-- A partial equivalence relation; reflexivity is required only on its field. -/
structure PER (α : Type u) where
  rel : Rel α α
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

def PER.Field (R : PER α) (x : α) : Prop := R.rel x x

theorem PER.left_mem {R : PER α} (h : R.rel x y) : R.Field x :=
  R.trans h (R.symm h)

theorem PER.right_mem {R : PER α} (h : R.rel x y) : R.Field y :=
  R.trans (R.symm h) h

def PER.id (α : Type u) : PER α where
  rel := Eq
  symm := Eq.symm
  trans := Eq.trans

def PER.prod (R : PER α) (S : PER β) : PER (α × β) where
  rel := Rel.prod R.rel S.rel
  symm h := ⟨R.symm h.1, S.symm h.2⟩
  trans h k := ⟨R.trans h.1 k.1, S.trans h.2 k.2⟩

def PER.sum (R : PER α) (S : PER β) : PER (α ⊕ β) where
  rel := Rel.sum R.rel S.rel
  symm := by
    intro x y h
    cases x <;> cases y <;> simp [Rel.sum] at h ⊢
    · exact R.symm h
    · exact S.symm h
  trans := by
    intro x y z h k
    cases x <;> cases y <;> cases z <;> simp [Rel.sum] at h k ⊢
    · exact R.trans h k
    · exact S.trans h k

def PER.arrow (R : PER α) (S : PER β) : PER (α → β) where
  rel := Rel.arrow R.rel S.rel
  symm h x y hxy := S.symm (h y x (R.symm hxy))
  trans h k x y hxy := S.trans (h x x (R.trans hxy (R.symm hxy))) (k x y hxy)

abbrev BethRel := Rel ProjectBeth.BethOmega ProjectBeth.BethOmega
abbrev BethPER := PER ProjectBeth.BethOmega

namespace Arrow

def Ty.per {Base : Type u} {El : Base → Type v} (base : ∀ X, PER (El X)) :
    (A : STLC.Arrow.Ty Base) → PER (STLC.Arrow.Ty.denote El A)
  | .base X => base X
  | .arr A B => PER.arrow (Ty.per base A) (Ty.per base B)

def Ty.rel {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) :
    (A : STLC.Arrow.Ty Base) →
      Rel (STLC.Arrow.Ty.denote El A) (STLC.Arrow.Ty.denote El' A)
  | .base X => base X
  | .arr A B => Rel.arrow (Ty.rel base A) (Ty.rel base B)

def Env.rel {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) : {Γ : List (STLC.Arrow.Ty Base)} →
    STLC.Env (STLC.Arrow.Ty.denote El) Γ →
    STLC.Env (STLC.Arrow.Ty.denote El') Γ → Prop
  | [], _, _ => True
  | A :: _Γ, ρ, ρ' => Ty.rel base A ρ.1 ρ'.1 ∧ Env.rel base ρ.2 ρ'.2

theorem lookup {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) {Γ} {A}
    (x : STLC.Var Γ A) {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.rel base A (x.lookup ρ) (x.lookup ρ') := by
  induction x with
  | here => exact h.1
  | there x ih => exact ih h.2

theorem fundamental {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) {Γ} {A}
    (t : STLC.Arrow.Tm Γ A) {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.rel base A (t.denote El ρ) (t.denote El' ρ') := by
  induction t with
  | var x => exact lookup base x h
  | app f x ihf ihx => exact ihf h _ _ (ihx h)
  | lam body ih => intro x y hxy; exact ih ⟨hxy, h⟩

end Arrow

namespace ArrowProd

def Ty.per {Base : Type u} {El : Base → Type v} (base : ∀ X, PER (El X)) :
    (A : STLC.ArrowProd.Ty Base) → PER (STLC.ArrowProd.Ty.denote El A)
  | .base X => base X
  | .arr A B => PER.arrow (Ty.per base A) (Ty.per base B)
  | .prod A B => PER.prod (Ty.per base A) (Ty.per base B)

def Ty.rel {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) : (A : STLC.ArrowProd.Ty Base) →
    Rel (STLC.ArrowProd.Ty.denote El A) (STLC.ArrowProd.Ty.denote El' A)
  | .base X => base X
  | .arr A B => Rel.arrow (Ty.rel base A) (Ty.rel base B)
  | .prod A B => Rel.prod (Ty.rel base A) (Ty.rel base B)

def Env.rel {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) : {Γ : List (STLC.ArrowProd.Ty Base)} →
    STLC.Env (STLC.ArrowProd.Ty.denote El) Γ →
    STLC.Env (STLC.ArrowProd.Ty.denote El') Γ → Prop
  | [], _, _ => True
  | A :: _Γ, ρ, ρ' => Ty.rel base A ρ.1 ρ'.1 ∧ Env.rel base ρ.2 ρ'.2

theorem lookup {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) {Γ} {A} (x : STLC.Var Γ A)
    {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.rel base A (x.lookup ρ) (x.lookup ρ') := by
  induction x with
  | here => exact h.1
  | there x ih => exact ih h.2

theorem fundamental {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) {Γ} {A}
    (t : STLC.ArrowProd.Tm Γ A) {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.rel base A (t.denote El ρ) (t.denote El' ρ') := by
  induction t with
  | var x => exact lookup base x h
  | app f x ihf ihx => exact ihf h _ _ (ihx h)
  | lam body ih => intro x y hxy; exact ih ⟨hxy, h⟩
  | pair a b iha ihb => exact ⟨iha h, ihb h⟩
  | fst p ih => exact (ih h).1
  | snd p ih => exact (ih h).2

end ArrowProd

namespace ArrowProdSum

def Ty.per {Base : Type u} {El : Base → Type v} (base : ∀ X, PER (El X)) :
    (A : STLC.ArrowProdSum.Ty Base) → PER (STLC.ArrowProdSum.Ty.denote El A)
  | .base X => base X
  | .arr A B => PER.arrow (Ty.per base A) (Ty.per base B)
  | .prod A B => PER.prod (Ty.per base A) (Ty.per base B)
  | .sum A B => PER.sum (Ty.per base A) (Ty.per base B)

def Ty.rel {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) : (A : STLC.ArrowProdSum.Ty Base) →
    Rel (STLC.ArrowProdSum.Ty.denote El A) (STLC.ArrowProdSum.Ty.denote El' A)
  | .base X => base X
  | .arr A B => Rel.arrow (Ty.rel base A) (Ty.rel base B)
  | .prod A B => Rel.prod (Ty.rel base A) (Ty.rel base B)
  | .sum A B => Rel.sum (Ty.rel base A) (Ty.rel base B)

def Env.rel {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) : {Γ : List (STLC.ArrowProdSum.Ty Base)} →
    STLC.Env (STLC.ArrowProdSum.Ty.denote El) Γ →
    STLC.Env (STLC.ArrowProdSum.Ty.denote El') Γ → Prop
  | [], _, _ => True
  | A :: _Γ, ρ, ρ' => Ty.rel base A ρ.1 ρ'.1 ∧ Env.rel base ρ.2 ρ'.2

theorem lookup {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) {Γ} {A} (x : STLC.Var Γ A)
    {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.rel base A (x.lookup ρ) (x.lookup ρ') := by
  induction x with
  | here => exact h.1
  | there x ih => exact ih h.2

theorem fundamental {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) {Γ} {A}
    (t : STLC.ArrowProdSum.Tm Γ A) {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.rel base A (t.denote El ρ) (t.denote El' ρ') := by
  induction t with
  | var x => exact lookup base x h
  | app f x ihf ihx => exact ihf h _ _ (ihx h)
  | lam body ih => intro x y hxy; exact ih ⟨hxy, h⟩
  | pair a b iha ihb => exact ⟨iha h, ihb h⟩
  | fst p ih => exact (ih h).1
  | snd p ih => exact (ih h).2
  | inl x ih => exact ih h
  | inr x ih => exact ih h
  | case s l r ihs ihl ihr =>
    have hs := ihs h
    cases hsl : s.denote El ρ <;> cases hsr : s.denote El' ρ' <;>
      simp [Ty.rel, Rel.sum, hsl, hsr] at hs
    · simpa [STLC.ArrowProdSum.Tm.denote, hsl, hsr] using ihl ⟨hs, h⟩
    · simpa [STLC.ArrowProdSum.Tm.denote, hsl, hsr] using ihr ⟨hs, h⟩

end ArrowProdSum

namespace Full

def Ty.per {Base : Type u} {El : Base → Type v} (base : ∀ X, PER (El X)) :
    (A : STLC.Full.Ty Base) → PER (STLC.Full.Ty.denote El A)
  | .base X => base X
  | .arr A B => PER.arrow (Ty.per base A) (Ty.per base B)
  | .prod A B => PER.prod (Ty.per base A) (Ty.per base B)
  | .sum A B => PER.sum (Ty.per base A) (Ty.per base B)
  | .bool => PER.id _
  | .nat => PER.id _

def Ty.rel {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) : (A : STLC.Full.Ty Base) →
    Rel (STLC.Full.Ty.denote El A) (STLC.Full.Ty.denote El' A)
  | .base X => base X
  | .arr A B => Rel.arrow (Ty.rel base A) (Ty.rel base B)
  | .prod A B => Rel.prod (Ty.rel base A) (Ty.rel base B)
  | .sum A B => Rel.sum (Ty.rel base A) (Ty.rel base B)
  | .bool => fun x y => x.down = y.down
  | .nat => fun x y => x.down = y.down

def Env.rel {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) : {Γ : List (STLC.Full.Ty Base)} →
    STLC.Env (STLC.Full.Ty.denote El) Γ →
    STLC.Env (STLC.Full.Ty.denote El') Γ → Prop
  | [], _, _ => True
  | A :: _Γ, ρ, ρ' => Ty.rel base A ρ.1 ρ'.1 ∧ Env.rel base ρ.2 ρ'.2

theorem lookup {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) {Γ} {A} (x : STLC.Var Γ A)
    {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.rel base A (x.lookup ρ) (x.lookup ρ') := by
  induction x with
  | here => exact h.1
  | there x ih => exact ih h.2

theorem fundamental {Base : Type u} {El : Base → Type v} {El' : Base → Type w}
    (base : ∀ X, Rel (El X) (El' X)) {Γ} {A}
    (t : STLC.Full.Tm Γ A) {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.rel base A (t.denote El ρ) (t.denote El' ρ') := by
  induction t with
  | var x => exact lookup base x h
  | app f x ihf ihx => exact ihf h _ _ (ihx h)
  | lam body ih => intro x y hxy; exact ih ⟨hxy, h⟩
  | pair a b iha ihb => exact ⟨iha h, ihb h⟩
  | fst p ih => exact (ih h).1
  | snd p ih => exact (ih h).2
  | inl x ih => exact ih h
  | inr x ih => exact ih h
  | case s l r ihs ihl ihr =>
    have hs := ihs h
    cases hsl : s.denote El ρ <;> cases hsr : s.denote El' ρ' <;>
      simp [Ty.rel, Rel.sum, hsl, hsr] at hs
    · simpa [STLC.Full.Tm.denote, hsl, hsr] using ihl ⟨hs, h⟩
    · simpa [STLC.Full.Tm.denote, hsl, hsr] using ihr ⟨hs, h⟩
  | bool b => rfl
  | nat n => rfl
  | ite c t e ihc iht ihe =>
    have hc := ihc h
    simp only [STLC.Full.Tm.denote]
    rw [hc]
    split
    · exact iht h
    · exact ihe h

end Full

namespace Arrow

abbrev Ty.bethRel {Base : Type u} (base : Base → BethRel) :=
  Ty.rel base
abbrev Ty.bethPER {Base : Type u} (base : Base → BethPER) :=
  Ty.per base

theorem Ty.per_rel_iff {Base : Type u} {El : Base → Type v} (base : ∀ X : Base, PER (El X))
    (A : STLC.Arrow.Ty Base) (x y) :
    (Ty.per base A).rel x y ↔ Ty.rel (fun X => (base X).rel) A x y := by
  induction A with
  | base X => rfl
  | arr A B ihA ihB =>
    constructor
    · intro h a b hab; exact (ihB _ _).mp (h a b ((ihA _ _).mpr hab))
    · intro h a b hab; exact (ihB _ _).mpr (h a b ((ihA _ _).mp hab))

theorem fundamental_beth {Base : Type u} (base : Base → BethRel) {Γ} {A}
    (t : STLC.Arrow.Tm Γ A) {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.bethRel base A (t.denote (fun _ => ProjectBeth.BethOmega) ρ)
      (t.denote (fun _ => ProjectBeth.BethOmega) ρ') :=
  fundamental base t h

end Arrow

namespace ArrowProd

abbrev Ty.bethRel {Base : Type u} (base : Base → BethRel) := Ty.rel base
abbrev Ty.bethPER {Base : Type u} (base : Base → BethPER) := Ty.per base

theorem Ty.per_rel_iff {Base : Type u} {El : Base → Type v} (base : ∀ X : Base, PER (El X))
    (A : STLC.ArrowProd.Ty Base) (x y) :
    (Ty.per base A).rel x y ↔ Ty.rel (fun X => (base X).rel) A x y := by
  induction A with
  | base X => rfl
  | arr A B ihA ihB =>
    exact ⟨fun h a b hab => (ihB _ _).mp (h a b ((ihA _ _).mpr hab)),
      fun h a b hab => (ihB _ _).mpr (h a b ((ihA _ _).mp hab))⟩
  | prod A B ihA ihB =>
    exact ⟨fun h => ⟨(ihA _ _).mp h.1, (ihB _ _).mp h.2⟩,
      fun h => ⟨(ihA _ _).mpr h.1, (ihB _ _).mpr h.2⟩⟩

theorem fundamental_beth {Base : Type u} (base : Base → BethRel) {Γ} {A}
    (t : STLC.ArrowProd.Tm Γ A) {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.bethRel base A (t.denote (fun _ => ProjectBeth.BethOmega) ρ)
      (t.denote (fun _ => ProjectBeth.BethOmega) ρ') :=
  fundamental base t h

end ArrowProd

namespace ArrowProdSum

abbrev Ty.bethRel {Base : Type u} (base : Base → BethRel) := Ty.rel base
abbrev Ty.bethPER {Base : Type u} (base : Base → BethPER) := Ty.per base

theorem Ty.per_rel_iff {Base : Type u} {El : Base → Type v} (base : ∀ X : Base, PER (El X))
    (A : STLC.ArrowProdSum.Ty Base) (x y) :
    (Ty.per base A).rel x y ↔ Ty.rel (fun X => (base X).rel) A x y := by
  induction A with
  | base X => rfl
  | arr A B ihA ihB =>
    exact ⟨fun h a b hab => (ihB _ _).mp (h a b ((ihA _ _).mpr hab)),
      fun h a b hab => (ihB _ _).mpr (h a b ((ihA _ _).mp hab))⟩
  | prod A B ihA ihB =>
    exact ⟨fun h => ⟨(ihA _ _).mp h.1, (ihB _ _).mp h.2⟩,
      fun h => ⟨(ihA _ _).mpr h.1, (ihB _ _).mpr h.2⟩⟩
  | sum A B ihA ihB =>
    cases x <;> cases y <;> simp [Ty.per, Ty.rel, PER.sum, Rel.sum, ihA, ihB]

theorem fundamental_beth {Base : Type u} (base : Base → BethRel) {Γ} {A}
    (t : STLC.ArrowProdSum.Tm Γ A) {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.bethRel base A (t.denote (fun _ => ProjectBeth.BethOmega) ρ)
      (t.denote (fun _ => ProjectBeth.BethOmega) ρ') :=
  fundamental base t h

end ArrowProdSum

namespace Full

abbrev Ty.bethRel {Base : Type u} (base : Base → BethRel) := Ty.rel base
abbrev Ty.bethPER {Base : Type u} (base : Base → BethPER) := Ty.per base

theorem Ty.per_rel_iff {Base : Type u} {El : Base → Type v} (base : ∀ X : Base, PER (El X))
    (A : STLC.Full.Ty Base) (x y) :
    (Ty.per base A).rel x y ↔ Ty.rel (fun X => (base X).rel) A x y := by
  induction A with
  | base X => rfl
  | arr A B ihA ihB =>
    exact ⟨fun h a b hab => (ihB _ _).mp (h a b ((ihA _ _).mpr hab)),
      fun h a b hab => (ihB _ _).mpr (h a b ((ihA _ _).mp hab))⟩
  | prod A B ihA ihB =>
    exact ⟨fun h => ⟨(ihA _ _).mp h.1, (ihB _ _).mp h.2⟩,
      fun h => ⟨(ihA _ _).mpr h.1, (ihB _ _).mpr h.2⟩⟩
  | sum A B ihA ihB =>
    cases x <;> cases y <;> simp [Ty.per, Ty.rel, PER.sum, Rel.sum, ihA, ihB]
  | bool =>
    cases x with | up x =>
      cases y with | up y =>
        exact ⟨fun h => congrArg ULift.down h, fun h => by cases h; rfl⟩
  | nat =>
    cases x with | up x =>
      cases y with | up y =>
        exact ⟨fun h => congrArg ULift.down h, fun h => by cases h; rfl⟩

theorem fundamental_beth {Base : Type u} (base : Base → BethRel) {Γ} {A}
    (t : STLC.Full.Tm Γ A) {ρ ρ'} (h : Env.rel base ρ ρ') :
    Ty.bethRel base A (t.denote (fun _ => ProjectBeth.BethOmega) ρ)
      (t.denote (fun _ => ProjectBeth.BethOmega) ρ') :=
  fundamental base t h

end Full

end ProjectBeth.STLC.Relational
