import ProjectBeth.Defs.STLC.Variants
import ProjectBeth.Defs.PowerTower

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

def PER.id (α : Type u) : PER α where
  rel := Eq
  symm := Eq.symm
  trans := Eq.trans

def PER.prod (R : PER α) (S : PER β) : PER (α × β) where
  rel := Rel.prod R.rel S.rel
  symm h := ⟨R.symm h.1, S.symm h.2⟩
  trans h k := ⟨R.trans h.1 k.1, S.trans h.2 k.2⟩

def PER.arrow (R : PER α) (S : PER β) : PER (α → β) where
  rel := Rel.arrow R.rel S.rel
  symm h x y hxy := S.symm (h y x (R.symm hxy))
  trans h k x y hxy := S.trans (h x x (R.trans hxy (R.symm hxy))) (k x y hxy)

abbrev BethRel := Rel ProjectBeth.BethOmega ProjectBeth.BethOmega
abbrev BethPER := PER ProjectBeth.BethOmega

namespace Arrow

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
  | A :: Γ, ρ, ρ' => Ty.rel base A ρ.1 ρ'.1 ∧ Env.rel base ρ.2 ρ'.2

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

end ProjectBeth.STLC.Relational
