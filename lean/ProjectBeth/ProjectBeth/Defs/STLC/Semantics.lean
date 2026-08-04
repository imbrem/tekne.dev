import ProjectBeth.Defs.Carrier
import ProjectBeth.Defs.STLC.Variants

universe u v

namespace ProjectBeth.STLC.Arrow

namespace Ty

abbrev Direct {Base : Type u} {Ω : Type v}
    (baseSet : Base → Set Ω) (A : Ty Base) : Type v :=
  denote (fun X => baseSet X) A

abbrev Shape {Base : Type u} (Ω : Type v) (A : Ty Base) : Type v :=
  denote (fun _ => Ω) A

def Rel {Base : Type u} {Ω : Type v} (baseSet : Base → Set Ω) :
    (A : Ty Base) → Shape Ω A → Prop
  | .base X, x => x ∈ baseSet X
  | .arr A B, f => ∀ x, Rel baseSet A x → Rel baseSet B (f x)

def Agree {Base : Type u} {Ω : Type v} (baseSet : Base → Set Ω) :
    (A : Ty Base) → Direct baseSet A → Shape Ω A → Prop
  | .base _, x, y => x.val = y
  | .arr A B, f, g =>
      ∀ x y, Agree baseSet A x y → Agree baseSet B (f x) (g y)

end Ty

namespace Env

def Agree {Base : Type u} {Ω : Type v} (baseSet : Base → Set Ω) :
    {Γ : List (Ty Base)} →
    STLC.Env (Ty.Direct baseSet) Γ → STLC.Env (Ty.Shape Ω) Γ → Prop
  | [], _, _ => True
  | A :: Γ, d, s =>
      Ty.Agree baseSet A d.1 s.1 ∧ Agree baseSet d.2 s.2

def Rel {Base : Type u} {Ω : Type v} (baseSet : Base → Set Ω) :
    {Γ : List (Ty Base)} → STLC.Env (Ty.Shape Ω) Γ → Prop
  | [], _ => True
  | A :: Γ, env => Ty.Rel baseSet A env.1 ∧ Rel baseSet env.2

theorem lookup_agree {Base : Type u} {Ω : Type v}
    {baseSet : Base → Set Ω} {Γ : List (Ty Base)} {A : Ty Base}
    (x : Var Γ A) {d : STLC.Env (Ty.Direct baseSet) Γ}
    {s : STLC.Env (Ty.Shape Ω) Γ} (h : Agree baseSet d s) :
    Ty.Agree baseSet A (x.lookup d) (x.lookup s) := by
  induction x with
  | here => exact h.1
  | there x ih => exact ih h.2

theorem lookup_rel {Base : Type u} {Ω : Type v}
    {baseSet : Base → Set Ω} {Γ : List (Ty Base)} {A : Ty Base}
    (x : Var Γ A) {s : STLC.Env (Ty.Shape Ω) Γ} (h : Rel baseSet s) :
    Ty.Rel baseSet A (x.lookup s) := by
  induction x with
  | here => exact h.1
  | there x ih => exact ih h.2

end Env

namespace Tm

def direct {Base : Type u} {Ω : Type v} (baseSet : Base → Set Ω)
    {Γ : List (Ty Base)} {A : Ty Base} (t : Tm Γ A) :
    STLC.Env (Ty.Direct baseSet) Γ → Ty.Direct baseSet A :=
  denote (fun X => baseSet X) t

def shape {Base : Type u} (Ω : Type v)
    {Γ : List (Ty Base)} {A : Ty Base} (t : Tm Γ A) :
    STLC.Env (Ty.Shape Ω) Γ → Ty.Shape Ω A :=
  denote (fun _ => Ω) t

theorem agreement {Base : Type u} {Ω : Type v}
    (baseSet : Base → Set Ω) {Γ : List (Ty Base)} {A : Ty Base}
    (t : Tm Γ A) {d : STLC.Env (Ty.Direct baseSet) Γ}
    {s : STLC.Env (Ty.Shape Ω) Γ} (h : Env.Agree baseSet d s) :
    Ty.Agree baseSet A (direct baseSet t d) (shape Ω t s) := by
  induction t with
  | var x => exact Env.lookup_agree x h
  | app f x ihf ihx => exact ihf h _ _ (ihx h)
  | lam t ih =>
    intro x y hxy
    exact ih ⟨hxy, h⟩

theorem fundamental {Base : Type u} {Ω : Type v}
    (baseSet : Base → Set Ω) {Γ : List (Ty Base)} {A : Ty Base}
    (t : Tm Γ A) {s : STLC.Env (Ty.Shape Ω) Γ} (h : Env.Rel baseSet s) :
    Ty.Rel baseSet A (shape Ω t s) := by
  induction t with
  | var x => exact Env.lookup_rel x h
  | app f x ihf ihx => exact ihf h _ (ihx h)
  | lam t ih =>
    intro x hx
    exact ih ⟨hx, h⟩

structure Coding {Base : Type u} (Ω : Type v) (baseSet : Base → Set Ω) where
  term : ∀ Γ A,
    _root_.Code
      (STLC.Env (Ty.Direct baseSet) Γ → Ty.Direct baseSet A)
      Ω

def coded {Base : Type u} {Ω : Type v} {baseSet : Base → Set Ω}
    (M : Coding Ω baseSet) {Γ : List (Ty Base)} {A : Ty Base}
    (t : Tm Γ A) : Ω :=
  (M.term Γ A).code (direct baseSet t)

theorem decode_coded {Base : Type u} {Ω : Type v} {baseSet : Base → Set Ω}
    (M : Coding Ω baseSet) {Γ : List (Ty Base)} {A : Ty Base}
    (t : Tm Γ A) :
    ProjectBeth.Code.decode (M.term Γ A)
      ⟨coded M t, by simp [coded]⟩ = direct baseSet t :=
  ProjectBeth.Code.decode_code (M.term Γ A) (direct baseSet t)

end Tm

end ProjectBeth.STLC.Arrow
