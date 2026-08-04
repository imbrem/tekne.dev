import ProjectBeth.Defs.STLC.Core

universe u

namespace ProjectBeth.HOL

mutual
  inductive Ty (Base : Type u) : Type u
    | base : Base → Ty Base
    | bool : Ty Base
    | arr : Ty Base → Ty Base → Ty Base
    | sub : Ty Base → Tm Base → Ty Base

  inductive Tm (Base : Type u) : Type u
    | var : Nat → Tm Base
    | app : Tm Base → Tm Base → Tm Base
    | lam : Ty Base → Tm Base → Tm Base
    | bool : Bool → Tm Base
    | eq : Ty Base → Tm Base → Tm Base → Tm Base
    | epsilon : Ty Base → Tm Base → Tm Base
    | abs : Ty Base → Tm Base → Tm Base → Tm Base
    | rep : Ty Base → Tm Base → Tm Base → Tm Base
end

abbrev Ctx (Base : Type u) := List (Ty Base)

mutual
  inductive Ty.Wf {Base : Type u} : Ty Base → Prop
    | base : Ty.Wf (.base A)
    | bool : Ty.Wf .bool
    | arr : Ty.Wf A → Ty.Wf B → Ty.Wf (.arr A B)
    | sub : Ty.Wf A → HasType [A] p .bool → Ty.Wf (.sub A p)

  inductive HasType {Base : Type u} : Ctx Base → Tm Base → Ty Base → Prop
    | var : Γ[n]? = some A → HasType Γ (.var n) A
    | app : HasType Γ f (.arr A B) → HasType Γ x A → HasType Γ (.app f x) B
    | lam : Ty.Wf A → HasType (A :: Γ) t B → HasType Γ (.lam A t) (.arr A B)
    | bool : HasType Γ (.bool b) .bool
    | eq : Ty.Wf A → HasType Γ x A → HasType Γ y A →
        HasType Γ (.eq A x y) .bool
    | epsilon : Ty.Wf A → HasType Γ p (.arr A .bool) →
        HasType Γ (.epsilon A p) A
    | abs : Ty.Wf A → HasType [A] p .bool → HasType Γ x A →
        HasType Γ (.abs A p x) (.sub A p)
    | rep : Ty.Wf A → HasType [A] p .bool → HasType Γ x (.sub A p) →
        HasType Γ (.rep A p x) A
end

def TotalSubtype (α : Type u) (P : α → Prop) :=
  {x : α // P x ∨ ¬∃ y, P y}

namespace TotalSubtype

def rep {α : Type u} {P : α → Prop} : TotalSubtype α P → α :=
  Subtype.val

noncomputable def abs {α : Type u} [Inhabited α] (P : α → Prop) :
    α → TotalSubtype α P := by
  classical
  intro x
  exact if hx : P x then ⟨x, Or.inl hx⟩
    else if hP : ∃ y, P y then ⟨Classical.choose hP, Or.inl (Classical.choose_spec hP)⟩
    else ⟨x, Or.inr hP⟩

noncomputable instance {α : Type u} [Inhabited α] (P : α → Prop) :
    Inhabited (TotalSubtype α P) where
  default := abs P default

@[simp]
theorem rep_abs_of {α : Type u} [Inhabited α] {P : α → Prop}
    {x : α} (hx : P x) : rep (abs P x) = x := by
  classical
  simp [abs, hx, rep]

@[simp]
theorem abs_rep {α : Type u} [Inhabited α] {P : α → Prop}
    (x : TotalSubtype α P) : abs P (rep x) = x := by
  classical
  apply Subtype.ext
  rcases x.property with hx | hP
  · simp [abs, rep, hx]
  · have hx : ¬P x.val := fun hp => hP ⟨x.val, hp⟩
    simp [abs, rep, hx, hP]

theorem nonempty {α : Type u} [Inhabited α] (P : α → Prop) :
    Nonempty (TotalSubtype α P) :=
  ⟨abs P default⟩

end TotalSubtype

end ProjectBeth.HOL
