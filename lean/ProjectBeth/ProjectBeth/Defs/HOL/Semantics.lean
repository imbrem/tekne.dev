import ProjectBeth.Defs.HOL.Syntax
import ProjectBeth.Defs.Carrier
import ProjectBeth.Defs.STLC.Core

universe u v

namespace ProjectBeth.HOL

structure DirectModel (Base : Type u) (Ω : Type v) where
  ty : Ty Base → Set Ω
  tm : ∀ {Γ t A}, HasType Γ t A →
    STLC.Env (fun B => ty B) Γ → ty A

structure ShapeModel (Base : Type u) where
  ty : Ty Base → Type u
  tm : ∀ {Γ t A}, HasType Γ t A →
    STLC.Env ty Γ → ty A

structure CodedModel (Base : Type u) (Ω : Type v) extends ShapeModel Base where
  tyCode : ∀ A, _root_.Code (toShapeModel.ty A) Ω
  envCode : ∀ Γ, _root_.Code (STLC.Env toShapeModel.ty Γ) Ω

structure Expansion (α : Type u) [Inhabited α] (P : α → Prop) where
  carrier : Type u
  subEquiv : carrier ≃ TotalSubtype α P
  abs : α → carrier
  rep : carrier → α
  rep_abs : ∀ x, P x → rep (abs x) = x
  abs_rep : ∀ x, abs (rep x) = x

noncomputable def Expansion.total (α : Type u) [Inhabited α] (P : α → Prop) :
    Expansion α P where
  carrier := TotalSubtype α P
  subEquiv := Equiv.refl _
  abs := TotalSubtype.abs P
  rep := TotalSubtype.rep
  rep_abs x hx := TotalSubtype.rep_abs_of hx
  abs_rep := TotalSubtype.abs_rep

theorem total_expansion_exists (α : Type u) [Inhabited α] (P : α → Prop) :
    Nonempty (Expansion α P) :=
  ⟨Expansion.total α P⟩

end ProjectBeth.HOL
