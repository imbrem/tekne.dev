import ProjectBeth.Defs.Closure
import ProjectBeth.Defs.STLC.Semantics
import ProjectBeth.Snapshots.A08

universe u v

namespace ProjectBeth.Snapshots.A09

open ProjectBeth.STLC

abbrev Ty := Arrow.Ty
abbrev Tm := @Arrow.Tm

abbrev Direct {Base : Type u} {Ω : Type v}
    (baseSet : Base → Set Ω) := Arrow.Ty.Direct baseSet

abbrev Shape {Base : Type u} (Ω : Type v) :=
  Arrow.Ty.Shape (Base := Base) Ω

abbrev Member {Base : Type u} {Ω : Type v}
    (baseSet : Base → Set Ω) := Arrow.Ty.Rel baseSet

theorem shape_sound {Base : Type u} {Ω : Type v}
    (baseSet : Base → Set Ω) {Γ : List (Ty Base)} {A : Ty Base}
    (t : Arrow.Tm Γ A) {env : STLC.Env (Shape Ω) Γ}
    (h : Arrow.Env.Rel baseSet env) :
    Member baseSet A (Arrow.Tm.shape Ω t env) :=
  Arrow.Tm.fundamental baseSet t h

theorem direct_shape_agree {Base : Type u} {Ω : Type v}
    (baseSet : Base → Set Ω) {Γ : List (Ty Base)} {A : Ty Base}
    (t : Arrow.Tm Γ A) {directEnv : STLC.Env (Direct baseSet) Γ}
    {shapeEnv : STLC.Env (Shape Ω) Γ}
    (h : Arrow.Env.Agree baseSet directEnv shapeEnv) :
    Arrow.Ty.Agree baseSet A
      (Arrow.Tm.direct baseSet t directEnv)
      (Arrow.Tm.shape Ω t shapeEnv) :=
  Arrow.Tm.agreement baseSet t h

abbrev Coding {Base : Type u} (Ω : Type v) (baseSet : Base → Set Ω) :=
  Arrow.Tm.Coding Ω baseSet

theorem coded_direct_agree {Base : Type u} {Ω : Type v}
    {baseSet : Base → Set Ω} (M : Coding Ω baseSet)
    {Γ : List (Ty Base)} {A : Ty Base} (t : Arrow.Tm Γ A) :
    ProjectBeth.Code.decode (M.term Γ A)
      ⟨Arrow.Tm.coded M t, by simp [Arrow.Tm.coded]⟩ =
      Arrow.Tm.direct baseSet t :=
  Arrow.Tm.decode_coded M t

end ProjectBeth.Snapshots.A09
