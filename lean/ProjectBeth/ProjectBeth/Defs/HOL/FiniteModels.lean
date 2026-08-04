import ProjectBeth.Defs.HOL.Entailment
import ProjectBeth.Defs.HOLOmega.Kernel
import ProjectBeth.Defs.PowerTower

universe u

namespace ProjectBeth.FiniteModels

/-! Concrete finite carriers for the two sound kernels, together with the
finite-to-`Nat`-to-`BethOmega` comparison square. -/

namespace HOL

/-- A finite HOL carrier.  The positivity assumption is exactly what supplies
the fallback used by epsilon when its predicate has no witness. -/
def finTy (n : Nat) [NeZero n] : ProjectBeth.HOL.Kernel.Ty :=
  ⟨ULift (Fin n), ⟨⟨0, Nat.pos_of_neZero n⟩⟩⟩

theorem derives_sound
    {Γ : ProjectBeth.HOL.Kernel.Ctx}
    {Assume : ProjectBeth.HOL.Kernel.Tm Γ ProjectBeth.HOL.Kernel.Ty.bool → Prop}
    {p : ProjectBeth.HOL.Kernel.Tm Γ ProjectBeth.HOL.Kernel.Ty.bool}
    (d : ProjectBeth.HOL.Kernel.Derives Assume p) :
    ProjectBeth.HOL.Kernel.Valid Assume p :=
  d.valid

theorem choice_sound_fin (n : Nat) [NeZero n]
    {Γ : ProjectBeth.HOL.Kernel.Ctx}
    (pred : ProjectBeth.HOL.Kernel.Tm Γ ((finTy n).arr ProjectBeth.HOL.Kernel.Ty.bool))
    (x : ProjectBeth.HOL.Kernel.Tm Γ (finTy n))
    {Assume} (d : ProjectBeth.HOL.Kernel.Derives Assume (.app pred x)) :
    ProjectBeth.HOL.Kernel.Valid Assume (.app pred (.epsilon pred)) :=
  (ProjectBeth.HOL.Kernel.Derives.choice pred x d).valid

end HOL

namespace Omega

/-- A concrete finite carrier represented by a code in a HOLω universe.  This
is the appropriate finite-model boundary for the impredicative `Universe`
interface: constructing the surrounding universe remains an explicit input. -/
structure FinCode (U : ProjectBeth.HOLOmega.Kernel.Universe) (n : Nat) where
  code : U.Code
  equiv : U.El code ≃ Fin n

theorem finCode_nonempty (U : ProjectBeth.HOLOmega.Kernel.Universe)
    (n : Nat) [NeZero n] (F : FinCode U n) : Nonempty (U.El F.code) :=
  ⟨F.equiv.symm ⟨0, Nat.pos_of_neZero n⟩⟩

theorem no_finCode_zero (U : ProjectBeth.HOLOmega.Kernel.Universe) :
    IsEmpty (FinCode U 0) := by
  constructor
  intro F
  exact Fin.elim0 (F.equiv (default : U.El F.code))

theorem choice_sound_fin
    (U : ProjectBeth.HOLOmega.Kernel.Universe) (n : Nat) [NeZero n]
    (F : FinCode U n) {Δ} {Γ : ProjectBeth.HOLOmega.Kernel.Ctx U Δ}
    {A : ProjectBeth.HOLOmega.Kernel.Ty U Δ .star}
    (hA : ∀ ρ, A ρ = F.code)
    (pred : ProjectBeth.HOLOmega.Kernel.Tm U Γ
      (ProjectBeth.HOLOmega.Kernel.Ty.arr U A
        (ProjectBeth.HOLOmega.Kernel.Ty.boolCode U)))
    (x : ProjectBeth.HOLOmega.Kernel.Tm U Γ A) {H}
    (d : ProjectBeth.HOLOmega.Kernel.Derives U H
      (ProjectBeth.HOLOmega.Kernel.Tm.app U pred x)) :
    ProjectBeth.HOLOmega.Kernel.Entails U H
      (ProjectBeth.HOLOmega.Kernel.Tm.app U pred
        (ProjectBeth.HOLOmega.Kernel.Tm.epsilon U pred)) := by
  have _ := F
  have _ := hA
  exact (ProjectBeth.HOLOmega.Kernel.Derives.choice pred x d).sound U

theorem derives_sound
    (U : ProjectBeth.HOLOmega.Kernel.Universe)
    {Δ} {Γ : ProjectBeth.HOLOmega.Kernel.Ctx U Δ}
    {H : List (ProjectBeth.HOLOmega.Kernel.Tm U Γ
      (ProjectBeth.HOLOmega.Kernel.Ty.boolCode U))}
    {p : ProjectBeth.HOLOmega.Kernel.Tm U Γ
      (ProjectBeth.HOLOmega.Kernel.Ty.boolCode U)}
    (d : ProjectBeth.HOLOmega.Kernel.Derives U H p) :
    ProjectBeth.HOLOmega.Kernel.Entails U H p :=
  d.sound U

end Omega

theorem fin_nat_beth_commutes (n : Nat) (x : Fin n) :
    ProjectBeth.finToBethOmega n x =
      ProjectBeth.natToBethOmega (ProjectBeth.finToNat n x) := rfl

theorem fin_nat_beth_embedding_square (n : Nat) :
    ProjectBeth.finToBethOmega n =
      (ProjectBeth.finToNat n).trans ProjectBeth.natToBethOmega := rfl

theorem fin_nat_beth_function_square (n : Nat) (f : Nat → Nat) (x : Fin n) :
    ProjectBeth.natToBethOmega (f (ProjectBeth.finToNat n x)) =
      (ProjectBeth.natToBethOmega ∘ f ∘ ProjectBeth.finToNat n) x := rfl

end ProjectBeth.FiniteModels
