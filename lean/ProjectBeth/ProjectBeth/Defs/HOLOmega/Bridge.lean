import ProjectBeth.Defs.HOLOmega.Kernel
import ProjectBeth.Defs.HOLOmega.Substitution

universe u

namespace ProjectBeth.HOLOmega.Kernel

variable (U : Universe) {Base : Type u} (baseCode : Base → U.Code)

/-- Honest common fragment shared by the original raw tree syntax and the
stratified kernel.  The relation excludes raw type variables, higher-kinded
application and tree subtypes, whose original judgments lack enough premises
for a semantics-preservation theorem. -/
inductive CommonTy : ProjectBeth.HOLOmega.Ty Base → Ty U [] .star → Prop
  | base (A) : CommonTy (.base A) (Ty.base U (baseCode A))
  | bool : CommonTy .bool (Ty.boolCode U)
  | arr : CommonTy A A' → CommonTy B B' → CommonTy (.arr A B) (Ty.arr U A' B')

inductive CommonTm : ProjectBeth.HOLOmega.Tm Base →
    {Γ : Ctx U []} → {A : Ty U [] .star} → Tm U Γ A → Prop
  | var : CommonTm (.var 0) (Tm.vz U)
  | weaken : CommonTm t (Γ := Γ) (A := A) x →
      CommonTm (ProjectBeth.HOLOmega.Tm.rename Nat.succ t)
        (Γ := B :: Γ) (Tm.vs U x)
  | app : CommonTm f (Γ := Γ) (A := Ty.arr U A B) f' →
      CommonTm x (Γ := Γ) (A := A) x' →
      CommonTm (.app f x) (Tm.app U f' x')
  | lam : CommonTy U baseCode A A' → CommonTm t (Γ := A' :: Γ) (A := B') t' →
      CommonTm (.lam A t) (Tm.lam U t')
  | bool (b) : CommonTm (.bool b) (Γ := Γ) (Tm.boolCode U b)
  | eq : CommonTy U baseCode A A' → CommonTm x (Γ := Γ) (A := A') x' →
      CommonTm y (Γ := Γ) (A := A') y' →
      CommonTm (.eq A x y) (Tm.equal U x' y')
  | epsilon : CommonTy U baseCode A A' →
      CommonTm p (Γ := Γ) (A := Ty.arr U A' (Ty.boolCode U)) p' →
      CommonTm (.epsilon A p) (Tm.epsilon U p')

def CommonTm.kernelTyped
    (h : CommonTm U baseCode t (Γ := Γ) (A := A) x) : Tm U Γ A := x

theorem CommonTm.eq_preserved
    {x y : Tm U Γ A} (h : EqTm U Γ x y) : x = y := h.sound U

end ProjectBeth.HOLOmega.Kernel
