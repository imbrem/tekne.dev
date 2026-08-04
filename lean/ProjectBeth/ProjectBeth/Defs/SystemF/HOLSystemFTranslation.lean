import ProjectBeth.Defs.SystemF.InductivePER
import ProjectBeth.Defs.HOL.Syntax
import ProjectBeth.Defs.HOLOmega.Syntax

namespace ProjectBeth.SystemF.HOLTranslation

namespace Raw

abbrev Ty := ProjectBeth.SystemF.Inductive.Ty
abbrev Tm := ProjectBeth.SystemF.Inductive.Tm
abbrev HasType := ProjectBeth.SystemF.Inductive.HasType
open ProjectBeth.SystemF.Inductive

def boolTy : Ty := .all (.arr (.var 0) (.arr (.var 0) (.var 0)))

def natTy : Ty := .all (.arr (.arr (.var 0) (.var 0)) (.arr (.var 0) (.var 0)))

def churchTrue : Tm := .tyLam (.lam (.var 0) (.lam (.var 0) (.var 1)))

def churchFalse : Tm := .tyLam (.lam (.var 0) (.lam (.var 0) (.var 0)))

def churchIter : Nat → Tm
  | 0 => .var 0
  | n + 1 => .app (.var 1) (churchIter n)

def churchNat (n : Nat) : Tm :=
  .tyLam (.lam (.arr (.var 0) (.var 0)) (.lam (.var 0) (churchIter n)))

theorem churchTrue_typed : HasType 0 [] churchTrue boolTy := by
  apply HasType.tyLam
  apply HasType.lam
  apply HasType.lam
  exact HasType.var (by rfl)

theorem churchFalse_typed : HasType 0 [] churchFalse boolTy := by
  apply HasType.tyLam
  apply HasType.lam
  apply HasType.lam
  exact HasType.var (by rfl)

theorem churchIter_typed (n : Nat) :
    HasType 1 [.var 0, .arr (.var 0) (.var 0)] (churchIter n) (.var 0) := by
  induction n with
  | zero => exact HasType.var (by rfl)
  | succ n ih =>
    exact HasType.app (HasType.var (n := 1) (by rfl)) ih

theorem churchNat_typed (n : Nat) : HasType 0 [] (churchNat n) natTy := by
  apply HasType.tyLam
  apply HasType.lam
  apply HasType.lam
  exact churchIter_typed n

@[simp] theorem churchIter_rename (n : Nat) (ρ : Nat → Nat) :
    (churchIter n).rename (upRen (upRen ρ)) = churchIter n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [churchIter, ProjectBeth.SystemF.Inductive.Tm.rename, upRen, ih]

@[simp] theorem churchBool_rename (b : Bool) (ρ : Nat → Nat) :
    (if b then churchTrue else churchFalse).rename ρ =
      (if b then churchTrue else churchFalse) := by
  cases b <;> rfl

@[simp] theorem churchNat_rename (n : Nat) (ρ : Nat → Nat) :
    (churchNat n).rename ρ = churchNat n := by
  simp only [churchNat, ProjectBeth.SystemF.Inductive.Tm.rename]
  congr 3
  change (churchIter n).rename (upRen (upRen ρ)) = churchIter n
  exact churchIter_rename n ρ

@[simp] theorem churchBool_subst (b : Bool) (σ : Nat → Tm) :
    (if b then churchTrue else churchFalse).subst σ =
      (if b then churchTrue else churchFalse) := by
  cases b <;> rfl

theorem churchIter_subst_of (n : Nat) (σ : Nat → Tm)
    (h0 : σ 0 = .var 0) (h1 : σ 1 = .var 1) :
    (churchIter n).subst σ = churchIter n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    simp only [churchIter, ProjectBeth.SystemF.Inductive.Tm.subst]
    rw [h1, ih]

@[simp] theorem churchNat_subst (n : Nat) (σ : Nat → Tm) :
    (churchNat n).subst σ = churchNat n := by
  simp only [churchNat, ProjectBeth.SystemF.Inductive.Tm.subst]
  congr 3
  apply churchIter_subst_of
  · rfl
  · rfl

end Raw

/-- The simply-typed HOL fragment representable without adding constants to
raw System F.  Subtypes deliberately remain outside this translation. -/
def holTy (base : B → Inductive.Ty) : ProjectBeth.HOL.Ty B → Option Inductive.Ty
  | .base A => some (base A)
  | .bool => some Raw.boolTy
  | .arr A B => return .arr (← holTy base A) (← holTy base B)
  | .sub _ _ => none

def holOmegaTy (base : B → Inductive.Ty) :
    ProjectBeth.HOLOmega.Ty B → Option Inductive.Ty
  | .base A => some (base A)
  | .var n => some (.var n)
  | .bool => some Raw.boolTy
  | .arr A B => return .arr (← holOmegaTy base A) (← holOmegaTy base B)
  | .lam _ A => return .all (← holOmegaTy base A)
  | .app _ _ => none
  | .sub _ _ => none

/-- An explicit boundary for constants absent from pure System F.  A client
may supply equality and classical choice only for translated types. -/
structure ClassicalInterface where
  eq : Inductive.Ty → Inductive.Tm
  epsilon : Inductive.Ty → Inductive.Tm
  eq_typed : ∀ A, Inductive.HasType 0 [] (eq A)
    (.arr A (.arr A Raw.boolTy))
  epsilon_typed : ∀ A, Inductive.HasType 0 [] (epsilon A)
    (.arr (.arr A Raw.boolTy) A)

end ProjectBeth.SystemF.HOLTranslation
