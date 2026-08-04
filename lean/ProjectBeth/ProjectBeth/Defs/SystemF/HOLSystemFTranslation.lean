import ProjectBeth.Defs.SystemF.InductivePER
import ProjectBeth.Defs.SystemF.Untyped
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

theorem churchTrue_typed : HasType Δ Γ churchTrue boolTy := by
  apply HasType.tyLam
  apply HasType.lam
  apply HasType.lam
  exact HasType.var (by rfl)

theorem churchFalse_typed : HasType Δ Γ churchFalse boolTy := by
  apply HasType.tyLam
  apply HasType.lam
  apply HasType.lam
  exact HasType.var (by rfl)

theorem churchIter_typed (n : Nat) :
    HasType Δ ([.var 0, .arr (.var 0) (.var 0)] ++ Γ) (churchIter n) (.var 0) := by
  induction n with
  | zero => exact HasType.var (by rfl)
  | succ n ih =>
    exact HasType.app (HasType.var (n := 1) (by rfl)) ih

theorem churchNat_typed (n : Nat) : HasType Δ Γ (churchNat n) natTy := by
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
  eq_typed : ∀ Δ Γ A, Inductive.HasType Δ Γ (eq A)
    (.arr A (.arr A Raw.boolTy))
  epsilon_typed : ∀ Δ Γ A, Inductive.HasType Δ Γ (epsilon A)
    (.arr (.arr A Raw.boolTy) A)

def holCtx (base : B → Inductive.Ty) (Γ : ProjectBeth.HOL.Ctx B) :
    Option (List Inductive.Ty) := Γ.mapM (holTy base)

def holOmegaCtx (base : B → Inductive.Ty) (Γ : List (ProjectBeth.HOLOmega.Ty B)) :
    Option (List Inductive.Ty) := Γ.mapM (holOmegaTy base)

def holTm (I : ClassicalInterface) (base : B → Inductive.Ty) :
    ProjectBeth.HOL.Tm B → Option Inductive.Tm
  | .var n => some (.var n)
  | .app f x => return .app (← holTm I base f) (← holTm I base x)
  | .lam A t => return .lam (← holTy base A) (← holTm I base t)
  | .bool b => some (if b then Raw.churchTrue else Raw.churchFalse)
  | .eq A x y => return .app (.app (I.eq (← holTy base A))
      (← holTm I base x)) (← holTm I base y)
  | .epsilon A p => return .app (I.epsilon (← holTy base A)) (← holTm I base p)
  | .abs _ _ _ => none
  | .rep _ _ _ => none

def holOmegaTm (I : ClassicalInterface) (base : B → Inductive.Ty) :
    ProjectBeth.HOLOmega.Tm B → Option Inductive.Tm
  | .var n => some (.var n)
  | .app f x => return .app (← holOmegaTm I base f) (← holOmegaTm I base x)
  | .lam A t => return .lam (← holOmegaTy base A) (← holOmegaTm I base t)
  | .tyApp f A => return .tyApp (← holOmegaTm I base f) (← holOmegaTy base A)
  | .tyLam .star t => return .tyLam (← holOmegaTm I base t)
  | .tyLam (.arr _ _) _ => none
  | .bool b => some (if b then Raw.churchTrue else Raw.churchFalse)
  | .eq A x y => return .app (.app (I.eq (← holOmegaTy base A))
      (← holOmegaTm I base x)) (← holOmegaTm I base y)
  | .epsilon A p => do
      let A' ← holOmegaTy base A
      let p' ← holOmegaTm I base p
      pure (.app (I.epsilon A') p')
  | .abs _ _ _ => none
  | .rep _ _ _ => none

@[simp] theorem holTm_bool (I : ClassicalInterface) (base : B → Inductive.Ty)
    (b : Bool) : holTm I base (.bool b) =
      some (if b then Raw.churchTrue else Raw.churchFalse) := rfl

@[simp] theorem holOmegaTm_bool (I : ClassicalInterface)
    (base : B → Inductive.Ty) (b : Bool) : holOmegaTm I base (.bool b) =
      some (if b then Raw.churchTrue else Raw.churchFalse) := rfl

/-- Erasure is deliberately factored through the typed translation.  Thus
the square cannot silently erase a source construct rejected by `holTm`. -/
def holErase (S : ProjectBeth.Untyped.Signature) (I : ClassicalInterface)
    (base : B → Inductive.Ty) (t : ProjectBeth.HOL.Tm B) :=
  (holTm I base t).map (Inductive.Untyped.erase S)

def holOmegaErase (S : ProjectBeth.Untyped.Signature) (I : ClassicalInterface)
    (base : B → Inductive.Ty) (t : ProjectBeth.HOLOmega.Tm B) :=
  (holOmegaTm I base t).map (Inductive.Untyped.erase S)

theorem hol_erase_square (base : B → Inductive.Ty)
    (h : holTm I base t = some u) :
    holErase S I base t = some (Inductive.Untyped.erase S u) := by
  simp [holErase, h]

theorem holOmega_erase_square (base : B → Inductive.Ty)
    (h : holOmegaTm I base t = some u) :
    holOmegaErase S I base t = some (Inductive.Untyped.erase S u) := by
  simp [holOmegaErase, h]

/-- Semantic obligation for a realization of classical choice. `Sat A p x`
means that `x : A` satisfies the translated predicate `p : A → Bool`.
The law is conditional and therefore makes no representability or
definability claim about arbitrary semantic elements. -/
structure SelectionLaw (I : ClassicalInterface)
    (Sat : Inductive.Ty → Inductive.Tm → Inductive.Tm → Prop) : Prop where
  selected : ∀ {A p}, (∃ x, Sat A p x) → Sat A p (.app (I.epsilon A) p)

theorem epsilon_selection {Sat : Inductive.Ty → Inductive.Tm → Inductive.Tm → Prop}
    (law : SelectionLaw I Sat) (h : ∃ x, Sat A p x) :
    Sat A p (.app (I.epsilon A) p) := law.selected h

end ProjectBeth.SystemF.HOLTranslation
