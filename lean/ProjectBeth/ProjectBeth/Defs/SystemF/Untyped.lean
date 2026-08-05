import ProjectBeth.Defs.SystemF.Inductive
import ProjectBeth.Defs.Untyped.Reduction

universe u

namespace ProjectBeth.SystemF.Inductive.Untyped

abbrev UTm (S : ProjectBeth.Untyped.Signature) :=
  ProjectBeth.Untyped.Tm S.Const

def churchBool (S : ProjectBeth.Untyped.Signature) : Bool → UTm S
  | true => .lam (.lam (.var 1))
  | false => .lam (.lam (.var 0))

def churchNatBody (S : ProjectBeth.Untyped.Signature) : Nat → UTm S
  | 0 => .var 0
  | n + 1 => .app (.var 1) (churchNatBody S n)

def churchNat (S : ProjectBeth.Untyped.Signature) (n : Nat) : UTm S :=
  .lam (.lam (churchNatBody S n))

theorem churchNatBody_rename (S : ProjectBeth.Untyped.Signature) (ρ)
    (h0 : ρ 0 = 0) (h1 : ρ 1 = 1) (n) :
    (churchNatBody S n).rename ρ = churchNatBody S n := by
  induction n with
  | zero => simp [churchNatBody, ProjectBeth.Untyped.Tm.rename, h0]
  | succ n ih => simp [churchNatBody, ProjectBeth.Untyped.Tm.rename, h1, ih]

theorem churchNatBody_subst (S : ProjectBeth.Untyped.Signature) (σ)
    (h0 : σ 0 = .var 0) (h1 : σ 1 = .var 1) (n) :
    (churchNatBody S n).subst σ = churchNatBody S n := by
  induction n with
  | zero => simp [churchNatBody, ProjectBeth.Untyped.Tm.subst, h0]
  | succ n ih => simp [churchNatBody, ProjectBeth.Untyped.Tm.subst, h1, ih]

@[simp] theorem churchBool_rename (S : ProjectBeth.Untyped.Signature) (ρ) (b) :
    (churchBool S b).rename ρ = churchBool S b := by cases b <;> rfl

@[simp] theorem churchBool_subst (S : ProjectBeth.Untyped.Signature) (σ) (b) :
    (churchBool S b).subst σ = churchBool S b := by cases b <;> rfl

@[simp] theorem churchNat_rename (S : ProjectBeth.Untyped.Signature) (ρ) (n) :
    (churchNat S n).rename ρ = churchNat S n := by
  simp only [churchNat, ProjectBeth.Untyped.Tm.rename]
  apply congrArg ProjectBeth.Untyped.Tm.lam
  apply congrArg ProjectBeth.Untyped.Tm.lam
  apply churchNatBody_rename S <;> rfl

@[simp] theorem churchNat_subst (S : ProjectBeth.Untyped.Signature) (σ) (n) :
    (churchNat S n).subst σ = churchNat S n := by
  simp only [churchNat, ProjectBeth.Untyped.Tm.subst]
  apply congrArg ProjectBeth.Untyped.Tm.lam
  apply congrArg ProjectBeth.Untyped.Tm.lam
  apply churchNatBody_subst S <;> rfl

/-- Type abstraction and application are computationally irrelevant; base
constants are compiled to their pure Church encodings. -/
def erase (S : ProjectBeth.Untyped.Signature) : Tm → UTm S
  | .var i => .var i
  | .app f x => .app (erase S f) (erase S x)
  | .lam _ body => .lam (erase S body)
  | .tyApp f _ => erase S f
  | .tyLam body => erase S body
  | .bool b => churchBool S b
  | .nat n => churchNat S n

@[simp] theorem erase_rename (S : ProjectBeth.Untyped.Signature)
    (ρ : Nat → Nat) (t : Tm) :
    erase S (t.rename ρ) = (erase S t).rename ρ := by
  induction t generalizing ρ with
  | var i => rfl
  | app f x ihf ihx => simp [erase, Tm.rename, ihf, ihx, ProjectBeth.Untyped.Tm.rename]
  | lam A t ih =>
    simp only [erase, Tm.rename, ProjectBeth.Untyped.Tm.rename, ih]
    apply congrArg ProjectBeth.Untyped.Tm.lam
    apply ProjectBeth.Untyped.Tm.rename_congr
    intro i; cases i <;> rfl
  | tyApp f A ih => exact ih ρ
  | tyLam t ih => exact ih ρ
  | bool b => simp [erase, Tm.rename]
  | nat n => simp [erase, Tm.rename]

@[simp] theorem erase_renameTy (S : ProjectBeth.Untyped.Signature)
    (ρ : Nat → Nat) (t : Tm) : erase S (t.renameTy ρ) = erase S t := by
  induction t generalizing ρ <;> simp [erase, Tm.renameTy, *]

@[simp] theorem erase_subst (S : ProjectBeth.Untyped.Signature)
    (σ : Nat → Tm) (t : Tm) :
    erase S (t.subst σ) =
      (erase S t).subst (fun i => erase S (σ i)) := by
  induction t generalizing σ with
  | var i => rfl
  | app f x ihf ihx => simp [erase, Tm.subst, ihf, ihx, ProjectBeth.Untyped.Tm.subst]
  | lam A t ih =>
    simp only [erase, Tm.subst, ProjectBeth.Untyped.Tm.subst, ih]
    congr 1
    apply ProjectBeth.Untyped.Tm.subst_congr
    intro i
    cases i with
    | zero => rfl
    | succ i => simpa [upTmSub, Tm.lift] using erase_rename S Nat.succ (σ i)
  | tyApp f A ih => exact ih σ
  | tyLam t ih =>
    simp only [Tm.subst, erase]
    rw [ih (liftTmSubTy σ)]
    apply ProjectBeth.Untyped.Tm.subst_congr
    intro i
    simp [liftTmSubTy, erase_renameTy]
  | bool b => simp [erase, Tm.subst]
  | nat n => simp [erase, Tm.subst]

@[simp] theorem erase_substTy (S : ProjectBeth.Untyped.Signature)
    (σ : Nat → Ty) (t : Tm) : erase S (t.substTy σ) = erase S t := by
  induction t generalizing σ <;> simp [erase, Tm.substTy, *]

@[simp] theorem erase_instantiate (S : ProjectBeth.Untyped.Signature) (t x : Tm) :
    erase S (t.instantiate x) = (erase S t).subst0 (erase S x) := by
  rw [Tm.instantiate, erase_subst]
  unfold ProjectBeth.Untyped.Tm.subst0
  apply ProjectBeth.Untyped.Tm.subst_congr
  intro i; cases i <;> rfl

@[simp] theorem erase_instantiateTy (S : ProjectBeth.Untyped.Signature)
    (t : Tm) (X : Ty) : erase S (t.instantiateTy X) = erase S t := by
  simp [Tm.instantiateTy]

theorem smallStep_steps (S : ProjectBeth.Untyped.Signature) {t u : Tm}
    (h : SmallStep t u) :
    ProjectBeth.Untyped.Steps S (erase S t) (erase S u) := by
  induction h with
  | beta =>
    simpa [erase] using
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
        (ProjectBeth.Untyped.Step.beta (S := S) _ _))
  | tyBeta => simp only [erase, erase_instantiateTy]; exact .refl
  | app_left h ih =>
    exact ProjectBeth.Untyped.Steps.appLeft _ ih
  | app_right h ih =>
    exact ProjectBeth.Untyped.Steps.appRight _ ih
  | lam h ih => exact ProjectBeth.Untyped.Steps.lam ih
  | tyApp h ih => simpa [erase] using ih
  | tyLam h ih => simpa [erase] using ih

theorem typedStep_steps (S : ProjectBeth.Untyped.Signature) {s t : Typed Δ Γ A}
    (h : TypedStep s t) :
    ProjectBeth.Untyped.Steps S (erase S s.term) (erase S t.term) := by
  exact smallStep_steps S h.syntax_square

end ProjectBeth.SystemF.Inductive.Untyped
