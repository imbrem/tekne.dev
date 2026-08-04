import ProjectBeth.Defs.Syntax.Substitution

namespace ProjectBeth.SystemF.Inductive

inductive Ty : Type
  | var : Nat → Ty
  | bool : Ty
  | nat : Ty
  | arr : Ty → Ty → Ty
  | all : Ty → Ty
  deriving DecidableEq

def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def Ty.rename (ρ : Nat → Nat) : Ty → Ty
  | .var n => .var (ρ n)
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (A.rename ρ) (B.rename ρ)
  | .all A => .all (A.rename (upRen ρ))

def Ty.lift (A : Ty) : Ty := A.rename Nat.succ

def upTySub (σ : Nat → Ty) : Nat → Ty
  | 0 => .var 0
  | n + 1 => (σ n).lift

def Ty.subst (σ : Nat → Ty) : Ty → Ty
  | .var n => σ n
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (A.subst σ) (B.subst σ)
  | .all A => .all (A.subst (upTySub σ))

def Ty.instantiate (A X : Ty) : Ty := A.subst (fun | 0 => X | n + 1 => .var n)

theorem Ty.rename_congr {ρ τ : Nat → Nat} (h : ∀n, ρ n = τ n) :
    ∀ A : Ty, A.rename ρ = A.rename τ := by
  intro A
  induction A generalizing ρ τ with
  | var n => simp [Ty.rename, h]
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.rename, ihA h, ihB h]
  | all A ih =>
    simp only [Ty.rename]
    congr 1
    apply ih
    intro n
    cases n <;> simp [upRen, h]

@[simp] theorem Ty.rename_id (A : Ty) : A.rename id = A := by
  induction A with
  | var n => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.rename, ihA, ihB]
  | all A ih =>
    simp only [Ty.rename]
    rw [show upRen id = id by funext n; cases n <;> rfl, ih]

theorem Ty.rename_comp (ρ τ : Nat → Nat) (A : Ty) :
    (A.rename ρ).rename τ = A.rename (τ ∘ ρ) := by
  induction A generalizing ρ τ with
  | var n => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.rename, ihA, ihB]
  | all A ih =>
    simp only [Ty.rename, ih]
    apply congrArg Ty.all
    apply Ty.rename_congr
    intro n
    cases n <;> rfl

theorem Ty.subst_congr {σ τ : Nat → Ty} (h : ∀n, σ n = τ n) :
    ∀ A : Ty, A.subst σ = A.subst τ := by
  intro A
  induction A generalizing σ τ with
  | var n => exact h n
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.subst, ihA h, ihB h]
  | all A ih =>
    simp only [Ty.subst]
    congr 1
    apply ih
    intro n
    cases n <;> simp [upTySub, h]

@[simp] theorem Ty.subst_var (A : Ty) : A.subst Ty.var = A := by
  induction A with
  | var n => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.subst, ihA, ihB]
  | all A ih =>
    simp only [Ty.subst]
    rw [show upTySub Ty.var = Ty.var by funext n; cases n <;> rfl, ih]

theorem Ty.rename_lift (ρ : Nat → Nat) (A : Ty) :
    (A.lift).rename (upRen ρ) = (A.rename ρ).lift := by
  simp only [Ty.lift, Ty.rename_comp]
  apply Ty.rename_congr
  intro n
  rfl

theorem Ty.rename_subst (ρ : Nat → Nat) (σ : Nat → Ty) (A : Ty) :
    (A.subst σ).rename ρ = A.subst (fun n => (σ n).rename ρ) := by
  induction A generalizing ρ σ with
  | var n => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.rename, Ty.subst, ihA, ihB]
  | all A ih =>
    simp only [Ty.rename, Ty.subst, ih]
    apply congrArg Ty.all
    apply Ty.subst_congr
    intro n
    cases n with
    | zero => rfl
    | succ n => exact Ty.rename_lift ρ (σ n)

theorem Ty.subst_rename (σ : Nat → Ty) (ρ : Nat → Nat) (A : Ty) :
    (A.rename ρ).subst σ = A.subst (σ ∘ ρ) := by
  induction A generalizing σ ρ with
  | var n => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.rename, Ty.subst, ihA, ihB]
  | all A ih =>
    simp only [Ty.rename, Ty.subst, ih]
    apply congrArg Ty.all
    apply Ty.subst_congr
    intro n
    cases n <;> rfl

theorem Ty.subst_lift (σ : Nat → Ty) (A : Ty) :
    (A.lift).subst (upTySub σ) = (A.subst σ).lift := by
  rw [Ty.lift, Ty.subst_rename, Ty.lift, Ty.rename_subst]
  apply Ty.subst_congr
  intro n
  rfl

theorem Ty.subst_comp (σ τ : Nat → Ty) (A : Ty) :
    (A.subst σ).subst τ = A.subst (fun n => (σ n).subst τ) := by
  induction A generalizing σ τ with
  | var n => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.subst, ihA, ihB]
  | all A ih =>
    simp only [Ty.subst, ih]
    apply congrArg Ty.all
    apply Ty.subst_congr
    intro n
    cases n with
    | zero => rfl
    | succ n => exact Ty.subst_lift τ (σ n)

inductive Tm : Type
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Ty → Tm → Tm
  | tyApp : Tm → Ty → Tm
  | tyLam : Tm → Tm
  | bool : Bool → Tm
  | nat : Nat → Tm
  deriving DecidableEq

def upTmRen (ρ : Nat → Nat) : Nat → Nat := upRen ρ

def Tm.rename (ρ : Nat → Nat) : Tm → Tm
  | .var n => .var (ρ n)
  | .app f x => .app (f.rename ρ) (x.rename ρ)
  | .lam A t => .lam A (t.rename (upTmRen ρ))
  | .tyApp f A => .tyApp (f.rename ρ) A
  | .tyLam t => .tyLam (t.rename ρ)
  | .bool b => .bool b
  | .nat n => .nat n

def Tm.lift (t : Tm) : Tm := t.rename Nat.succ

def Tm.renameTy (ρ : Nat → Nat) : Tm → Tm
  | .var n => .var n
  | .app f x => .app (f.renameTy ρ) (x.renameTy ρ)
  | .lam A t => .lam (A.rename ρ) (t.renameTy ρ)
  | .tyApp f A => .tyApp (f.renameTy ρ) (A.rename ρ)
  | .tyLam t => .tyLam (t.renameTy (upRen ρ))
  | .bool b => .bool b
  | .nat n => .nat n

def upTmSub (σ : Nat → Tm) : Nat → Tm
  | 0 => .var 0
  | n + 1 => (σ n).lift

def Tm.subst (σ : Nat → Tm) : Tm → Tm
  | .var n => σ n
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .lam A t => .lam A (t.subst (upTmSub σ))
  | .tyApp f A => .tyApp (f.subst σ) A
  | .tyLam t => .tyLam (t.subst σ)
  | .bool b => .bool b
  | .nat n => .nat n

def Tm.substTy (σ : Nat → Ty) : Tm → Tm
  | .var n => .var n
  | .app f x => .app (f.substTy σ) (x.substTy σ)
  | .lam A t => .lam (A.subst σ) (t.substTy σ)
  | .tyApp f A => .tyApp (f.substTy σ) (A.subst σ)
  | .tyLam t => .tyLam (t.substTy (upTySub σ))
  | .bool b => .bool b
  | .nat n => .nat n

def Tm.instantiate (t x : Tm) : Tm := t.subst (fun | 0 => x | n + 1 => .var n)
def Tm.instantiateTy (t : Tm) (X : Ty) : Tm :=
  t.substTy (fun | 0 => X | n + 1 => .var n)

theorem Tm.rename_renameTy (ρ θ : Nat → Nat) (t : Tm) :
    (t.renameTy θ).rename ρ = (t.rename ρ).renameTy θ := by
  induction t generalizing ρ θ with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.rename, Tm.renameTy, ihf, ihx]
  | lam A t ih => simp [Tm.rename, Tm.renameTy, ih]
  | tyApp f A ih => simp [Tm.rename, Tm.renameTy, ih]
  | tyLam t ih => simp [Tm.rename, Tm.renameTy, ih]
  | bool b => rfl
  | nat n => rfl

theorem Tm.renameTy_congr {ρ θ : Nat → Nat} (h : ∀ n, ρ n = θ n) (t : Tm) :
    t.renameTy ρ = t.renameTy θ := by
  induction t generalizing ρ θ with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.renameTy, ihf h, ihx h]
  | lam A t ih => simp [Tm.renameTy, Ty.rename_congr h, ih h]
  | tyApp f A ih => simp [Tm.renameTy, Ty.rename_congr h, ih h]
  | tyLam t ih =>
    simp only [Tm.renameTy]
    congr 1
    apply ih
    intro n; cases n <;> simp [upRen, h]
  | bool b => rfl
  | nat n => rfl

theorem Tm.renameTy_comp (ρ θ : Nat → Nat) (t : Tm) :
    (t.renameTy ρ).renameTy θ = t.renameTy (θ ∘ ρ) := by
  induction t generalizing ρ θ with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.renameTy, ihf, ihx]
  | lam A t ih => simp [Tm.renameTy, Ty.rename_comp, ih]
  | tyApp f A ih => simp [Tm.renameTy, Ty.rename_comp, ih]
  | tyLam t ih =>
    simp only [Tm.renameTy, ih]
    apply congrArg Tm.tyLam
    apply Tm.renameTy_congr
    intro n
    cases n <;> rfl
  | bool b => rfl
  | nat n => rfl

theorem Tm.rename_congr {ρ τ : Nat → Nat} (h : ∀n, ρ n = τ n) (t : Tm) :
    t.rename ρ = t.rename τ := by
  induction t generalizing ρ τ with
  | var n => simp [Tm.rename, h]
  | app f x ihf ihx => simp [Tm.rename, ihf h, ihx h]
  | lam A t ih =>
    simp only [Tm.rename]
    congr 1
    apply ih
    intro n
    cases n <;> simp [upTmRen, upRen, h]
  | tyApp f A ih => simp [Tm.rename, ih h]
  | tyLam t ih => simp [Tm.rename, ih h]
  | bool b => rfl
  | nat n => rfl

@[simp] theorem Tm.rename_id (t : Tm) : t.rename id = t := by
  induction t with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.rename, ihf, ihx]
  | lam A t ih =>
    simp only [Tm.rename]
    rw [show upTmRen id = id by funext n; cases n <;> rfl, ih]
  | tyApp f A ih => simp [Tm.rename, ih]
  | tyLam t ih => simp [Tm.rename, ih]
  | bool b => rfl
  | nat n => rfl

theorem Tm.rename_comp (ρ τ : Nat → Nat) (t : Tm) :
    (t.rename ρ).rename τ = t.rename (τ ∘ ρ) := by
  induction t generalizing ρ τ with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.rename, ihf, ihx]
  | lam A t ih =>
    simp only [Tm.rename, ih]
    apply congrArg (Tm.lam A)
    apply Tm.rename_congr
    intro n
    cases n <;> rfl
  | tyApp f A ih => simp [Tm.rename, ih]
  | tyLam t ih => simp [Tm.rename, ih]
  | bool b => rfl
  | nat n => rfl

theorem Tm.subst_congr {σ τ : Nat → Tm} (h : ∀n, σ n = τ n) (t : Tm) :
    t.subst σ = t.subst τ := by
  induction t generalizing σ τ with
  | var n => exact h n
  | app f x ihf ihx => simp [Tm.subst, ihf h, ihx h]
  | lam A t ih =>
    simp only [Tm.subst]
    congr 1
    apply ih
    intro n
    cases n <;> simp [upTmSub, h]
  | tyApp f A ih => simp [Tm.subst, ih h]
  | tyLam t ih => simp [Tm.subst, ih h]
  | bool b => rfl
  | nat n => rfl

@[simp] theorem Tm.subst_var (t : Tm) : t.subst Tm.var = t := by
  induction t with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.subst, ihf, ihx]
  | lam A t ih =>
    simp only [Tm.subst]
    rw [show upTmSub Tm.var = Tm.var by funext n; cases n <;> rfl, ih]
  | tyApp f A ih => simp [Tm.subst, ih]
  | tyLam t ih => simp [Tm.subst, ih]
  | bool b => rfl
  | nat n => rfl

theorem Tm.rename_lift (ρ : Nat → Nat) (t : Tm) :
    t.lift.rename (upTmRen ρ) = (t.rename ρ).lift := by
  simp only [Tm.lift, Tm.rename_comp]
  apply Tm.rename_congr
  intro n
  rfl

theorem Tm.rename_subst (ρ : Nat → Nat) (σ : Nat → Tm) (t : Tm) :
    (t.subst σ).rename ρ = t.subst (fun n => (σ n).rename ρ) := by
  induction t generalizing ρ σ with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.rename, Tm.subst, ihf, ihx]
  | lam A t ih =>
    simp only [Tm.rename, Tm.subst, ih]
    apply congrArg (Tm.lam A)
    apply Tm.subst_congr
    intro n
    cases n with
    | zero => rfl
    | succ n => exact Tm.rename_lift ρ (σ n)
  | tyApp f A ih => simp [Tm.rename, Tm.subst, ih]
  | tyLam t ih => simp [Tm.rename, Tm.subst, ih]
  | bool b => rfl
  | nat n => rfl

theorem Tm.subst_rename (σ : Nat → Tm) (ρ : Nat → Nat) (t : Tm) :
    (t.rename ρ).subst σ = t.subst (σ ∘ ρ) := by
  induction t generalizing σ ρ with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.rename, Tm.subst, ihf, ihx]
  | lam A t ih =>
    simp only [Tm.rename, Tm.subst, ih]
    apply congrArg (Tm.lam A)
    apply Tm.subst_congr
    intro n
    cases n <;> rfl
  | tyApp f A ih => simp [Tm.rename, Tm.subst, ih]
  | tyLam t ih => simp [Tm.rename, Tm.subst, ih]
  | bool b => rfl
  | nat n => rfl

theorem Tm.subst_lift (σ : Nat → Tm) (t : Tm) :
    t.lift.subst (upTmSub σ) = (t.subst σ).lift := by
  rw [Tm.lift, Tm.subst_rename, Tm.lift, Tm.rename_subst]
  apply Tm.subst_congr
  intro n
  rfl

theorem Tm.subst_comp (σ τ : Nat → Tm) (t : Tm) :
    (t.subst σ).subst τ = t.subst (fun n => (σ n).subst τ) := by
  induction t generalizing σ τ with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.subst, ihf, ihx]
  | lam A t ih =>
    simp only [Tm.subst, ih]
    apply congrArg (Tm.lam A)
    apply Tm.subst_congr
    intro n
    cases n with
    | zero => rfl
    | succ n => exact Tm.subst_lift τ (σ n)
  | tyApp f A ih => simp [Tm.subst, ih]
  | tyLam t ih => simp [Tm.subst, ih]
  | bool b => rfl
  | nat n => rfl

theorem Tm.substTy_congr {σ τ : Nat → Ty} (h : ∀n, σ n = τ n) (t : Tm) :
    t.substTy σ = t.substTy τ := by
  induction t generalizing σ τ with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.substTy, ihf h, ihx h]
  | lam A t ih => simp [Tm.substTy, Ty.subst_congr h A, ih h]
  | tyApp f A ih => simp [Tm.substTy, Ty.subst_congr h A, ih h]
  | tyLam t ih =>
    simp only [Tm.substTy]
    congr 1
    apply ih
    intro n
    cases n <;> simp [upTySub, h]
  | bool b => rfl
  | nat n => rfl

@[simp] theorem Tm.substTy_var (t : Tm) : t.substTy Ty.var = t := by
  induction t with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.substTy, ihf, ihx]
  | lam A t ih => simp [Tm.substTy, ih]
  | tyApp f A ih => simp [Tm.substTy, ih]
  | tyLam t ih =>
    simp only [Tm.substTy]
    rw [show upTySub Ty.var = Ty.var by funext n; cases n <;> rfl, ih]
  | bool b => rfl
  | nat n => rfl

theorem Tm.substTy_comp (σ τ : Nat → Ty) (t : Tm) :
    (t.substTy σ).substTy τ = t.substTy (fun n => (σ n).subst τ) := by
  induction t generalizing σ τ with
  | var n => rfl
  | app f x ihf ihx => simp [Tm.substTy, ihf, ihx]
  | lam A t ih => simp [Tm.substTy, Ty.subst_comp, ih]
  | tyApp f A ih => simp [Tm.substTy, Ty.subst_comp, ih]
  | tyLam t ih =>
    simp only [Tm.substTy, ih]
    apply congrArg Tm.tyLam
    apply Tm.substTy_congr
    intro n
    cases n with
    | zero => rfl
    | succ n => exact Ty.subst_lift τ (σ n)
  | bool b => rfl
  | nat n => rfl

inductive HasType : Nat → List Ty → Tm → Ty → Prop
  | var : Γ[n]? = some A → HasType Δ Γ (.var n) A
  | app : HasType Δ Γ f (.arr A B) → HasType Δ Γ x A → HasType Δ Γ (.app f x) B
  | lam : HasType Δ (A :: Γ) t B → HasType Δ Γ (.lam A t) (.arr A B)
  | tyApp : HasType Δ Γ f (.all A) → HasType Δ Γ (.tyApp f X) (A.instantiate X)
  | tyLam : HasType (Δ + 1) (Γ.map Ty.lift) t A → HasType Δ Γ (.tyLam t) (.all A)
  | bool : HasType Δ Γ (.bool b) .bool
  | nat : HasType Δ Γ (.nat n) .nat

inductive SmallStep : Tm → Tm → Prop
  | beta : SmallStep (.app (.lam A t) x) (t.instantiate x)
  | tyBeta : SmallStep (.tyApp (.tyLam t) X) (t.instantiateTy X)
  | app_left : SmallStep f f' → SmallStep (.app f x) (.app f' x)
  | app_right : SmallStep x x' → SmallStep (.app f x) (.app f x')
  | lam : SmallStep t t' → SmallStep (.lam A t) (.lam A t')
  | tyApp : SmallStep f f' → SmallStep (.tyApp f X) (.tyApp f' X)
  | tyLam : SmallStep t t' → SmallStep (.tyLam t) (.tyLam t')

structure Typed (Δ : Nat) (Γ : List Ty) (A : Ty) where
  term : Tm
  typing : HasType Δ Γ term A

inductive TypedStep : Typed Δ Γ A → Typed Δ Γ A → Prop
  | ofSmallStep (s t : Typed Δ Γ A) : SmallStep s.term t.term → TypedStep s t

theorem subject_reduction {s t : Typed Δ Γ A} (_h : TypedStep s t) :
    HasType Δ Γ t.term A := t.typing

theorem TypedStep.syntax_square {s t : Typed Δ Γ A} (h : TypedStep s t) :
    SmallStep s.term t.term := by cases h with | ofSmallStep h => exact h

end ProjectBeth.SystemF.Inductive
