import ProjectBeth.Defs.SystemF.Syntax.DeBruijn

namespace ProjectBeth.SystemF.Syntax.Bounded

/-- System F types whose free type variables are statically bounded. -/
inductive Ty : Nat → Type
  | var : Fin Δ → Ty Δ
  | bool : Ty Δ
  | nat : Ty Δ
  | arr : Ty Δ → Ty Δ → Ty Δ
  | all : Ty (Δ + 1) → Ty Δ
  deriving DecidableEq

/-- System F terms with separate static bounds for type and term variables. -/
inductive Tm : (Δ Γ : Nat) → Type
  | var : Fin Γ → Tm Δ Γ
  | app : Tm Δ Γ → Tm Δ Γ → Tm Δ Γ
  | lam : Ty Δ → Tm Δ (Γ + 1) → Tm Δ Γ
  | tyApp : Tm Δ Γ → Ty Δ → Tm Δ Γ
  | tyLam : Tm (Δ + 1) Γ → Tm Δ Γ
  | bool : Bool → Tm Δ Γ
  | nat : Nat → Tm Δ Γ
  deriving DecidableEq

def Ty.erase : Ty Δ → Inductive.Ty
  | .var i => .var i
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr A.erase B.erase
  | .all A => .all A.erase

def Tm.erase : Tm Δ Γ → Inductive.Tm
  | .var i => .var i
  | .app f x => .app f.erase x.erase
  | .lam A t => .lam A.erase t.erase
  | .tyApp f A => .tyApp f.erase A.erase
  | .tyLam t => .tyLam t.erase
  | .bool b => .bool b
  | .nat n => .nat n

def Ty.check (Δ : Nat) : Inductive.Ty → Option (Ty Δ)
  | .var n => if h : n < Δ then some (.var ⟨n, h⟩) else none
  | .bool => some .bool
  | .nat => some .nat
  | .arr A B => return .arr (← Ty.check Δ A) (← Ty.check Δ B)
  | .all A => return .all (← Ty.check (Δ + 1) A)

def Tm.check (Δ Γ : Nat) : Inductive.Tm → Option (Tm Δ Γ)
  | .var n => if h : n < Γ then some (.var ⟨n, h⟩) else none
  | .app f x => return .app (← Tm.check Δ Γ f) (← Tm.check Δ Γ x)
  | .lam A t => return .lam (← Ty.check Δ A) (← Tm.check Δ (Γ + 1) t)
  | .tyApp f A => return .tyApp (← Tm.check Δ Γ f) (← Ty.check Δ A)
  | .tyLam t => return .tyLam (← Tm.check (Δ + 1) Γ t)
  | .bool b => some (.bool b)
  | .nat n => some (.nat n)

@[simp] theorem Ty.check_erase (A : Ty Δ) : Ty.check Δ A.erase = some A := by
  induction A <;> simp [erase, check, Fin.isLt, *]

@[simp] theorem Tm.check_erase (t : Tm Δ Γ) : Tm.check Δ Γ t.erase = some t := by
  induction t <;> simp [erase, check, Ty.check_erase, Fin.isLt, *]

def Ty.rename (ρ : Fin Δ → Fin Δ') : Ty Δ → Ty Δ'
  | .var i => .var (ρ i)
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (A.rename ρ) (B.rename ρ)
  | .all A => .all (A.rename (Fin.cases 0 (fun i => Fin.succ (ρ i))))

def Tm.rename (ρTy : Fin Δ → Fin Δ') (ρTm : Fin Γ → Fin Γ') :
    Tm Δ Γ → Tm Δ' Γ'
  | .var i => .var (ρTm i)
  | .app f x => .app (f.rename ρTy ρTm) (x.rename ρTy ρTm)
  | .lam A t => .lam (A.rename ρTy)
      (t.rename ρTy (Fin.cases 0 (fun i => Fin.succ (ρTm i))))
  | .tyApp f A => .tyApp (f.rename ρTy ρTm) (A.rename ρTy)
  | .tyLam t => .tyLam
      (t.rename (Fin.cases 0 (fun i => Fin.succ (ρTy i))) ρTm)
  | .bool b => .bool b
  | .nat n => .nat n

def extendFin (ρ : Fin n → Fin m) : Nat → Nat
  | i => if h : i < n then (ρ ⟨i, h⟩).val else i - n + m

@[simp] theorem extendFin_apply (ρ : Fin n → Fin m) (i : Fin n) :
    extendFin ρ i = ρ i := by simp [extendFin, i.isLt]

def Ty.renameRaw (ρ : Fin Δ → Fin Δ') : Ty Δ → Inductive.Ty
  | .var i => .var (ρ i)
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (A.renameRaw ρ) (B.renameRaw ρ)
  | .all A => .all (A.renameRaw (Fin.cases 0 (fun i => Fin.succ (ρ i))))

/-- The independently implemented bounded renaming commutes with erasure into
the shared raw representation. -/
@[simp] theorem Ty.erase_rename (A : Ty Δ) (ρ : Fin Δ → Fin Δ') :
    (A.rename ρ).erase = A.renameRaw ρ := by
  induction A generalizing Δ' <;> simp [rename, erase, renameRaw, *]

end ProjectBeth.SystemF.Syntax.Bounded
