import ProjectBeth.Defs.STLC.Variants

universe u

namespace ProjectBeth.Syntax

/-! Several deliberately coexisting representations of the untyped lambda calculus. -/

namespace Untyped

inductive Tm : Type
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
  deriving DecidableEq

def rename (ρ : Nat → Nat) : Tm → Tm
  | .var i => .var (ρ i)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .lam b => .lam (rename (fun i => match i with | 0 => 0 | i + 1 => ρ i + 1) b)

def lift (t : Tm) : Tm := rename Nat.succ t

def subst (σ : Nat → Tm) : Tm → Tm
  | .var i => σ i
  | .app f a => .app (subst σ f) (subst σ a)
  | .lam b => .lam (subst (fun i => match i with | 0 => .var 0 | i + 1 => lift (σ i)) b)

theorem rename_congr {ρ τ : Nat → Nat} (h : ∀ i, ρ i = τ i) (t : Tm) :
    rename ρ t = rename τ t := by
  induction t generalizing ρ τ with
  | var i => simp [rename, h]
  | app f a ihf iha => simp [rename, ihf h, iha h]
  | lam b ih =>
      simp only [rename]
      congr 1
      apply ih
      intro i
      cases i with
      | zero => rfl
      | succ i => simp [h]

@[simp] theorem rename_id (t : Tm) : rename id t = t := by
  induction t with
  | var i => rfl
  | app f a ihf iha => simp [rename, ihf, iha]
  | lam b ih =>
      rw [rename]
      apply congrArg Tm.lam
      calc
        rename (fun i => match i with | 0 => 0 | i + 1 => id i + 1) b = rename id b := by
          apply rename_congr
          intro i
          cases i <;> rfl
        _ = b := ih

theorem subst_congr {σ τ : Nat → Tm} (h : ∀ i, σ i = τ i) (t : Tm) :
    subst σ t = subst τ t := by
  induction t generalizing σ τ with
  | var i => exact h i
  | app f a ihf iha => simp [subst, ihf h, iha h]
  | lam b ih =>
      simp only [subst]
      congr 1
      apply ih
      intro i
      cases i with
      | zero => rfl
      | succ i => simp [h]

@[simp] theorem subst_var (t : Tm) : subst Tm.var t = t := by
  induction t with
  | var i => rfl
  | app f a ihf iha => simp [subst, ihf, iha]
  | lam b ih =>
      rw [subst]
      apply congrArg Tm.lam
      calc
        subst (fun i => match i with | 0 => .var 0 | i + 1 => lift (.var i)) b =
            subst Tm.var b := by
          apply subst_congr
          intro i
          cases i with
          | zero => rfl
          | succ i => rfl
        _ = b := ih

end Untyped

namespace Bounded

/-- Untyped terms whose free de Bruijn variables are bounded by `n`. -/
inductive Tm : Nat → Type
  | var : Fin n → Tm n
  | app : Tm n → Tm n → Tm n
  | lam : Tm (n + 1) → Tm n
  deriving DecidableEq

def erase : Tm n → Untyped.Tm
  | .var i => .var i
  | .app f a => .app (erase f) (erase a)
  | .lam b => .lam (erase b)

def check (n : Nat) : Untyped.Tm → Option (Tm n)
  | .var i => if h : i < n then some (.var ⟨i, h⟩) else none
  | .app f a => return .app (← check n f) (← check n a)
  | .lam b => return .lam (← check (n + 1) b)

@[simp] theorem check_erase (t : Tm n) : check n (erase t) = some t := by
  induction t with
  | var i => simp [erase, check, i.isLt]
  | app f a ihf iha => simp [erase, check, ihf, iha]
  | lam b ih => simp [erase, check, ih]

theorem erase_injective : Function.Injective (@erase n) := by
  intro a b h
  have := congrArg (check n) h
  simpa using this

end Bounded

namespace Named

/-- Explicit names are retained; terms are considered before quotienting by α-equivalence. -/
inductive Tm (Name : Type u) : Type u
  | var : Name → Tm Name
  | app : Tm Name → Tm Name → Tm Name
  | lam : Name → Tm Name → Tm Name
  deriving DecidableEq

end Named

namespace LocallyNameless

variable {Name : Type u}

inductive Var (Name : Type u) : Type u
  | bound : Nat → Var Name
  | free : Name → Var Name
  deriving DecidableEq

inductive Tm (Name : Type u) : Type u
  | var : Var Name → Tm Name
  | app : Tm Name → Tm Name → Tm Name
  | lam : Tm Name → Tm Name
  deriving DecidableEq

def indexOf? [DecidableEq Name] (x : Name) : List Name → Option Nat
  | [] => none
  | y :: ys => if x = y then some 0 else (indexOf? x ys).map Nat.succ

def ofNamed [DecidableEq Name] : List Name → Named.Tm Name → Tm Name
  | Γ, .var x => match indexOf? x Γ with
    | some i => .var (.bound i)
    | none => .var (.free x)
  | Γ, .app f a => .app (ofNamed Γ f) (ofNamed Γ a)
  | Γ, .lam x b => .lam (ofNamed (x :: Γ) b)

def close [DecidableEq Name] (x : Name) : Nat → Tm Name → Tm Name
  | k, .var (.free y) => if x = y then .var (.bound k) else .var (.free y)
  | _, .var (.bound i) => .var (.bound i)
  | k, .app f a => .app (close x k f) (close x k a)
  | k, .lam b => .lam (close x (k + 1) b)

def openAt (x : Name) : Nat → Tm Name → Tm Name
  | k, .var (.bound i) => if i = k then .var (.free x) else .var (.bound i)
  | _, .var (.free y) => .var (.free y)
  | k, .app f a => .app (openAt x k f) (openAt x k a)
  | k, .lam b => .lam (openAt x (k + 1) b)

@[simp] theorem ofNamed_nil_var [DecidableEq Name] (x : Name) :
    ofNamed [] (.var x) = .var (.free x) := by simp [ofNamed, indexOf?]

@[simp] theorem ofNamed_lam_var [DecidableEq Name] (x : Name) :
    ofNamed [] (.lam x (.var x)) = .lam (.var (.bound 0)) := by
  simp [ofNamed, indexOf?]

end LocallyNameless

namespace Intrinsic

abbrev Ty (Base : Type u) := STLC.Arrow.Ty Base
abbrev Tm {Base : Type u} := @STLC.Arrow.Tm Base

def eraseVar : STLC.Var Γ A → Fin Γ.length
  | .here => ⟨0, by simp⟩
  | .there v => ⟨eraseVar v + 1, by simpa using (eraseVar v).isLt⟩

def erase : Tm Γ A → Bounded.Tm Γ.length
  | .var v => .var (eraseVar v)
  | .app f a => .app (erase f) (erase a)
  | .lam b => .lam (by simpa using erase b)

/-- The ordinary extrinsic typing relation for bounded de Bruijn terms. -/
inductive HasType {Base : Type u} :
    (Γ : List (Ty Base)) → Bounded.Tm Γ.length → Ty Base → Prop
  | var (v : STLC.Var Γ A) : HasType Γ (.var (eraseVar v)) A
  | app : HasType Γ f (.arr A B) → HasType Γ a A → HasType Γ (.app f a) B
  | lam : HasType (A :: Γ) b B → HasType Γ (.lam (by simpa using b)) (.arr A B)

theorem erase_hasType (t : Tm Γ A) : HasType Γ (erase t) A := by
  induction t with
  | var v => exact .var v
  | app f a ihf iha => exact .app ihf iha
  | lam b ih => exact .lam ih

end Intrinsic

end ProjectBeth.Syntax
