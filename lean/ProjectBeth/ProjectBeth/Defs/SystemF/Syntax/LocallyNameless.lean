import ProjectBeth.Defs.SystemF.Syntax.DeBruijn

namespace ProjectBeth.SystemF.Syntax.LocallyNameless

universe u v u' v'
variable {Name : Type u} {Name' : Type u'}
variable {TyName : Type u} {TmName : Type v}
variable {TyName' : Type u'} {TmName' : Type v'}

inductive Var (Name : Type u)
  | bound (index : Nat)
  | free (name : Name)
  deriving DecidableEq

inductive Ty (Name : Type u) : Type u
  | var : Var Name → Ty Name
  | bool | nat
  | arr : Ty Name → Ty Name → Ty Name
  | all : Ty Name → Ty Name
  deriving DecidableEq

inductive Tm (TyName : Type u) (TmName : Type v) : Type (max u v)
  | var : Var TmName → Tm TyName TmName
  | app : Tm TyName TmName → Tm TyName TmName → Tm TyName TmName
  | lam : Ty TyName → Tm TyName TmName → Tm TyName TmName
  | tyApp : Tm TyName TmName → Ty TyName → Tm TyName TmName
  | tyLam : Tm TyName TmName → Tm TyName TmName
  | bool : Bool → Tm TyName TmName
  | nat : Nat → Tm TyName TmName
  deriving DecidableEq

def up (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def Ty.erase (free : Name → Nat) : Ty Name → Inductive.Ty
  | .var (.bound n) => .var n
  | .var (.free x) => .var (free x)
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (A.erase free) (B.erase free)
  | .all A => .all (A.erase (Nat.succ ∘ free))

def Tm.erase (freeTy : TyName → Nat) (freeTm : TmName → Nat) :
    Tm TyName TmName → Inductive.Tm
  | .var (.bound n) => .var n
  | .var (.free x) => .var (freeTm x)
  | .app f x => .app (f.erase freeTy freeTm) (x.erase freeTy freeTm)
  | .lam A t => .lam (A.erase freeTy) (t.erase freeTy (Nat.succ ∘ freeTm))
  | .tyApp f A => .tyApp (f.erase freeTy freeTm) (A.erase freeTy)
  | .tyLam t => .tyLam (t.erase (Nat.succ ∘ freeTy) freeTm)
  | .bool b => .bool b
  | .nat n => .nat n

def Ty.renameFree (ρ : Name → Name') : Ty Name → Ty Name'
  | .var (.bound n) => .var (.bound n)
  | .var (.free x) => .var (.free (ρ x))
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (A.renameFree ρ) (B.renameFree ρ)
  | .all A => .all (A.renameFree ρ)

def Tm.renameFree (ρTy : TyName → TyName') (ρTm : TmName → TmName') :
    Tm TyName TmName → Tm TyName' TmName'
  | .var (.bound n) => .var (.bound n)
  | .var (.free x) => .var (.free (ρTm x))
  | .app f x => .app (f.renameFree ρTy ρTm) (x.renameFree ρTy ρTm)
  | .lam A t => .lam (A.renameFree ρTy) (t.renameFree ρTy ρTm)
  | .tyApp f A => .tyApp (f.renameFree ρTy ρTm) (A.renameFree ρTy)
  | .tyLam t => .tyLam (t.renameFree ρTy ρTm)
  | .bool b => .bool b
  | .nat n => .nat n

def Var.openAt (k : Nat) (x : Name) : Var Name → Var Name
  | .bound n => if n = k then .free x else .bound n
  | .free y => .free y

def Var.closeAt [DecidableEq Name] (k : Nat) (x : Name) : Var Name → Var Name
  | .bound n => .bound n
  | .free y => if y = x then .bound k else .free y

def Ty.openAt (k : Nat) (x : Name) : Ty Name → Ty Name
  | .var v => .var (v.openAt k x)
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (A.openAt k x) (B.openAt k x)
  | .all A => .all (A.openAt (k + 1) x)

def Ty.closeAt [DecidableEq Name] (k : Nat) (x : Name) : Ty Name → Ty Name
  | .var v => .var (v.closeAt k x)
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (A.closeAt k x) (B.closeAt k x)
  | .all A => .all (A.closeAt (k + 1) x)

abbrev Ty.open (A : Ty Name) (x : Name) := A.openAt 0 x
abbrev Ty.close [DecidableEq Name] (A : Ty Name) (x : Name) := A.closeAt 0 x

def Ty.substFree (σ : Name → Ty Name') : Ty Name → Ty Name'
  | .var (.bound n) => .var (.bound n)
  | .var (.free x) => σ x
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (A.substFree σ) (B.substFree σ)
  | .all A => .all (A.substFree σ)

def Tm.openTmAt (k : Nat) (x : TmName) : Tm TyName TmName → Tm TyName TmName
  | .var v => .var (v.openAt k x)
  | .app f a => .app (f.openTmAt k x) (a.openTmAt k x)
  | .lam A t => .lam A (t.openTmAt (k + 1) x)
  | .tyApp f A => .tyApp (f.openTmAt k x) A
  | .tyLam t => .tyLam (t.openTmAt k x)
  | .bool b => .bool b
  | .nat n => .nat n

def Tm.closeTmAt [DecidableEq TmName] (k : Nat) (x : TmName) :
    Tm TyName TmName → Tm TyName TmName
  | .var v => .var (v.closeAt k x)
  | .app f a => .app (f.closeTmAt k x) (a.closeTmAt k x)
  | .lam A t => .lam A (t.closeTmAt (k + 1) x)
  | .tyApp f A => .tyApp (f.closeTmAt k x) A
  | .tyLam t => .tyLam (t.closeTmAt k x)
  | .bool b => .bool b
  | .nat n => .nat n

def Tm.openTyAt (k : Nat) (x : TyName) : Tm TyName TmName → Tm TyName TmName
  | .var v => .var v
  | .app f a => .app (f.openTyAt k x) (a.openTyAt k x)
  | .lam A t => .lam (A.openAt k x) (t.openTyAt k x)
  | .tyApp f A => .tyApp (f.openTyAt k x) (A.openAt k x)
  | .tyLam t => .tyLam (t.openTyAt (k + 1) x)
  | .bool b => .bool b
  | .nat n => .nat n

def Tm.closeTyAt [DecidableEq TyName] (k : Nat) (x : TyName) :
    Tm TyName TmName → Tm TyName TmName
  | .var v => .var v
  | .app f a => .app (f.closeTyAt k x) (a.closeTyAt k x)
  | .lam A t => .lam (A.closeAt k x) (t.closeTyAt k x)
  | .tyApp f A => .tyApp (f.closeTyAt k x) (A.closeAt k x)
  | .tyLam t => .tyLam (t.closeTyAt (k + 1) x)
  | .bool b => .bool b
  | .nat n => .nat n

theorem Ty.erase_openAt (A : Ty Name) (free : Name → Nat) (x : Name)
    (hx : free x = k) : (A.openAt k x).erase free = A.erase free := by
  induction A generalizing k free with
  | var v =>
    cases v with
    | bound n =>
      by_cases h : n = k
      · subst n; simp [Ty.openAt, Var.openAt, Ty.erase, hx]
      · simp [Ty.openAt, Var.openAt, Ty.erase, h]
    | free y => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [openAt, erase, ihA free hx, ihB free hx]
  | all A ih =>
    simp [openAt, erase]
    exact ih (fun y => free y + 1) (by simp [hx])

theorem Ty.erase_closeAt [DecidableEq Name] (A : Ty Name) (free : Name → Nat) (x : Name)
    (hx : free x = k) : (A.closeAt k x).erase free = A.erase free := by
  induction A generalizing k free with
  | var v =>
    cases v with
    | bound n => rfl
    | free y =>
      by_cases h : y = x
      · subst y; simp [Ty.closeAt, Var.closeAt, Ty.erase, hx]
      · simp [Ty.closeAt, Var.closeAt, Ty.erase, h]
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [closeAt, erase, ihA free hx, ihB free hx]
  | all A ih =>
    simp [closeAt, erase]
    exact ih (fun y => free y + 1) (by simp [hx])

theorem Tm.erase_openTmAt (t : Tm TyName TmName)
    (freeTy : TyName → Nat) (freeTm : TmName → Nat) (x : TmName)
    (hx : freeTm x = k) :
    (t.openTmAt k x).erase freeTy freeTm = t.erase freeTy freeTm := by
  induction t generalizing k freeTy freeTm with
  | var v =>
    cases v with
    | bound n =>
      by_cases h : n = k
      · subst n; simp [openTmAt, Var.openAt, Tm.erase, hx]
      · simp [openTmAt, Var.openAt, Tm.erase, h]
    | free y => rfl
  | app f a ihf iha => simp [openTmAt, Tm.erase, ihf freeTy freeTm hx, iha freeTy freeTm hx]
  | lam A t ih =>
    simp [openTmAt, Tm.erase]
    exact ih freeTy (fun y => freeTm y + 1) (by simp [hx])
  | tyApp f A ih => simp [openTmAt, Tm.erase, ih freeTy freeTm hx]
  | tyLam t ih => exact congrArg Inductive.Tm.tyLam (ih _ _ hx)
  | bool b => rfl
  | nat n => rfl

theorem Tm.erase_closeTmAt [DecidableEq TmName] (t : Tm TyName TmName)
    (freeTy : TyName → Nat) (freeTm : TmName → Nat) (x : TmName)
    (hx : freeTm x = k) :
    (t.closeTmAt k x).erase freeTy freeTm = t.erase freeTy freeTm := by
  induction t generalizing k freeTy freeTm with
  | var v =>
    cases v with
    | bound n => rfl
    | free y =>
      by_cases h : y = x
      · subst y; simp [closeTmAt, Var.closeAt, Tm.erase, hx]
      · simp [closeTmAt, Var.closeAt, Tm.erase, h]
  | app f a ihf iha => simp [closeTmAt, Tm.erase, ihf freeTy freeTm hx, iha freeTy freeTm hx]
  | lam A t ih =>
    simp [closeTmAt, Tm.erase]
    exact ih freeTy (fun y => freeTm y + 1) (by simp [hx])
  | tyApp f A ih => simp [closeTmAt, Tm.erase, ih freeTy freeTm hx]
  | tyLam t ih => exact congrArg Inductive.Tm.tyLam (ih _ _ hx)
  | bool b => rfl
  | nat n => rfl

theorem Tm.erase_openTyAt (t : Tm TyName TmName)
    (freeTy : TyName → Nat) (freeTm : TmName → Nat) (x : TyName)
    (hx : freeTy x = k) :
    (t.openTyAt k x).erase freeTy freeTm = t.erase freeTy freeTm := by
  induction t generalizing k freeTy freeTm with
  | var v => rfl
  | app f a ihf iha => simp [openTyAt, Tm.erase, ihf freeTy freeTm hx, iha freeTy freeTm hx]
  | lam A t ih =>
    simp only [openTyAt, Tm.erase, Ty.erase_openAt A freeTy x hx]
    congr 1
    exact ih freeTy (Nat.succ ∘ freeTm) hx
  | tyApp f A ih => simp [openTyAt, Tm.erase, Ty.erase_openAt A freeTy x hx, ih freeTy freeTm hx]
  | tyLam t ih =>
    simp [openTyAt, Tm.erase]
    exact ih (fun y => freeTy y + 1) freeTm (by simp [hx])
  | bool b => rfl
  | nat n => rfl

theorem Tm.erase_closeTyAt [DecidableEq TyName] (t : Tm TyName TmName)
    (freeTy : TyName → Nat) (freeTm : TmName → Nat) (x : TyName)
    (hx : freeTy x = k) :
    (t.closeTyAt k x).erase freeTy freeTm = t.erase freeTy freeTm := by
  induction t generalizing k freeTy freeTm with
  | var v => rfl
  | app f a ihf iha => simp [closeTyAt, Tm.erase, ihf freeTy freeTm hx, iha freeTy freeTm hx]
  | lam A t ih =>
    simp only [closeTyAt, Tm.erase, Ty.erase_closeAt A freeTy x hx]
    congr 1
    exact ih freeTy (Nat.succ ∘ freeTm) hx
  | tyApp f A ih => simp [closeTyAt, Tm.erase, Ty.erase_closeAt A freeTy x hx, ih freeTy freeTm hx]
  | tyLam t ih =>
    simp [closeTyAt, Tm.erase]
    exact ih (fun y => freeTy y + 1) freeTm (by simp [hx])
  | bool b => rfl
  | nat n => rfl

@[simp] theorem Ty.erase_renameFree (A : Ty Name) (ρ : Name → Name') (free : Name' → Nat) :
    (A.renameFree ρ).erase free = A.erase (free ∘ ρ) := by
  induction A generalizing free with
  | var x => cases x <;> rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [renameFree, erase, ihA, ihB]
  | all A ih => simp [renameFree, erase, ih, Function.comp_def]

@[simp] theorem Tm.erase_renameFree (t : Tm TyName TmName)
    (ρTy : TyName → TyName') (ρTm : TmName → TmName')
    (freeTy : TyName' → Nat) (freeTm : TmName' → Nat) :
    (t.renameFree ρTy ρTm).erase freeTy freeTm =
      t.erase (freeTy ∘ ρTy) (freeTm ∘ ρTm) := by
  induction t generalizing freeTy freeTm with
  | var x => cases x <;> rfl
  | app f x ihf ihx => simp [renameFree, erase, ihf, ihx]
  | lam A t ih => simp [renameFree, erase, ih, Ty.erase_renameFree, Function.comp_def]
  | tyApp f A ih => simp [renameFree, erase, ih, Ty.erase_renameFree]
  | tyLam t ih => simp [renameFree, erase, ih, Function.comp_def]
  | bool b => rfl
  | nat n => rfl

end ProjectBeth.SystemF.Syntax.LocallyNameless
