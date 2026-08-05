import ProjectBeth.Defs.SystemF.Syntax.LocallyNameless

namespace ProjectBeth.SystemF.Syntax.Named

universe u v
variable {Name : Type u} {TyName : Type u} {TmName : Type v}

inductive Ty (Name : Type u) : Type u
  | var : Name → Ty Name
  | bool | nat
  | arr : Ty Name → Ty Name → Ty Name
  | all : Name → Ty Name → Ty Name
  deriving DecidableEq

inductive Tm (TyName : Type u) (TmName : Type v) : Type (max u v)
  | var : TmName → Tm TyName TmName
  | app : Tm TyName TmName → Tm TyName TmName → Tm TyName TmName
  | lam : TmName → Ty TyName → Tm TyName TmName → Tm TyName TmName
  | tyApp : Tm TyName TmName → Ty TyName → Tm TyName TmName
  | tyLam : TyName → Tm TyName TmName → Tm TyName TmName
  | bool : Bool → Tm TyName TmName
  | nat : Nat → Tm TyName TmName
  deriving DecidableEq

def lookup [DecidableEq Name] (x : Name) : List Name → Option Nat
  | [] => none
  | y :: ys => if x = y then some 0 else Nat.succ <$> lookup x ys

def Ty.toLN [DecidableEq Name] (bound : List Name) : Ty Name → LocallyNameless.Ty Name
  | .var x => match lookup x bound with
    | some n => .var (.bound n)
    | none => .var (.free x)
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (A.toLN bound) (B.toLN bound)
  | .all x A => .all (A.toLN (x :: bound))

def Tm.toLN [DecidableEq TyName] [DecidableEq TmName]
    (boundTy : List TyName) (boundTm : List TmName) :
    Tm TyName TmName → LocallyNameless.Tm TyName TmName
  | .var x => match lookup x boundTm with
    | some n => .var (.bound n)
    | none => .var (.free x)
  | .app f x => .app (f.toLN boundTy boundTm) (x.toLN boundTy boundTm)
  | .lam x A t => .lam (A.toLN boundTy) (t.toLN boundTy (x :: boundTm))
  | .tyApp f A => .tyApp (f.toLN boundTy boundTm) (A.toLN boundTy)
  | .tyLam a t => .tyLam (t.toLN (a :: boundTy) boundTm)
  | .bool b => .bool b
  | .nat n => .nat n

/-- Alpha equivalence is equality after forgetting the spelling of binders. -/
def Ty.Alpha [DecidableEq Name] (A B : Ty Name) : Prop := A.toLN [] = B.toLN []

/-- Alpha equivalence for terms, simultaneously accounting for type and term binders. -/
def Tm.Alpha [DecidableEq TyName] [DecidableEq TmName]
    (t s : Tm TyName TmName) : Prop := t.toLN [] [] = s.toLN [] []

instance [DecidableEq Name] : Setoid (Ty Name) where
  r := Ty.Alpha
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

instance [DecidableEq TyName] [DecidableEq TmName] : Setoid (Tm TyName TmName) where
  r := Tm.Alpha
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

def Ty.erase [DecidableEq Name] (free : Name → Nat) (A : Ty Name) : Inductive.Ty :=
  (A.toLN []).erase free

def Tm.erase [DecidableEq TyName] [DecidableEq TmName]
    (freeTy : TyName → Nat) (freeTm : TmName → Nat) (t : Tm TyName TmName) : Inductive.Tm :=
  (t.toLN [] []).erase freeTy freeTm

theorem Ty.erase_eq_of_alpha [DecidableEq Name] {A B : Ty Name}
    (h : A.Alpha B) (free : Name → Nat) : A.erase free = B.erase free := by
  simp only [erase, Alpha] at *; rw [h]

theorem Tm.erase_eq_of_alpha [DecidableEq TyName] [DecidableEq TmName]
    {t s : Tm TyName TmName} (h : t.Alpha s)
    (freeTy : TyName → Nat) (freeTm : TmName → Nat) :
    t.erase freeTy freeTm = s.erase freeTy freeTm := by
  simp only [erase, Alpha] at *; rw [h]

end ProjectBeth.SystemF.Syntax.Named
