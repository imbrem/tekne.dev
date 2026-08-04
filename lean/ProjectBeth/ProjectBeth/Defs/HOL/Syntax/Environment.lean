import ProjectBeth.Defs.HOL.Syntax

/-! Concrete, monomorphic HOL syntax with the traditional sequential definition
environment.  This is deliberately independent of the generic syntax tower: it
is a second implementation which is grounded by the translations below. -/

universe u v w

namespace ProjectBeth.HOL.Syntax.Environment

variable {Base : Type u} {TyName : Type v} {ConstName : Type w}

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def rawRename (ρ : Nat → Nat) : HOL.Tm Base → HOL.Tm Base
  | .var n => .var (ρ n)
  | .app f x => .app (rawRename ρ f) (rawRename ρ x)
  | .lam A t => .lam A (rawRename (liftRen ρ) t)
  | .bool b => .bool b
  | .eq A x y => .eq A (rawRename ρ x) (rawRename ρ y)
  | .epsilon A p => .epsilon A (rawRename ρ p)
  | .abs A p x => .abs A (rawRename (liftRen ρ) p) (rawRename ρ x)
  | .rep A p x => .rep A (rawRename (liftRen ρ) p) (rawRename ρ x)

namespace Minimal

inductive Ty (Base : Type u) : Type u
  | base : Base → Ty Base
  | bool : Ty Base
  | arr : Ty Base → Ty Base → Ty Base
  deriving DecidableEq

inductive Tm (Base : Type u) : Type u
  | var : Nat → Tm Base
  | app : Tm Base → Tm Base → Tm Base
  | lam : Ty Base → Tm Base → Tm Base
  | bool : Bool → Tm Base
  | eq : Ty Base → Tm Base → Tm Base → Tm Base

def Ty.toRaw : Ty Base → HOL.Ty Base
  | .base b => .base b
  | .bool => .bool
  | .arr a b => .arr a.toRaw b.toRaw

def Tm.toRaw : Tm Base → HOL.Tm Base
  | .var n => .var n
  | .app f x => .app f.toRaw x.toRaw
  | .lam A t => .lam A.toRaw t.toRaw
  | .bool b => .bool b
  | .eq A x y => .eq A.toRaw x.toRaw y.toRaw

def Tm.rename (ρ : Nat → Nat) : Tm Base → Tm Base
  | .var n => .var (ρ n)
  | .app f x => .app (f.rename ρ) (x.rename ρ)
  | .lam A t => .lam A (t.rename (Environment.liftRen ρ))
  | .bool b => .bool b
  | .eq A x y => .eq A (x.rename ρ) (y.rename ρ)

@[simp] theorem Tm.toRaw_rename (t : Tm Base) (ρ : Nat → Nat) :
    (t.rename ρ).toRaw = rawRename ρ t.toRaw := by
  induction t generalizing ρ <;> simp [Tm.rename, Tm.toRaw, rawRename, *]

end Minimal

namespace Choice

inductive Ty (Base : Type u) : Type u
  | base : Base → Ty Base
  | bool : Ty Base
  | arr : Ty Base → Ty Base → Ty Base
  deriving DecidableEq

inductive Tm (Base : Type u) : Type u
  | var : Nat → Tm Base
  | app : Tm Base → Tm Base → Tm Base
  | lam : Ty Base → Tm Base → Tm Base
  | bool : Bool → Tm Base
  | eq : Ty Base → Tm Base → Tm Base → Tm Base
  | epsilon : Ty Base → Tm Base → Tm Base

def Ty.ofMinimal : Minimal.Ty Base → Ty Base
  | .base b => .base b
  | .bool => .bool
  | .arr a b => .arr (Ty.ofMinimal a) (Ty.ofMinimal b)

def Tm.ofMinimal : Minimal.Tm Base → Tm Base
  | .var n => .var n
  | .app f x => .app (Tm.ofMinimal f) (Tm.ofMinimal x)
  | .lam A t => .lam (Ty.ofMinimal A) (Tm.ofMinimal t)
  | .bool b => .bool b
  | .eq A x y => .eq (Ty.ofMinimal A) (Tm.ofMinimal x) (Tm.ofMinimal y)

def Ty.project : Ty Base → Minimal.Ty Base
  | .base b => .base b
  | .bool => .bool
  | .arr a b => .arr a.project b.project

def Tm.project : Tm Base → Option (Minimal.Tm Base)
  | .var n => some (.var n)
  | .app f x => return .app (← f.project) (← x.project)
  | .lam A t => return .lam A.project (← t.project)
  | .bool b => some (.bool b)
  | .eq A x y => return .eq A.project (← x.project) (← y.project)
  | .epsilon _ _ => none

@[simp] theorem Ty.project_ofMinimal (A : Minimal.Ty Base) : (Ty.ofMinimal A).project = A := by
  induction A <;> simp [Ty.ofMinimal, Ty.project, *]

@[simp] theorem Tm.project_ofMinimal (t : Minimal.Tm Base) : (Tm.ofMinimal t).project = some t := by
  induction t <;> simp [Tm.ofMinimal, Tm.project, Ty.project_ofMinimal, *]

theorem Ty.ofMinimal_injective : Function.Injective (@Ty.ofMinimal Base) := by
  intro A B h
  simpa using congrArg Ty.project h

theorem Tm.ofMinimal_injective : Function.Injective (@Tm.ofMinimal Base) := by
  intro t s h
  simpa using congrArg Tm.project h

def Ty.toRaw : Ty Base → HOL.Ty Base
  | .base b => .base b
  | .bool => .bool
  | .arr a b => .arr a.toRaw b.toRaw

def Tm.toRaw : Tm Base → HOL.Tm Base
  | .var n => .var n
  | .app f x => .app f.toRaw x.toRaw
  | .lam A t => .lam A.toRaw t.toRaw
  | .bool b => .bool b
  | .eq A x y => .eq A.toRaw x.toRaw y.toRaw
  | .epsilon A p => .epsilon A.toRaw p.toRaw

def Tm.rename (ρ : Nat → Nat) : Tm Base → Tm Base
  | .var n => .var (ρ n)
  | .app f x => .app (f.rename ρ) (x.rename ρ)
  | .lam A t => .lam A (t.rename (Environment.liftRen ρ))
  | .bool b => .bool b
  | .eq A x y => .eq A (x.rename ρ) (y.rename ρ)
  | .epsilon A p => .epsilon A (p.rename ρ)

@[simp] theorem Ty.toRaw_ofMinimal (A : Minimal.Ty Base) :
    (Ty.ofMinimal A).toRaw = A.toRaw := by induction A <;> simp [Ty.ofMinimal, Ty.toRaw, Minimal.Ty.toRaw, *]

@[simp] theorem Tm.toRaw_ofMinimal (t : Minimal.Tm Base) :
    (Tm.ofMinimal t).toRaw = t.toRaw := by induction t <;> simp [Tm.ofMinimal, Tm.toRaw, Minimal.Tm.toRaw, Ty.toRaw_ofMinimal, *]

@[simp] theorem Tm.rename_ofMinimal (t : Minimal.Tm Base) (ρ : Nat → Nat) :
    Tm.rename ρ (Tm.ofMinimal t) = Tm.ofMinimal (t.rename ρ) := by
  induction t generalizing ρ <;> simp [Tm.rename, Tm.ofMinimal, Minimal.Tm.rename, *]

@[simp] theorem Tm.toRaw_rename (t : Tm Base) (ρ : Nat → Nat) :
    (t.rename ρ).toRaw = rawRename ρ t.toRaw := by
  induction t generalizing ρ <;> simp [Tm.rename, Tm.toRaw, rawRename, *]

end Choice

namespace Defined

/-- User type names and constants are syntax, not aliases for their definitions. -/
inductive Ty (Base : Type u) (TyName : Type v) : Type (max u v)
  | base : Base → Ty Base TyName
  | bool : Ty Base TyName
  | arr : Ty Base TyName → Ty Base TyName → Ty Base TyName
  | defined : TyName → Ty Base TyName
  deriving DecidableEq

inductive Tm (Base : Type u) (TyName : Type v) (ConstName : Type w) : Type (max u v w)
  | var : Nat → Tm Base TyName ConstName
  | const : ConstName → Tm Base TyName ConstName
  | app : Tm Base TyName ConstName → Tm Base TyName ConstName → Tm Base TyName ConstName
  | lam : Ty Base TyName → Tm Base TyName ConstName → Tm Base TyName ConstName
  | bool : Bool → Tm Base TyName ConstName
  | eq : Ty Base TyName → Tm Base TyName ConstName → Tm Base TyName ConstName → Tm Base TyName ConstName
  | epsilon : Ty Base TyName → Tm Base TyName ConstName → Tm Base TyName ConstName
  | abs : TyName → Tm Base TyName ConstName → Tm Base TyName ConstName
  | rep : TyName → Tm Base TyName ConstName → Tm Base TyName ConstName

def Ty.ofChoice : Choice.Ty Base → Ty Base TyName
  | .base b => .base b
  | .bool => .bool
  | .arr a b => .arr (Ty.ofChoice a) (Ty.ofChoice b)

def Tm.ofChoice : Choice.Tm Base → Tm Base TyName ConstName
  | .var n => .var n
  | .app f x => .app (Tm.ofChoice f) (Tm.ofChoice x)
  | .lam A t => .lam (Ty.ofChoice A) (Tm.ofChoice t)
  | .bool b => .bool b
  | .eq A x y => .eq (Ty.ofChoice A) (Tm.ofChoice x) (Tm.ofChoice y)
  | .epsilon A p => .epsilon (Ty.ofChoice A) (Tm.ofChoice p)

inductive Obstruction (TyName : Type v) (ConstName : Type w)
  | type (name : TyName) | const (name : ConstName) | abs (name : TyName) | rep (name : TyName)

def Ty.project : Ty Base TyName → Except (Obstruction TyName ConstName) (Choice.Ty Base)
  | .base b => pure (.base b)
  | .bool => pure .bool
  | .arr a b => return .arr (← a.project) (← b.project)
  | .defined n => .error (.type n)

def Tm.project : Tm Base TyName ConstName → Except (Obstruction TyName ConstName) (Choice.Tm Base)
  | .var n => pure (.var n)
  | .const c => .error (.const c)
  | .app f x => return .app (← f.project) (← x.project)
  | .lam A t => return .lam (← A.project) (← t.project)
  | .bool b => pure (.bool b)
  | .eq A x y => return .eq (← A.project) (← x.project) (← y.project)
  | .epsilon A p => return .epsilon (← A.project) (← p.project)
  | .abs n _ => .error (.abs n)
  | .rep n _ => .error (.rep n)

@[simp] theorem Ty.project_ofChoice (A : Choice.Ty Base) :
    (Ty.ofChoice A : Ty Base TyName).project (ConstName := ConstName) = .ok A := by
  induction A with
  | base b => rfl
  | bool => rfl
  | arr A B ihA ihB => simp only [Ty.ofChoice, Ty.project, ihA, ihB]; rfl

@[simp] theorem Tm.project_ofChoice (t : Choice.Tm Base) :
    (Tm.ofChoice t : Tm Base TyName ConstName).project = .ok t := by
  induction t with
  | var n => rfl
  | app f x ihf ihx => simp only [Tm.ofChoice, Tm.project, ihf, ihx]; rfl
  | lam A t ih => simp only [Tm.ofChoice, Tm.project, Ty.project_ofChoice, ih]; rfl
  | bool b => rfl
  | eq A x y ihx ihy => simp only [Tm.ofChoice, Tm.project, Ty.project_ofChoice, ihx, ihy]; rfl
  | epsilon A p ih => simp only [Tm.ofChoice, Tm.project, Ty.project_ofChoice, ih]; rfl

theorem Ty.ofChoice_injective {ConstName : Type w} : Function.Injective
    (@Ty.ofChoice Base TyName) := by
  intro A B h
  simpa using congrArg (Ty.project (ConstName := ConstName)) h

theorem Tm.ofChoice_injective : Function.Injective
    (@Tm.ofChoice Base TyName ConstName) := by
  intro t s h
  simpa using congrArg Tm.project h

/-- Traditional HOL environments introduce constants and types in sequence.
The definition bodies only mention earlier declarations when `Wf` below holds. -/
inductive Decl (Base : Type u) (TyName : Type v) (ConstName : Type w)
  | constdef (name : ConstName) (type : Ty Base TyName) (rhs : Tm Base TyName ConstName)
  | typedef (name : TyName) (rep : Ty Base TyName) (predicate : Tm Base TyName ConstName)

abbrev Env (Base : Type u) (TyName : Type v) (ConstName : Type w) :=
  List (Decl Base TyName ConstName)

inductive HasTypeDef : Env Base TyName ConstName → TyName → Ty Base TyName →
    Tm Base TyName ConstName → Prop
  | here {n A p E} : HasTypeDef (.typedef n A p :: E) n A p
  | there {E n A p d} : HasTypeDef E n A p → HasTypeDef (d :: E) n A p

inductive HasConstDef : Env Base TyName ConstName → ConstName → Ty Base TyName →
    Tm Base TyName ConstName → Prop
  | here {c A t E} : HasConstDef (.constdef c A t :: E) c A t
  | there {E c A t d} : HasConstDef E c A t → HasConstDef (d :: E) c A t

abbrev Ctx (Base : Type u) (TyName : Type v) := List (Ty Base TyName)

mutual
  inductive Ty.Wf (E : Env Base TyName ConstName) : Ty Base TyName → Prop
    | base (b : Base) : Ty.Wf E (.base b)
    | bool : Ty.Wf E .bool
    | arr {A B} : Ty.Wf E A → Ty.Wf E B → Ty.Wf E (.arr A B)
    | defined {n A p} : HasTypeDef E n A p → Ty.Wf E A → HasType E [A] p .bool → Ty.Wf E (.defined n)

  inductive HasType (E : Env Base TyName ConstName) :
      Ctx Base TyName → Tm Base TyName ConstName → Ty Base TyName → Prop
    | var {Γ n A} : Γ[n]? = some A → HasType E Γ (.var n) A
    | const {c A rhs Γ} : HasConstDef E c A rhs → Ty.Wf E A → HasType E [] rhs A → HasType E Γ (.const c) A
    | app {Γ f A B x} : HasType E Γ f (.arr A B) → HasType E Γ x A → HasType E Γ (.app f x) B
    | lam {A Γ t B} : Ty.Wf E A → HasType E (A :: Γ) t B → HasType E Γ (.lam A t) (.arr A B)
    | bool {Γ b} : HasType E Γ (.bool b) .bool
    | eq {A Γ x y} : Ty.Wf E A → HasType E Γ x A → HasType E Γ y A → HasType E Γ (.eq A x y) .bool
    | epsilon {A Γ p} : Ty.Wf E A → HasType E Γ p (.arr A .bool) → HasType E Γ (.epsilon A p) A
    | abs {n A p Γ x} : HasTypeDef E n A p → HasType E Γ x A → HasType E Γ (.abs n x) (.defined n)
    | rep {n A p Γ x} : HasTypeDef E n A p → HasType E Γ x (.defined n) → HasType E Γ (.rep n x) A
end

/-- Every declaration is checked against the strictly earlier tail.  This is
the usual HOL discipline and excludes recursive constant or type definitions. -/
inductive Env.Wf : Env Base TyName ConstName → Prop
  | nil : Env.Wf []
  | constdef {E A rhs c} : Env.Wf E → Ty.Wf E A → HasType E [] rhs A →
      Env.Wf (.constdef c A rhs :: E)
  | typedef {E A p n} : Env.Wf E → Ty.Wf E A → HasType E [A] p .bool →
      Env.Wf (.typedef n A p :: E)

/-- Intrinsic façade over the independent raw environment syntax.  Keeping the
derivation as data makes conversion to proof-carrying clients lossless. -/
structure Intrinsic (E : Env Base TyName ConstName)
    (Γ : Ctx Base TyName) (A : Ty Base TyName) where
  term : Tm Base TyName ConstName
  typing : HasType E Γ term A

/-- A lightweight bounded de Bruijn façade, useful before a typing environment
has been chosen.  Constants and definition names do not consume variable slots. -/
def Tm.FreeBelow : Nat → Tm Base TyName ConstName → Prop
  | n, .var k => k < n
  | _, .const _ => True
  | n, .app f x => f.FreeBelow n ∧ x.FreeBelow n
  | n, .lam _ t => t.FreeBelow (n + 1)
  | _, .bool _ => True
  | n, .eq _ x y => x.FreeBelow n ∧ y.FreeBelow n
  | n, .epsilon _ p => p.FreeBelow n
  | n, .abs _ x => x.FreeBelow n
  | n, .rep _ x => x.FreeBelow n

structure Bounded (Base : Type u) (TyName : Type v) (ConstName : Type w) (n : Nat) where
  term : Tm Base TyName ConstName
  bounded : term.FreeBelow n

def Bounded.erase (t : Bounded Base TyName ConstName n) : Tm Base TyName ConstName := t.term

@[simp] theorem Bounded.erase_mk (t : Tm Base TyName ConstName) (h : t.FreeBelow n) :
    (Bounded.mk t h).erase = t := rfl

/-- A semantic/elaboration environment resolves names to the old raw HOL layer.
Its laws state that it really interprets the stored definition environment. -/
structure Interpretation (E : Env Base TyName ConstName) where
  elabTy : Ty Base TyName → HOL.Ty Base
  elabTm : Tm Base TyName ConstName → HOL.Tm Base
  ty_base : ∀ b, elabTy (.base b) = .base b
  ty_bool : elabTy .bool = .bool
  ty_arr : ∀ A B, elabTy (.arr A B) = .arr (elabTy A) (elabTy B)
  tm_var : ∀ n, elabTm (.var n) = .var n
  tm_app : ∀ f x, elabTm (.app f x) = .app (elabTm f) (elabTm x)
  tm_lam : ∀ A t, elabTm (.lam A t) = .lam (elabTy A) (elabTm t)
  tm_bool : ∀ b, elabTm (.bool b) = .bool b
  tm_eq : ∀ A x y, elabTm (.eq A x y) = .eq (elabTy A) (elabTm x) (elabTm y)
  tm_epsilon : ∀ A p, elabTm (.epsilon A p) = .epsilon (elabTy A) (elabTm p)
  type_def : ∀ {n A p}, HasTypeDef E n A p →
    elabTy (.defined n) = .sub (elabTy A) (elabTm p)
  const_def : ∀ {c A rhs}, HasConstDef E c A rhs → elabTm (.const c) = elabTm rhs
  tm_abs : ∀ {n A p}, HasTypeDef E n A p → ∀ x,
    elabTm (.abs n x) = .abs (elabTy A) (elabTm p) (elabTm x)
  tm_rep : ∀ {n A p}, HasTypeDef E n A p → ∀ x,
    elabTm (.rep n x) = .rep (elabTy A) (elabTm p) (elabTm x)

theorem Interpretation.ty_ofChoice {Base : Type u} {TyName : Type v}
    {ConstName : Type w} {E : Env Base TyName ConstName}
    (I : Interpretation E) (A : Choice.Ty Base) :
    I.elabTy (Ty.ofChoice A) = A.toRaw := by
  induction A with
  | base b => exact I.ty_base b
  | bool => exact I.ty_bool
  | arr A B ihA ihB => rw [Ty.ofChoice, I.ty_arr, ihA, ihB, Choice.Ty.toRaw]

theorem Interpretation.tm_ofChoice {Base : Type u} {TyName : Type v}
    {ConstName : Type w} {E : Env Base TyName ConstName}
    (I : Interpretation E) (t : Choice.Tm Base) :
    I.elabTm (Tm.ofChoice t) = t.toRaw := by
  induction t with
  | var n => exact I.tm_var n
  | app f x ihf ihx => rw [Tm.ofChoice, I.tm_app, ihf, ihx, Choice.Tm.toRaw]
  | lam A t ih => rw [Tm.ofChoice, I.tm_lam, I.ty_ofChoice, ih, Choice.Tm.toRaw]
  | bool b => exact I.tm_bool b
  | eq A x y ihx ihy => rw [Tm.ofChoice, I.tm_eq, I.ty_ofChoice, ihx, ihy, Choice.Tm.toRaw]
  | epsilon A p ih => rw [Tm.ofChoice, I.tm_epsilon, I.ty_ofChoice, ih, Choice.Tm.toRaw]

/-- Extending a definition environment is conservative for every old lookup. -/
theorem HasTypeDef.weaken {E : Env Base TyName ConstName} {n A p d}
    (h : HasTypeDef E n A p) : HasTypeDef (d :: E) n A p := .there h

theorem HasConstDef.weaken {E : Env Base TyName ConstName} {c A t d}
    (h : HasConstDef E c A t) : HasConstDef (d :: E) c A t := .there h

end Defined

end ProjectBeth.HOL.Syntax.Environment
