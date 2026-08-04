import ProjectBeth.Defs.HOLOmega.Syntax.Indexed

/-! Concrete staged HOLω grammars.  The levels are intentionally separate
ASTs; translations into the shared indexed grammar ground their relationship. -/

universe u
namespace ProjectBeth.HOLOmega.Syntax

variable {Base : Type u}

namespace Minimal
inductive Expr (Base : Type u) : Indexed.Category → Type u
  | base : Base → Expr Base .ty | tyVar : Nat → Expr Base .ty
  | tyLam : Kind → Expr Base .ty → Expr Base .ty
  | tyApp : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | boolTy : Expr Base .ty | arr : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | var : Nat → Expr Base .tm | app : Expr Base .tm → Expr Base .tm → Expr Base .tm
  | lam : Expr Base .ty → Expr Base .tm → Expr Base .tm
  | inst : Expr Base .tm → Expr Base .ty → Expr Base .tm
  | gen : Kind → Expr Base .tm → Expr Base .tm
  | bool : Bool → Expr Base .tm
  | eq : Expr Base .ty → Expr Base .tm → Expr Base .tm → Expr Base .tm
abbrev Ty (Base : Type u) := Expr Base .ty
abbrev Tm (Base : Type u) := Expr Base .tm

def toIndexed : {s : Indexed.Category} → Expr Base s → Indexed.Expr Base s
  | _, .base A => .base A | _, .tyVar n => .tyVar n
  | _, .tyLam K A => .tyLam K (toIndexed A)
  | _, .tyApp F A => .tyApp (toIndexed F) (toIndexed A)
  | _, .boolTy => .boolTy | _, .arr A B => .arr (toIndexed A) (toIndexed B)
  | _, .var n => .var n | _, .app f x => .app (toIndexed f) (toIndexed x)
  | _, .lam A t => .lam (toIndexed A) (toIndexed t)
  | _, .inst f A => .inst (toIndexed f) (toIndexed A)
  | _, .gen K t => .gen K (toIndexed t) | _, .bool b => .bool b
  | _, .eq A x y => .eq (toIndexed A) (toIndexed x) (toIndexed y)

def fromIndexed : {s : Indexed.Category} → Indexed.Expr Base s → Option (Expr Base s)
  | _, .base A => pure (.base A) | _, .tyVar n => pure (.tyVar n)
  | _, .tyLam K A => return .tyLam K (← fromIndexed A)
  | _, .tyApp F A => return .tyApp (← fromIndexed F) (← fromIndexed A)
  | _, .boolTy => pure .boolTy | _, .arr A B => return .arr (← fromIndexed A) (← fromIndexed B)
  | _, .sub _ _ => none | _, .var n => pure (.var n)
  | _, .app f x => return .app (← fromIndexed f) (← fromIndexed x)
  | _, .lam A t => return .lam (← fromIndexed A) (← fromIndexed t)
  | _, .inst f A => return .inst (← fromIndexed f) (← fromIndexed A)
  | _, .gen K t => return .gen K (← fromIndexed t) | _, .bool b => pure (.bool b)
  | _, .eq A x y => return .eq (← fromIndexed A) (← fromIndexed x) (← fromIndexed y)
  | _, .epsilon _ _ | _, .abs _ _ _ | _, .rep _ _ _ => none

@[simp] theorem fromIndexed_toIndexed (e : Expr Base s) : fromIndexed (toIndexed e) = some e := by
  induction e <;> simp [toIndexed, fromIndexed, *]

theorem toIndexed_injective : Function.Injective (@toIndexed Base s) := by
  intro a b h
  have := congrArg fromIndexed h
  simpa using this
end Minimal

namespace Choice
inductive Expr (Base : Type u) : Indexed.Category → Type u
  | base : Base → Expr Base .ty | tyVar : Nat → Expr Base .ty
  | tyLam : Kind → Expr Base .ty → Expr Base .ty
  | tyApp : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | boolTy : Expr Base .ty | arr : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | var : Nat → Expr Base .tm | app : Expr Base .tm → Expr Base .tm → Expr Base .tm
  | lam : Expr Base .ty → Expr Base .tm → Expr Base .tm
  | inst : Expr Base .tm → Expr Base .ty → Expr Base .tm
  | gen : Kind → Expr Base .tm → Expr Base .tm
  | bool : Bool → Expr Base .tm
  | eq : Expr Base .ty → Expr Base .tm → Expr Base .tm → Expr Base .tm
  | epsilon : Expr Base .ty → Expr Base .tm → Expr Base .tm
abbrev Ty (Base : Type u) := Expr Base .ty
abbrev Tm (Base : Type u) := Expr Base .tm

def ofMinimal : {s : Indexed.Category} → Minimal.Expr Base s → Expr Base s
  | _, .base A => .base A | _, .tyVar n => .tyVar n
  | _, .tyLam K A => .tyLam K (ofMinimal A)
  | _, .tyApp F A => .tyApp (ofMinimal F) (ofMinimal A)
  | _, .boolTy => .boolTy | _, .arr A B => .arr (ofMinimal A) (ofMinimal B)
  | _, .var n => .var n | _, .app f x => .app (ofMinimal f) (ofMinimal x)
  | _, .lam A t => .lam (ofMinimal A) (ofMinimal t)
  | _, .inst f A => .inst (ofMinimal f) (ofMinimal A)
  | _, .gen K t => .gen K (ofMinimal t) | _, .bool b => .bool b
  | _, .eq A x y => .eq (ofMinimal A) (ofMinimal x) (ofMinimal y)

def toIndexed : {s : Indexed.Category} → Expr Base s → Indexed.Expr Base s
  | _, .base A => .base A | _, .tyVar n => .tyVar n
  | _, .tyLam K A => .tyLam K (toIndexed A)
  | _, .tyApp F A => .tyApp (toIndexed F) (toIndexed A)
  | _, .boolTy => .boolTy | _, .arr A B => .arr (toIndexed A) (toIndexed B)
  | _, .var n => .var n | _, .app f x => .app (toIndexed f) (toIndexed x)
  | _, .lam A t => .lam (toIndexed A) (toIndexed t)
  | _, .inst f A => .inst (toIndexed f) (toIndexed A)
  | _, .gen K t => .gen K (toIndexed t) | _, .bool b => .bool b
  | _, .eq A x y => .eq (toIndexed A) (toIndexed x) (toIndexed y)
  | _, .epsilon A p => .epsilon (toIndexed A) (toIndexed p)

def fromIndexed : {s : Indexed.Category} → Indexed.Expr Base s → Option (Expr Base s)
  | _, .base A => pure (.base A) | _, .tyVar n => pure (.tyVar n)
  | _, .tyLam K A => return .tyLam K (← fromIndexed A)
  | _, .tyApp F A => return .tyApp (← fromIndexed F) (← fromIndexed A)
  | _, .boolTy => pure .boolTy | _, .arr A B => return .arr (← fromIndexed A) (← fromIndexed B)
  | _, .sub _ _ => none | _, .var n => pure (.var n)
  | _, .app f x => return .app (← fromIndexed f) (← fromIndexed x)
  | _, .lam A t => return .lam (← fromIndexed A) (← fromIndexed t)
  | _, .inst f A => return .inst (← fromIndexed f) (← fromIndexed A)
  | _, .gen K t => return .gen K (← fromIndexed t) | _, .bool b => pure (.bool b)
  | _, .eq A x y => return .eq (← fromIndexed A) (← fromIndexed x) (← fromIndexed y)
  | _, .epsilon A p => return .epsilon (← fromIndexed A) (← fromIndexed p)
  | _, .abs _ _ _ | _, .rep _ _ _ => none

@[simp] theorem fromIndexed_toIndexed (e : Expr Base s) : fromIndexed (toIndexed e) = some e := by
  induction e <;> simp [toIndexed, fromIndexed, *]

theorem toIndexed_injective : Function.Injective (@toIndexed Base s) := by
  intro a b h
  have := congrArg fromIndexed h
  simpa using this

@[simp] theorem toIndexed_ofMinimal (e : Minimal.Expr Base s) :
    toIndexed (ofMinimal e) = Minimal.toIndexed e := by
  induction e <;> simp [ofMinimal, toIndexed, Minimal.toIndexed, *]

theorem ofMinimal_injective : Function.Injective (@ofMinimal Base s) := by
  intro a b h
  have := congrArg toIndexed h
  exact Minimal.toIndexed_injective (by simpa using this)
end Choice

namespace Full
inductive Expr (Base : Type u) : Indexed.Category → Type u
  | base : Base → Expr Base .ty | tyVar : Nat → Expr Base .ty
  | tyLam : Kind → Expr Base .ty → Expr Base .ty
  | tyApp : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | boolTy : Expr Base .ty | arr : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | sub : Expr Base .ty → Expr Base .tm → Expr Base .ty
  | var : Nat → Expr Base .tm | app : Expr Base .tm → Expr Base .tm → Expr Base .tm
  | lam : Expr Base .ty → Expr Base .tm → Expr Base .tm
  | inst : Expr Base .tm → Expr Base .ty → Expr Base .tm
  | gen : Kind → Expr Base .tm → Expr Base .tm
  | bool : Bool → Expr Base .tm
  | eq : Expr Base .ty → Expr Base .tm → Expr Base .tm → Expr Base .tm
  | epsilon : Expr Base .ty → Expr Base .tm → Expr Base .tm
  | abs : Expr Base .ty → Expr Base .tm → Expr Base .tm → Expr Base .tm
  | rep : Expr Base .ty → Expr Base .tm → Expr Base .tm → Expr Base .tm
abbrev Ty (Base : Type u) := Expr Base .ty
abbrev Tm (Base : Type u) := Expr Base .tm

def ofChoice : {s : Indexed.Category} → Choice.Expr Base s → Expr Base s
  | _, .base A => .base A | _, .tyVar n => .tyVar n
  | _, .tyLam K A => .tyLam K (ofChoice A)
  | _, .tyApp F A => .tyApp (ofChoice F) (ofChoice A)
  | _, .boolTy => .boolTy | _, .arr A B => .arr (ofChoice A) (ofChoice B)
  | _, .var n => .var n | _, .app f x => .app (ofChoice f) (ofChoice x)
  | _, .lam A t => .lam (ofChoice A) (ofChoice t)
  | _, .inst f A => .inst (ofChoice f) (ofChoice A)
  | _, .gen K t => .gen K (ofChoice t) | _, .bool b => .bool b
  | _, .eq A x y => .eq (ofChoice A) (ofChoice x) (ofChoice y)
  | _, .epsilon A p => .epsilon (ofChoice A) (ofChoice p)

def toIndexed : {s : Indexed.Category} → Expr Base s → Indexed.Expr Base s
  | _, .base A => .base A | _, .tyVar n => .tyVar n
  | _, .tyLam K A => .tyLam K (toIndexed A)
  | _, .tyApp F A => .tyApp (toIndexed F) (toIndexed A)
  | _, .boolTy => .boolTy | _, .arr A B => .arr (toIndexed A) (toIndexed B)
  | _, .sub A p => .sub (toIndexed A) (toIndexed p)
  | _, .var n => .var n | _, .app f x => .app (toIndexed f) (toIndexed x)
  | _, .lam A t => .lam (toIndexed A) (toIndexed t)
  | _, .inst f A => .inst (toIndexed f) (toIndexed A)
  | _, .gen K t => .gen K (toIndexed t) | _, .bool b => .bool b
  | _, .eq A x y => .eq (toIndexed A) (toIndexed x) (toIndexed y)
  | _, .epsilon A p => .epsilon (toIndexed A) (toIndexed p)
  | _, .abs A p x => .abs (toIndexed A) (toIndexed p) (toIndexed x)
  | _, .rep A p x => .rep (toIndexed A) (toIndexed p) (toIndexed x)

def ofIndexed : {s : Indexed.Category} → Indexed.Expr Base s → Expr Base s
  | _, .base A => .base A | _, .tyVar n => .tyVar n
  | _, .tyLam K A => .tyLam K (ofIndexed A)
  | _, .tyApp F A => .tyApp (ofIndexed F) (ofIndexed A)
  | _, .boolTy => .boolTy | _, .arr A B => .arr (ofIndexed A) (ofIndexed B)
  | _, .sub A p => .sub (ofIndexed A) (ofIndexed p)
  | _, .var n => .var n | _, .app f x => .app (ofIndexed f) (ofIndexed x)
  | _, .lam A t => .lam (ofIndexed A) (ofIndexed t)
  | _, .inst f A => .inst (ofIndexed f) (ofIndexed A)
  | _, .gen K t => .gen K (ofIndexed t) | _, .bool b => .bool b
  | _, .eq A x y => .eq (ofIndexed A) (ofIndexed x) (ofIndexed y)
  | _, .epsilon A p => .epsilon (ofIndexed A) (ofIndexed p)
  | _, .abs A p x => .abs (ofIndexed A) (ofIndexed p) (ofIndexed x)
  | _, .rep A p x => .rep (ofIndexed A) (ofIndexed p) (ofIndexed x)

@[simp] theorem ofIndexed_toIndexed (e : Expr Base s) : ofIndexed (toIndexed e) = e := by
  induction e <;> simp [toIndexed, ofIndexed, *]
@[simp] theorem toIndexed_ofIndexed (e : Indexed.Expr Base s) : toIndexed (ofIndexed e) = e := by
  induction e <;> simp [toIndexed, ofIndexed, *]
def indexedEquiv (s : Indexed.Category) : Equiv (Expr Base s) (Indexed.Expr Base s) where
  toFun := toIndexed
  invFun := ofIndexed
  left_inv := ofIndexed_toIndexed
  right_inv := toIndexed_ofIndexed

@[simp] theorem toIndexed_ofChoice (e : Choice.Expr Base s) :
    toIndexed (ofChoice e) = Choice.toIndexed e := by
  induction e <;> simp [toIndexed, ofChoice, Choice.toIndexed, *]

@[simp] theorem ofChoice_ofMinimal (e : Minimal.Expr Base s) :
    ofChoice (Choice.ofMinimal e) = ofIndexed (Minimal.toIndexed e) := by
  induction e <;> simp [ofChoice, Choice.ofMinimal, ofIndexed, Minimal.toIndexed, *]
theorem ofChoice_injective : Function.Injective (@ofChoice Base s) := by
  intro a b h
  apply Choice.toIndexed_injective
  have := congrArg toIndexed h
  simpa using this
end Full

/-- Definition environments decide whether constructors outside a target
fragment have an expansion.  This is the precise extra data needed to lower
rather than merely reject richer trees. -/
structure LoweringEnvironment (Base : Type u) where
  epsilon : Choice.Ty Base → Choice.Tm Base → Minimal.Tm Base
  subtype : Full.Ty Base → Full.Tm Base → Choice.Ty Base
  abs : Full.Ty Base → Full.Tm Base → Full.Tm Base → Choice.Tm Base
  rep : Full.Ty Base → Full.Tm Base → Full.Tm Base → Choice.Tm Base

def Choice.lower (E : LoweringEnvironment Base) :
    {s : Indexed.Category} → Choice.Expr Base s → Minimal.Expr Base s
  | _, .base A => .base A | _, .tyVar n => .tyVar n
  | _, .tyLam K A => .tyLam K (lower E A)
  | _, .tyApp F A => .tyApp (lower E F) (lower E A)
  | _, .boolTy => .boolTy | _, .arr A B => .arr (lower E A) (lower E B)
  | _, .var n => .var n | _, .app f x => .app (lower E f) (lower E x)
  | _, .lam A t => .lam (lower E A) (lower E t)
  | _, .inst f A => .inst (lower E f) (lower E A)
  | _, .gen K t => .gen K (lower E t) | _, .bool b => .bool b
  | _, .eq A x y => .eq (lower E A) (lower E x) (lower E y)
  | _, .epsilon A p => E.epsilon A p

@[simp] theorem Choice.lower_ofMinimal (E : LoweringEnvironment Base)
    (e : Minimal.Expr Base s) : Choice.lower E (Choice.ofMinimal e) = e := by
  induction e <;> simp [Choice.lower, Choice.ofMinimal, *]

def Full.lower (E : LoweringEnvironment Base) :
    {s : Indexed.Category} → Full.Expr Base s → Choice.Expr Base s
  | _, .base A => .base A | _, .tyVar n => .tyVar n
  | _, .tyLam K A => .tyLam K (lower E A)
  | _, .tyApp F A => .tyApp (lower E F) (lower E A)
  | _, .boolTy => .boolTy | _, .arr A B => .arr (lower E A) (lower E B)
  | _, .sub A p => E.subtype A p
  | _, .var n => .var n | _, .app f x => .app (lower E f) (lower E x)
  | _, .lam A t => .lam (lower E A) (lower E t)
  | _, .inst f A => .inst (lower E f) (lower E A)
  | _, .gen K t => .gen K (lower E t) | _, .bool b => .bool b
  | _, .eq A x y => .eq (lower E A) (lower E x) (lower E y)
  | _, .epsilon A p => .epsilon (lower E A) (lower E p)
  | _, .abs A p x => E.abs A p x
  | _, .rep A p x => E.rep A p x

@[simp] theorem Full.lower_ofChoice (E : LoweringEnvironment Base)
    (e : Choice.Expr Base s) : Full.lower E (Full.ofChoice e) = e := by
  induction e <;> simp [Full.lower, Full.ofChoice, *]

end ProjectBeth.HOLOmega.Syntax
