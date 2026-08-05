import ProjectBeth.Defs.HOL.Syntax.Environment
import ProjectBeth.Defs.HOLOmega.Syntax.Environment
import ProjectBeth.Defs.Translations

/-! The traditional HOL environment embeds into the HOLω environment and the
name-resolution square is recorded explicitly. -/

universe u v w
namespace ProjectBeth.HOLOmega.Syntax.EnvironmentBridge
variable {Base : Type u} {TyName : Type v} {ConstName : Type w}

def ty : ProjectBeth.HOL.Syntax.Environment.Defined.Ty Base TyName →
    ProjectBeth.HOLOmega.Syntax.Environment.Ty Base TyName
  | .base b => .base b | .bool => .bool
  | .arr A B => .arr (ty A) (ty B) | .defined n => .defined n

def tm : ProjectBeth.HOL.Syntax.Environment.Defined.Tm Base TyName ConstName →
    ProjectBeth.HOLOmega.Syntax.Environment.Tm Base TyName ConstName
  | .var n => .var n | .const c => .const c
  | .app f x => .app (tm f) (tm x) | .lam A t => .lam (ty A) (tm t)
  | .bool b => .bool b | .eq A x y => .eq (ty A) (tm x) (tm y)
  | .epsilon A p => .epsilon (ty A) (tm p)
  | .abs n x => .abs n (tm x) | .rep n x => .rep n (tm x)

def decl : ProjectBeth.HOL.Syntax.Environment.Defined.Decl Base TyName ConstName →
    ProjectBeth.HOLOmega.Syntax.Environment.Decl Base TyName ConstName
  | .constdef c A t => .constdef c (ty A) (tm t)
  | .typedef n A p => .typedef n (ty A) (tm p)

def env (E : ProjectBeth.HOL.Syntax.Environment.Defined.Env Base TyName ConstName) :
    ProjectBeth.HOLOmega.Syntax.Environment.Env Base TyName ConstName := E.map decl

theorem typeDef
    (h : ProjectBeth.HOL.Syntax.Environment.Defined.HasTypeDef E n A p) :
    ProjectBeth.HOLOmega.Syntax.Environment.HasTypeDef (env E) n (ty A) (tm p) := by
  induction h with
  | here => exact .here
  | there h ih => exact .there ih

theorem constDef
    (h : ProjectBeth.HOL.Syntax.Environment.Defined.HasConstDef E c A t) :
    ProjectBeth.HOLOmega.Syntax.Environment.HasConstDef (env E) c (ty A) (tm t) := by
  induction h with
  | here => exact .here
  | there h ih => exact .there ih

/-- Resolving a monomorphic name before or after inclusion gives the same
legacy HOLω tree. -/
structure Commutes
    {E : ProjectBeth.HOL.Syntax.Environment.Defined.Env Base TyName ConstName}
    (HI : ProjectBeth.HOL.Syntax.Environment.Defined.Interpretation E)
    (OI : ProjectBeth.HOLOmega.Syntax.Environment.Interpretation (env E)) : Prop where
  ty_square : ∀ A,
    (OI.ty (ty A)).toLegacy = Translations.HOLToOmega.ty (HI.elabTy A)
  tm_square : ∀ t,
    (OI.tm (tm t)).toLegacy = Translations.HOLToOmega.tm (HI.elabTm t)

theorem Commutes.typedef_square
    {E : ProjectBeth.HOL.Syntax.Environment.Defined.Env Base TyName ConstName}
    {HI : ProjectBeth.HOL.Syntax.Environment.Defined.Interpretation E}
    {OI : ProjectBeth.HOLOmega.Syntax.Environment.Interpretation (env E)}
    (C : Commutes HI OI)
    (h : ProjectBeth.HOL.Syntax.Environment.Defined.HasTypeDef E n A p) :
    (OI.ty (.defined n)).toLegacy =
      HOLOmega.Ty.sub (Translations.HOLToOmega.ty (HI.elabTy A))
        (Translations.HOLToOmega.tm (HI.elabTm p)) := by
  rw [OI.typedef (typeDef h), Indexed.Expr.toLegacy]
  simp only [C.ty_square, C.tm_square]

theorem Commutes.constdef_square
    {E : ProjectBeth.HOL.Syntax.Environment.Defined.Env Base TyName ConstName}
    {HI : ProjectBeth.HOL.Syntax.Environment.Defined.Interpretation E}
    {OI : ProjectBeth.HOLOmega.Syntax.Environment.Interpretation (env E)}
    (C : Commutes HI OI)
    (h : ProjectBeth.HOL.Syntax.Environment.Defined.HasConstDef E c A t) :
    (OI.tm (.const c)).toLegacy = Translations.HOLToOmega.tm (HI.elabTm t) := by
  rw [OI.constdef (constDef h), C.tm_square]

end ProjectBeth.HOLOmega.Syntax.EnvironmentBridge
