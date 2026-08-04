import ProjectBeth.Defs.HOL.Syntax.Environment
import ProjectBeth.Defs.HOLOmega.Syntax.HOLBridge

/-! Constructor-for-constructor inclusions of the concrete HOL fragments. -/

universe u
namespace ProjectBeth.HOLOmega.Syntax.HOLLevelsBridge
variable {Base : Type u}

namespace Minimal
def ty : ProjectBeth.HOL.Syntax.Environment.Minimal.Ty Base → HOLOmega.Syntax.Minimal.Ty Base
  | .base b => .base b | .bool => .boolTy | .arr A B => .arr (ty A) (ty B)

def tm : ProjectBeth.HOL.Syntax.Environment.Minimal.Tm Base → HOLOmega.Syntax.Minimal.Tm Base
  | .var n => .var n | .app f x => .app (tm f) (tm x)
  | .lam A t => .lam (ty A) (tm t) | .bool b => .bool b
  | .eq A x y => .eq (ty A) (tm x) (tm y)

@[simp] theorem ty_square (A : ProjectBeth.HOL.Syntax.Environment.Minimal.Ty Base) :
    (HOLOmega.Syntax.Minimal.toIndexed (ty A)).toLegacy =
      Translations.HOLToOmega.ty A.toRaw := by
  induction A <;> simp [ty, HOLOmega.Syntax.Minimal.toIndexed,
    Indexed.Expr.toLegacy,
    ProjectBeth.HOL.Syntax.Environment.Minimal.Ty.toRaw, *]

@[simp] theorem tm_square (t : ProjectBeth.HOL.Syntax.Environment.Minimal.Tm Base) :
    (HOLOmega.Syntax.Minimal.toIndexed (tm t)).toLegacy =
      Translations.HOLToOmega.tm t.toRaw := by
  induction t <;> simp [tm, HOLOmega.Syntax.Minimal.toIndexed,
    Indexed.Expr.toLegacy,
    ProjectBeth.HOL.Syntax.Environment.Minimal.Tm.toRaw,
    Translations.HOLToOmega.tm, *]
end Minimal

namespace Choice
def ty : ProjectBeth.HOL.Syntax.Environment.Choice.Ty Base → HOLOmega.Syntax.Choice.Ty Base
  | .base b => .base b | .bool => .boolTy | .arr A B => .arr (ty A) (ty B)

def tm : ProjectBeth.HOL.Syntax.Environment.Choice.Tm Base → HOLOmega.Syntax.Choice.Tm Base
  | .var n => .var n | .app f x => .app (tm f) (tm x)
  | .lam A t => .lam (ty A) (tm t) | .bool b => .bool b
  | .eq A x y => .eq (ty A) (tm x) (tm y)
  | .epsilon A p => .epsilon (ty A) (tm p)

@[simp] theorem ty_ofMinimal (A : ProjectBeth.HOL.Syntax.Environment.Minimal.Ty Base) :
    ty (ProjectBeth.HOL.Syntax.Environment.Choice.Ty.ofMinimal A) =
      HOLOmega.Syntax.Choice.ofMinimal (Minimal.ty A) := by
  induction A <;> simp [ty, Minimal.ty,
    ProjectBeth.HOL.Syntax.Environment.Choice.Ty.ofMinimal,
    HOLOmega.Syntax.Choice.ofMinimal, *]

@[simp] theorem tm_ofMinimal (t : ProjectBeth.HOL.Syntax.Environment.Minimal.Tm Base) :
    tm (ProjectBeth.HOL.Syntax.Environment.Choice.Tm.ofMinimal t) =
      HOLOmega.Syntax.Choice.ofMinimal (Minimal.tm t) := by
  induction t <;> simp [tm, Minimal.tm,
    ProjectBeth.HOL.Syntax.Environment.Choice.Tm.ofMinimal,
    HOLOmega.Syntax.Choice.ofMinimal, ty_ofMinimal, *]

@[simp] theorem ty_square (A : ProjectBeth.HOL.Syntax.Environment.Choice.Ty Base) :
    (HOLOmega.Syntax.Choice.toIndexed (ty A)).toLegacy =
      Translations.HOLToOmega.ty A.toRaw := by
  induction A <;> simp [ty, HOLOmega.Syntax.Choice.toIndexed,
    Indexed.Expr.toLegacy,
    ProjectBeth.HOL.Syntax.Environment.Choice.Ty.toRaw, *]

@[simp] theorem tm_square (t : ProjectBeth.HOL.Syntax.Environment.Choice.Tm Base) :
    (HOLOmega.Syntax.Choice.toIndexed (tm t)).toLegacy =
      Translations.HOLToOmega.tm t.toRaw := by
  induction t <;> simp [tm, HOLOmega.Syntax.Choice.toIndexed,
    Indexed.Expr.toLegacy,
    ProjectBeth.HOL.Syntax.Environment.Choice.Tm.toRaw,
    Translations.HOLToOmega.tm, *]
end Choice

end ProjectBeth.HOLOmega.Syntax.HOLLevelsBridge
