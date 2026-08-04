import ProjectBeth.Defs.HOLOmega.Syntax.Levels

/-! Traditional sequential HOLω definitions, kept distinct from pure trees. -/

universe u v w
namespace ProjectBeth.HOLOmega.Syntax.Environment

variable {Base : Type u} {TyName : Type v} {ConstName : Type w}

inductive Ty (Base : Type u) (TyName : Type v) : Type (max u v)
  | base : Base → Ty Base TyName | var : Nat → Ty Base TyName
  | lam : Kind → Ty Base TyName → Ty Base TyName
  | app : Ty Base TyName → Ty Base TyName → Ty Base TyName
  | bool : Ty Base TyName | arr : Ty Base TyName → Ty Base TyName → Ty Base TyName
  | defined : TyName → Ty Base TyName

inductive Tm (Base : Type u) (TyName : Type v) (ConstName : Type w) : Type (max u v w)
  | var : Nat → Tm Base TyName ConstName | const : ConstName → Tm Base TyName ConstName
  | app : Tm Base TyName ConstName → Tm Base TyName ConstName → Tm Base TyName ConstName
  | lam : Ty Base TyName → Tm Base TyName ConstName → Tm Base TyName ConstName
  | tyApp : Tm Base TyName ConstName → Ty Base TyName → Tm Base TyName ConstName
  | tyLam : Kind → Tm Base TyName ConstName → Tm Base TyName ConstName
  | bool : Bool → Tm Base TyName ConstName
  | eq : Ty Base TyName → Tm Base TyName ConstName → Tm Base TyName ConstName →
      Tm Base TyName ConstName
  | epsilon : Ty Base TyName → Tm Base TyName ConstName → Tm Base TyName ConstName
  | abs : TyName → Tm Base TyName ConstName → Tm Base TyName ConstName
  | rep : TyName → Tm Base TyName ConstName → Tm Base TyName ConstName

inductive Decl (Base : Type u) (TyName : Type v) (ConstName : Type w)
  | constdef (name : ConstName) (type : Ty Base TyName) (rhs : Tm Base TyName ConstName)
  | typedef (name : TyName) (rep : Ty Base TyName) (predicate : Tm Base TyName ConstName)
  | typeop (name : TyName) (kind : Kind) (rhs : Ty Base TyName)

abbrev Env (Base : Type u) (TyName : Type v) (ConstName : Type w) :=
  List (Decl Base TyName ConstName)

inductive HasTypeDef : Env Base TyName ConstName → TyName → Ty Base TyName →
    Tm Base TyName ConstName → Prop
  | here {n A p E} : HasTypeDef (.typedef n A p :: E) n A p
  | there {E n A p d} : HasTypeDef E n A p → HasTypeDef (d :: E) n A p

inductive HasTypeOp : Env Base TyName ConstName → TyName → Kind → Ty Base TyName → Prop
  | here {n K A E} : HasTypeOp (.typeop n K A :: E) n K A
  | there {E n K A d} : HasTypeOp E n K A → HasTypeOp (d :: E) n K A

inductive HasConstDef : Env Base TyName ConstName → ConstName → Ty Base TyName →
    Tm Base TyName ConstName → Prop
  | here {c A t E} : HasConstDef (.constdef c A t :: E) c A t
  | there {E c A t d} : HasConstDef E c A t → HasConstDef (d :: E) c A t

/-- Resolving names is exactly the environment-dependent downward map. -/
structure Interpretation (E : Env Base TyName ConstName) where
  ty : Ty Base TyName → Indexed.Ty Base
  tm : Tm Base TyName ConstName → Indexed.Tm Base
  ty_base : ∀ b, ty (.base b) = .base b
  ty_var : ∀ n, ty (.var n) = .tyVar n
  ty_lam : ∀ K A, ty (.lam K A) = .tyLam K (ty A)
  ty_app : ∀ F A, ty (.app F A) = .tyApp (ty F) (ty A)
  ty_bool : ty .bool = .boolTy
  ty_arr : ∀ A B, ty (.arr A B) = .arr (ty A) (ty B)
  tm_var : ∀ n, tm (.var n) = .var n
  tm_app : ∀ f x, tm (.app f x) = .app (tm f) (tm x)
  tm_lam : ∀ A t, tm (.lam A t) = .lam (ty A) (tm t)
  tm_tyApp : ∀ f A, tm (.tyApp f A) = .inst (tm f) (ty A)
  tm_tyLam : ∀ K t, tm (.tyLam K t) = .gen K (tm t)
  tm_bool : ∀ b, tm (.bool b) = .bool b
  tm_eq : ∀ A x y, tm (.eq A x y) = .eq (ty A) (tm x) (tm y)
  tm_epsilon : ∀ A p, tm (.epsilon A p) = .epsilon (ty A) (tm p)
  typedef : ∀ {n A p}, HasTypeDef E n A p → ty (.defined n) = .sub (ty A) (tm p)
  typeop : ∀ {n K A}, HasTypeOp E n K A → ty (.defined n) = ty A
  constdef : ∀ {c A t}, HasConstDef E c A t → tm (.const c) = tm t
  tm_abs : ∀ {n A p}, HasTypeDef E n A p → ∀ x,
    tm (.abs n x) = .abs (ty A) (tm p) (tm x)
  tm_rep : ∀ {n A p}, HasTypeDef E n A p → ∀ x,
    tm (.rep n x) = .rep (ty A) (tm p) (tm x)

/-- A declaration is accepted only when its elaboration is a genuine legacy
HOLω derivation. -/
inductive Valid {Base : Type u} {TyName : Type v} {ConstName : Type w}
    {E : Env Base TyName ConstName} (I : Interpretation E) :
    Decl Base TyName ConstName → Prop
  | constdef {A : Ty Base TyName} {rhs : Tm Base TyName ConstName} {c : ConstName} :
      HOLOmega.Kinded [] (I.ty A).toLegacy .star →
      HOLOmega.HasType [] [] (I.tm rhs).toLegacy (I.ty A).toLegacy →
      Valid I (.constdef c A rhs)
  | typedef {A : Ty Base TyName} {p : Tm Base TyName ConstName} {n : TyName} :
      HOLOmega.Kinded [] (I.ty A).toLegacy .star →
      HOLOmega.HasType [] [(I.ty A).toLegacy] (I.tm p).toLegacy .bool →
      Valid I (.typedef n A p)
  | typeop {A : Ty Base TyName} {K : Kind} {n : TyName} :
      HOLOmega.Kinded [] (I.ty A).toLegacy K → Valid I (.typeop n K A)

/-- Each new declaration is checked in, and interpreted by, the strictly older
tail.  The interpretation for the extended environment is stored for the next
step, matching actual HOL implementations. -/
inductive Checked {Base : Type u} {TyName : Type v} {ConstName : Type w} :
    Env Base TyName ConstName → Type (max u v w)
  | nil (I : Interpretation ([] : Env Base TyName ConstName)) : Checked []
  | cons {E d} : Checked E → (old : Interpretation E) → Valid old d →
      Interpretation (d :: E) → Checked (d :: E)

theorem Checked.head_valid : Checked (d :: E) →
    ∃ (I : Interpretation E), Valid I d
  | .cons _ I h _ => ⟨I, h⟩

end ProjectBeth.HOLOmega.Syntax.Environment
