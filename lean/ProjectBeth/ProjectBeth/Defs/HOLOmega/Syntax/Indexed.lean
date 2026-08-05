import ProjectBeth.Basic
import ProjectBeth.Defs.HOLOmega.Substitution

/-! A single indexed inductive for the mutually recursive raw HOLω grammar. -/

universe u

namespace ProjectBeth.HOLOmega.Syntax.Indexed

variable {Base : Type u}

inductive Category where | ty | tm

/-- Unlike the historical `HOLOmega.Ty`/`Tm`, this is one inductive family and
therefore has one ordinary recursor and induction principle. -/
inductive Expr (Base : Type u) : Category → Type u
  | base : Base → Expr Base .ty
  | tyVar : Nat → Expr Base .ty
  | tyLam : Kind → Expr Base .ty → Expr Base .ty
  | tyApp : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | boolTy : Expr Base .ty
  | arr : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | sub : Expr Base .ty → Expr Base .tm → Expr Base .ty
  | var : Nat → Expr Base .tm
  | app : Expr Base .tm → Expr Base .tm → Expr Base .tm
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

def Expr.toLegacy : {s : Category} → Expr Base s →
    match s with | .ty => HOLOmega.Ty Base | .tm => HOLOmega.Tm Base
  | _, .base A => .base A
  | _, .tyVar n => .var n
  | _, .tyLam K A => .lam K A.toLegacy
  | _, .tyApp F A => .app F.toLegacy A.toLegacy
  | _, .boolTy => .bool
  | _, .arr A B => .arr A.toLegacy B.toLegacy
  | _, .sub A p => .sub A.toLegacy p.toLegacy
  | _, .var n => .var n
  | _, .app f x => .app f.toLegacy x.toLegacy
  | _, .lam A t => .lam A.toLegacy t.toLegacy
  | _, .inst f A => .tyApp f.toLegacy A.toLegacy
  | _, .gen K t => .tyLam K t.toLegacy
  | _, .bool b => .bool b
  | _, .eq A x y => .eq A.toLegacy x.toLegacy y.toLegacy
  | _, .epsilon A p => .epsilon A.toLegacy p.toLegacy
  | _, .abs A p x => .abs A.toLegacy p.toLegacy x.toLegacy
  | _, .rep A p x => .rep A.toLegacy p.toLegacy x.toLegacy

mutual
  def ofLegacyTy : HOLOmega.Ty Base → Ty Base
    | .base A => .base A
    | .var n => .tyVar n
    | .lam K A => .tyLam K (ofLegacyTy A)
    | .app F A => .tyApp (ofLegacyTy F) (ofLegacyTy A)
    | .bool => .boolTy
    | .arr A B => .arr (ofLegacyTy A) (ofLegacyTy B)
    | .sub A p => .sub (ofLegacyTy A) (ofLegacyTm p)
  def ofLegacyTm : HOLOmega.Tm Base → Tm Base
    | .var n => .var n
    | .app f x => .app (ofLegacyTm f) (ofLegacyTm x)
    | .lam A t => .lam (ofLegacyTy A) (ofLegacyTm t)
    | .tyApp f A => .inst (ofLegacyTm f) (ofLegacyTy A)
    | .tyLam K t => .gen K (ofLegacyTm t)
    | .bool b => .bool b
    | .eq A x y => .eq (ofLegacyTy A) (ofLegacyTm x) (ofLegacyTm y)
    | .epsilon A p => .epsilon (ofLegacyTy A) (ofLegacyTm p)
    | .abs A p x => .abs (ofLegacyTy A) (ofLegacyTm p) (ofLegacyTm x)
    | .rep A p x => .rep (ofLegacyTy A) (ofLegacyTm p) (ofLegacyTm x)
end

mutual
  @[simp] theorem toLegacy_ofLegacyTy : (A : HOLOmega.Ty Base) →
      (ofLegacyTy A).toLegacy = A
    | .base _ | .var _ | .bool => rfl
    | .lam _ A => by simp [ofLegacyTy, Expr.toLegacy, toLegacy_ofLegacyTy A]
    | .app F A | .arr F A => by
        simp [ofLegacyTy, Expr.toLegacy, toLegacy_ofLegacyTy F, toLegacy_ofLegacyTy A]
    | .sub A p => by
        simp [ofLegacyTy, Expr.toLegacy, toLegacy_ofLegacyTy A, toLegacy_ofLegacyTm p]
  @[simp] theorem toLegacy_ofLegacyTm : (t : HOLOmega.Tm Base) →
      (ofLegacyTm t).toLegacy = t
    | .var _ | .bool _ => rfl
    | .app f x => by
        simp [ofLegacyTm, Expr.toLegacy, toLegacy_ofLegacyTm f, toLegacy_ofLegacyTm x]
    | .lam A t => by
        simp [ofLegacyTm, Expr.toLegacy, toLegacy_ofLegacyTy A, toLegacy_ofLegacyTm t]
    | .tyApp f A => by
        simp [ofLegacyTm, Expr.toLegacy, toLegacy_ofLegacyTm f, toLegacy_ofLegacyTy A]
    | .tyLam _ t => by simp [ofLegacyTm, Expr.toLegacy, toLegacy_ofLegacyTm t]
    | .eq A x y => by simp [ofLegacyTm, Expr.toLegacy, toLegacy_ofLegacyTy A,
        toLegacy_ofLegacyTm x, toLegacy_ofLegacyTm y]
    | .epsilon A p => by
        simp [ofLegacyTm, Expr.toLegacy, toLegacy_ofLegacyTy A, toLegacy_ofLegacyTm p]
    | .abs A p x | .rep A p x => by
        simp [ofLegacyTm, Expr.toLegacy, toLegacy_ofLegacyTy A,
          toLegacy_ofLegacyTm p, toLegacy_ofLegacyTm x]
end

@[simp] theorem ofLegacy_toLegacy : {s : Category} → (e : Expr Base s) →
    (match s with
      | .ty => ofLegacyTy e.toLegacy
      | .tm => ofLegacyTm e.toLegacy) = e
  | _, .base _ | _, .tyVar _ | _, .boolTy | _, .var _ | _, .bool _ => rfl
  | _, .tyLam K A => by
      change Expr.tyLam K (ofLegacyTy A.toLegacy) = _
      congr; exact ofLegacy_toLegacy (s := .ty) A
  | _, .tyApp F A => by
      change Expr.tyApp (ofLegacyTy F.toLegacy) (ofLegacyTy A.toLegacy) = _
      congr <;> exact ofLegacy_toLegacy (s := .ty) _
  | _, .arr A B => by
      change Expr.arr (ofLegacyTy A.toLegacy) (ofLegacyTy B.toLegacy) = _
      congr <;> exact ofLegacy_toLegacy (s := .ty) _
  | _, .sub A p => by
      change Expr.sub (ofLegacyTy A.toLegacy) (ofLegacyTm p.toLegacy) = _
      congr <;> first | exact ofLegacy_toLegacy (s := .ty) _ | exact ofLegacy_toLegacy (s := .tm) _
  | _, .app f x => by
      change Expr.app (ofLegacyTm f.toLegacy) (ofLegacyTm x.toLegacy) = _
      congr <;> first | exact ofLegacy_toLegacy (s := .ty) _ | exact ofLegacy_toLegacy (s := .tm) _
  | _, .lam A t => by
      change Expr.lam (ofLegacyTy A.toLegacy) (ofLegacyTm t.toLegacy) = _
      congr <;> first | exact ofLegacy_toLegacy (s := .ty) _ | exact ofLegacy_toLegacy (s := .tm) _
  | _, .inst f A => by
      change Expr.inst (ofLegacyTm f.toLegacy) (ofLegacyTy A.toLegacy) = _
      congr <;> first | exact ofLegacy_toLegacy (s := .ty) _ | exact ofLegacy_toLegacy (s := .tm) _
  | _, .gen K t => by
      change Expr.gen K (ofLegacyTm t.toLegacy) = _
      congr; exact ofLegacy_toLegacy (s := .tm) t
  | _, .eq A x y => by
      change Expr.eq (ofLegacyTy A.toLegacy) (ofLegacyTm x.toLegacy) (ofLegacyTm y.toLegacy) = _
      congr <;> first | exact ofLegacy_toLegacy (s := .ty) _ | exact ofLegacy_toLegacy (s := .tm) _
  | _, .epsilon A p => by
      change Expr.epsilon (ofLegacyTy A.toLegacy) (ofLegacyTm p.toLegacy) = _
      congr <;> first | exact ofLegacy_toLegacy (s := .ty) _ | exact ofLegacy_toLegacy (s := .tm) _
  | _, .abs A p x => by
      change Expr.abs (ofLegacyTy A.toLegacy) (ofLegacyTm p.toLegacy) (ofLegacyTm x.toLegacy) = _
      congr <;> first | exact ofLegacy_toLegacy (s := .ty) _ | exact ofLegacy_toLegacy (s := .tm) _
  | _, .rep A p x => by
      change Expr.rep (ofLegacyTy A.toLegacy) (ofLegacyTm p.toLegacy) (ofLegacyTm x.toLegacy) = _
      congr <;> first | exact ofLegacy_toLegacy (s := .ty) _ | exact ofLegacy_toLegacy (s := .tm) _

def tyEquiv : Equiv (Ty Base) (HOLOmega.Ty Base) where
  toFun := Expr.toLegacy
  invFun := ofLegacyTy
  left_inv := ofLegacy_toLegacy
  right_inv := toLegacy_ofLegacyTy

def tmEquiv : Equiv (Tm Base) (HOLOmega.Tm Base) where
  toFun := Expr.toLegacy
  invFun := ofLegacyTm
  left_inv := ofLegacy_toLegacy
  right_inv := toLegacy_ofLegacyTm

/-- Operations transported from the established substitution algebra.  These
definitions make the comparison maps homomorphisms by construction. -/
def Ty.rename (ρ : Nat → Nat) (A : Ty Base) : Ty Base :=
  ofLegacyTy (A.toLegacy.rename ρ)
def Ty.subst (σ : Nat → Ty Base) (A : Ty Base) : Ty Base :=
  ofLegacyTy (A.toLegacy.subst (fun n => (σ n).toLegacy))
def Tm.rename (ρ : Nat → Nat) (t : Tm Base) : Tm Base :=
  ofLegacyTm (t.toLegacy.rename ρ)
def Tm.renameTy (ρ : Nat → Nat) (t : Tm Base) : Tm Base :=
  ofLegacyTm (t.toLegacy.renameTy ρ)
def Tm.subst (σ : Nat → Tm Base) (t : Tm Base) : Tm Base :=
  ofLegacyTm (t.toLegacy.subst (fun n => (σ n).toLegacy))
def Tm.substTy (σ : Nat → Ty Base) (t : Tm Base) : Tm Base :=
  ofLegacyTm (t.toLegacy.substTy (fun n => (σ n).toLegacy))

@[simp] theorem toLegacy_renameTy (A : Ty Base) :
    (A.rename ρ).toLegacy = A.toLegacy.rename ρ := by simp [Ty.rename]
@[simp] theorem toLegacy_substTy (A : Ty Base) :
    (A.subst σ).toLegacy = A.toLegacy.subst (fun n => (σ n).toLegacy) := by simp [Ty.subst]
@[simp] theorem toLegacy_rename (t : Tm Base) :
    (t.rename ρ).toLegacy = t.toLegacy.rename ρ := by simp [Tm.rename]
@[simp] theorem toLegacy_tmRenameTy (t : Tm Base) :
    (t.renameTy ρ).toLegacy = t.toLegacy.renameTy ρ := by simp [Tm.renameTy]
@[simp] theorem toLegacy_subst (t : Tm Base) :
    (t.subst σ).toLegacy = t.toLegacy.subst (fun n => (σ n).toLegacy) := by simp [Tm.subst]
@[simp] theorem toLegacy_tmSubstTy (t : Tm Base) :
    (t.substTy σ).toLegacy = t.toLegacy.substTy (fun n => (σ n).toLegacy) := by simp [Tm.substTy]

abbrev Kinded (Δ : List Kind) (A : Ty Base) (K : Kind) : Prop :=
  HOLOmega.IndexedKinded Δ A.toLegacy K
abbrev HasType (Δ : List Kind) (Γ : List (Ty Base)) (t : Tm Base) (A : Ty Base) : Prop :=
  HOLOmega.IndexedHasType Δ (Γ.map Expr.toLegacy) t.toLegacy A.toLegacy

theorem kinded_legacy_iff : Kinded Δ A K ↔ HOLOmega.Kinded Δ A.toLegacy K :=
  HOLOmega.judgement_kinded_iff
theorem hasType_legacy_iff : HasType Δ Γ t A ↔
    HOLOmega.HasType Δ (Γ.map Expr.toLegacy) t.toLegacy A.toLegacy :=
  HOLOmega.judgement_hasType_iff

end ProjectBeth.HOLOmega.Syntax.Indexed
