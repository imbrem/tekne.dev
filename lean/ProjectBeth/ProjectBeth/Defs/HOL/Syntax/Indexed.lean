import ProjectBeth.Defs.HOL.Syntax
import Mathlib.Logic.Equiv.Defs

/-! A non-mutual, indexed presentation of the raw HOL grammar.

`Node` is useful when a proof or generic traversal should use one ordinary
induction principle across types and terms.  `Ty` and `Tm` remain the public,
conventional mutually inductive presentation; the equivalences below make the
choice of presentation immaterial.
-/

universe u

namespace ProjectBeth.HOL.Syntax.Indexed

inductive Category : Type
  | ty
  | tm
  deriving DecidableEq

/-- The raw HOL type/term grammar as one indexed inductive family. -/
inductive Node (Base : Type u) : Category → Type u
  | tyBase : Base → Node Base .ty
  | tyBool : Node Base .ty
  | tyArr : Node Base .ty → Node Base .ty → Node Base .ty
  | tySub : Node Base .ty → Node Base .tm → Node Base .ty
  | tmVar : Nat → Node Base .tm
  | tmApp : Node Base .tm → Node Base .tm → Node Base .tm
  | tmLam : Node Base .ty → Node Base .tm → Node Base .tm
  | tmBool : Bool → Node Base .tm
  | tmEq : Node Base .ty → Node Base .tm → Node Base .tm → Node Base .tm
  | tmEpsilon : Node Base .ty → Node Base .tm → Node Base .tm
  | tmAbs : Node Base .ty → Node Base .tm → Node Base .tm → Node Base .tm
  | tmRep : Node Base .ty → Node Base .tm → Node Base .tm → Node Base .tm

abbrev ITy (Base : Type u) := Node Base .ty
abbrev ITm (Base : Type u) := Node Base .tm

variable {Base : Type u}

mutual
  def encodeTy : HOL.Ty Base → ITy Base
    | .base A => .tyBase A
    | .bool => .tyBool
    | .arr A B => .tyArr (encodeTy A) (encodeTy B)
    | .sub A p => .tySub (encodeTy A) (encodeTm p)

  def encodeTm : HOL.Tm Base → ITm Base
    | .var n => .tmVar n
    | .app f x => .tmApp (encodeTm f) (encodeTm x)
    | .lam A t => .tmLam (encodeTy A) (encodeTm t)
    | .bool b => .tmBool b
    | .eq A x y => .tmEq (encodeTy A) (encodeTm x) (encodeTm y)
    | .epsilon A p => .tmEpsilon (encodeTy A) (encodeTm p)
    | .abs A p x => .tmAbs (encodeTy A) (encodeTm p) (encodeTm x)
    | .rep A p x => .tmRep (encodeTy A) (encodeTm p) (encodeTm x)
end

mutual
  def decodeTy : ITy Base → HOL.Ty Base
    | .tyBase A => .base A
    | .tyBool => .bool
    | .tyArr A B => .arr (decodeTy A) (decodeTy B)
    | .tySub A p => .sub (decodeTy A) (decodeTm p)

  def decodeTm : ITm Base → HOL.Tm Base
    | .tmVar n => .var n
    | .tmApp f x => .app (decodeTm f) (decodeTm x)
    | .tmLam A t => .lam (decodeTy A) (decodeTm t)
    | .tmBool b => .bool b
    | .tmEq A x y => .eq (decodeTy A) (decodeTm x) (decodeTm y)
    | .tmEpsilon A p => .epsilon (decodeTy A) (decodeTm p)
    | .tmAbs A p x => .abs (decodeTy A) (decodeTm p) (decodeTm x)
    | .tmRep A p x => .rep (decodeTy A) (decodeTm p) (decodeTm x)
end

mutual
  @[simp] theorem decode_encode_ty : (A : HOL.Ty Base) → decodeTy (encodeTy A) = A
    | .base _ => by simp [encodeTy, decodeTy]
    | .bool => by simp [encodeTy, decodeTy]
    | .arr A B => by simp [encodeTy, decodeTy, decode_encode_ty A, decode_encode_ty B]
    | .sub A p => by simp [encodeTy, decodeTy, decode_encode_ty A, decode_encode_tm p]

  @[simp] theorem decode_encode_tm : (t : HOL.Tm Base) → decodeTm (encodeTm t) = t
    | .var _ => by simp [encodeTm, decodeTm]
    | .app f x => by simp [encodeTm, decodeTm, decode_encode_tm f, decode_encode_tm x]
    | .lam A t => by simp [encodeTm, decodeTm, decode_encode_ty A, decode_encode_tm t]
    | .bool _ => by simp [encodeTm, decodeTm]
    | .eq A x y => by
      simp [encodeTm, decodeTm, decode_encode_ty A, decode_encode_tm x,
        decode_encode_tm y]
    | .epsilon A p => by simp [encodeTm, decodeTm, decode_encode_ty A, decode_encode_tm p]
    | .abs A p x => by
      simp [encodeTm, decodeTm, decode_encode_ty A, decode_encode_tm p,
        decode_encode_tm x]
    | .rep A p x => by
      simp [encodeTm, decodeTm, decode_encode_ty A, decode_encode_tm p,
        decode_encode_tm x]
end

def decodeNode : {s : Category} → Node Base s →
    (match s with | .ty => HOL.Ty Base | .tm => HOL.Tm Base)
  | .ty, A => decodeTy A
  | .tm, t => decodeTm t

def encodeNode : (s : Category) →
    (match s with | .ty => HOL.Ty Base | .tm => HOL.Tm Base) → Node Base s
  | .ty, A => encodeTy A
  | .tm, t => encodeTm t

/-- A directly usable ordinary induction over both halves of the grammar. -/
@[simp] theorem encode_decode {s : Category} (n : Node Base s) :
    encodeNode s (decodeNode n) = n := by
  induction n <;> simp_all [encodeNode, decodeNode, encodeTy, encodeTm, decodeTy, decodeTm]

@[simp] theorem encode_decode_ty (A : ITy Base) : encodeTy (decodeTy A) = A :=
  encode_decode A

@[simp] theorem encode_decode_tm (t : ITm Base) : encodeTm (decodeTm t) = t :=
  encode_decode t

def tyEquiv (Base : Type u) : Equiv (HOL.Ty Base) (ITy Base) where
  toFun := encodeTy
  invFun := decodeTy
  left_inv := decode_encode_ty
  right_inv := encode_decode_ty

def tmEquiv (Base : Type u) : Equiv (HOL.Tm Base) (ITm Base) where
  toFun := encodeTm
  invFun := decodeTm
  left_inv := decode_encode_tm
  right_inv := encode_decode_tm

/-- Lift a renaming through one de Bruijn binder. -/
def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Simultaneous traversal of the indexed grammar.  Types are traversed too
because subtype types contain a predicate term. -/
def rename (ρ : Nat → Nat) : {s : Category} → Node Base s → Node Base s
  | .ty, .tyBase A => .tyBase A
  | .ty, .tyBool => .tyBool
  | .ty, .tyArr A B => .tyArr (rename ρ A) (rename ρ B)
  | .ty, .tySub A p => .tySub (rename ρ A) (rename (upRen ρ) p)
  | .tm, .tmVar n => .tmVar (ρ n)
  | .tm, .tmApp f x => .tmApp (rename ρ f) (rename ρ x)
  | .tm, .tmLam A t => .tmLam (rename ρ A) (rename (upRen ρ) t)
  | .tm, .tmBool b => .tmBool b
  | .tm, .tmEq A x y => .tmEq (rename ρ A) (rename ρ x) (rename ρ y)
  | .tm, .tmEpsilon A p => .tmEpsilon (rename ρ A) (rename ρ p)
  | .tm, .tmAbs A p x => .tmAbs (rename ρ A) (rename (upRen ρ) p) (rename ρ x)
  | .tm, .tmRep A p x => .tmRep (rename ρ A) (rename (upRen ρ) p) (rename ρ x)

/-- Lift a substitution through one de Bruijn binder. -/
def upSub (σ : Nat → ITm Base) : Nat → ITm Base
  | 0 => .tmVar 0
  | n + 1 => rename (upRen Nat.succ) (σ n)

def subst (σ : Nat → ITm Base) : {s : Category} → Node Base s → Node Base s
  | .ty, .tyBase A => .tyBase A
  | .ty, .tyBool => .tyBool
  | .ty, .tyArr A B => .tyArr (subst σ A) (subst σ B)
  | .ty, .tySub A p => .tySub (subst σ A) (subst (upSub σ) p)
  | .tm, .tmVar n => σ n
  | .tm, .tmApp f x => .tmApp (subst σ f) (subst σ x)
  | .tm, .tmLam A t => .tmLam (subst σ A) (subst (upSub σ) t)
  | .tm, .tmBool b => .tmBool b
  | .tm, .tmEq A x y => .tmEq (subst σ A) (subst σ x) (subst σ y)
  | .tm, .tmEpsilon A p => .tmEpsilon (subst σ A) (subst σ p)
  | .tm, .tmAbs A p x => .tmAbs (subst σ A) (subst (upSub σ) p) (subst σ x)
  | .tm, .tmRep A p x => .tmRep (subst σ A) (subst (upSub σ) p) (subst σ x)

def freeVars : {s : Category} → Node Base s → (Nat → Prop)
  | .ty, .tyBase _ => fun _ => False
  | .ty, .tyBool => fun _ => False
  | .ty, .tyArr A B => fun n => freeVars A n ∨ freeVars B n
  | .ty, .tySub A p => fun n => freeVars A n ∨ freeVars p (n + 1)
  | .tm, .tmVar n => fun m => m = n
  | .tm, .tmApp f x => fun n => freeVars f n ∨ freeVars x n
  | .tm, .tmLam A t => fun n => freeVars A n ∨ freeVars t (n + 1)
  | .tm, .tmBool _ => fun _ => False
  | .tm, .tmEq A x y => fun n => freeVars A n ∨ freeVars x n ∨ freeVars y n
  | .tm, .tmEpsilon A p => fun n => freeVars A n ∨ freeVars p n
  | .tm, .tmAbs A p x => fun n => freeVars A n ∨ freeVars p (n + 1) ∨ freeVars x n
  | .tm, .tmRep A p x => fun n => freeVars A n ∨ freeVars p (n + 1) ∨ freeVars x n

/-! Exact bridge squares for operations on the conventional raw grammar.
These definitions also provide raw HOL with a single, binder-correct source of
renaming, substitution and free-variable operations. -/

def renameLegacyTy (ρ : Nat → Nat) (A : HOL.Ty Base) : HOL.Ty Base :=
  decodeTy (rename ρ (encodeTy A))

def renameLegacyTm (ρ : Nat → Nat) (t : HOL.Tm Base) : HOL.Tm Base :=
  decodeTm (rename ρ (encodeTm t))

def substLegacyTy (σ : Nat → HOL.Tm Base) (A : HOL.Ty Base) : HOL.Ty Base :=
  decodeTy (subst (encodeTm ∘ σ) (encodeTy A))

def substLegacyTm (σ : Nat → HOL.Tm Base) (t : HOL.Tm Base) : HOL.Tm Base :=
  decodeTm (subst (encodeTm ∘ σ) (encodeTm t))

def freeVarsLegacyTy (A : HOL.Ty Base) : Nat → Prop := freeVars (encodeTy A)

def freeVarsLegacyTm (t : HOL.Tm Base) : Nat → Prop := freeVars (encodeTm t)

@[simp] theorem encode_renameLegacyTy (ρ : Nat → Nat) (A : HOL.Ty Base) :
    encodeTy (renameLegacyTy ρ A) = rename ρ (encodeTy A) := by
  simp [renameLegacyTy]

@[simp] theorem encode_renameLegacyTm (ρ : Nat → Nat) (t : HOL.Tm Base) :
    encodeTm (renameLegacyTm ρ t) = rename ρ (encodeTm t) := by
  simp [renameLegacyTm]

@[simp] theorem encode_substLegacyTy (σ : Nat → HOL.Tm Base) (A : HOL.Ty Base) :
    encodeTy (substLegacyTy σ A) = subst (encodeTm ∘ σ) (encodeTy A) := by
  simp [substLegacyTy]

@[simp] theorem encode_substLegacyTm (σ : Nat → HOL.Tm Base) (t : HOL.Tm Base) :
    encodeTm (substLegacyTm σ t) = subst (encodeTm ∘ σ) (encodeTm t) := by
  simp [substLegacyTm]

theorem freeVars_ty_square (A : HOL.Ty Base) :
    freeVarsLegacyTy A = freeVars (encodeTy A) := rfl

theorem freeVars_tm_square (t : HOL.Tm Base) :
    freeVarsLegacyTm t = freeVars (encodeTm t) := rfl

/-- Well-formedness and typing transported along the exact grammar
equivalence.  Thus existing metatheory applies without duplication. -/
abbrev Wf (A : ITy Base) : Prop := HOL.Ty.Wf (decodeTy A)

abbrev HasType (Γ : List (ITy Base)) (t : ITm Base) (A : ITy Base) : Prop :=
  HOL.HasType (Γ.map decodeTy) (decodeTm t) (decodeTy A)

@[simp] theorem wf_encode_iff (A : HOL.Ty Base) : Wf (encodeTy A) ↔ HOL.Ty.Wf A := by
  simp [Wf]

@[simp] theorem hasType_encode_iff (Γ : HOL.Ctx Base) (t : HOL.Tm Base) (A : HOL.Ty Base) :
    HasType (Γ.map encodeTy) (encodeTm t) (encodeTy A) ↔ HOL.HasType Γ t A := by
  simp only [HasType, List.map_map, decode_encode_tm, decode_encode_ty]
  have h : List.map (decodeTy ∘ encodeTy) Γ = List.map id Γ := by
    apply List.map_congr_left
    intro A hA
    exact decode_encode_ty A
  rw [h, List.map_id]

/-- The generic indexed judgement and the indexed grammar commute: encode the
grammar first or transport the old judgement first gives the same proposition. -/
theorem judgement_wf_square (A : HOL.Ty Base) :
    HOL.Judgement (.wf A) ↔ Wf (encodeTy A) := by
  rw [HOL.judgement_wf_iff, wf_encode_iff]

theorem judgement_hasType_square (Γ : HOL.Ctx Base) (t : HOL.Tm Base) (A : HOL.Ty Base) :
    HOL.Judgement (.hasType Γ t A) ↔
      HasType (Γ.map encodeTy) (encodeTm t) (encodeTy A) := by
  rw [HOL.judgement_hasType_iff, hasType_encode_iff]

end ProjectBeth.HOL.Syntax.Indexed
