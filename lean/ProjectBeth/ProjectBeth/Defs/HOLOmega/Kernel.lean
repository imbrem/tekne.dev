import ProjectBeth.Defs.HOL.Syntax
import ProjectBeth.Defs.HOLOmega.Syntax
import Mathlib

universe u

namespace ProjectBeth.HOLOmega.Kernel

/-- A Tarskian universe with the closures needed by the shallow-intrinsic
HOLω kernel.  Predicate codes keep syntax stratified: subtype formation does
not mention the term datatype. -/
class Universe where
  Code : Type u
  El : Code → Type u
  inhabited : ∀ A, Inhabited (El A)
  boolCode : Code
  boolEquiv : El boolCode ≃ Bool
  arr : Code → Code → Code
  arrEquiv : ∀ A B, El (arr A B) ≃ (El A → El B)
  subCode : (A : Code) → (El A → Prop) → Code
  subEquiv : ∀ A P, El (subCode A P) ≃ ProjectBeth.HOL.TotalSubtype (El A) P

attribute [instance] Universe.inhabited

variable (U : Universe)

def Kind.Val : ProjectBeth.HOLOmega.Kind → Type u
  | .star => U.Code
  | .arr K L => Kind.Val K → Kind.Val L

def Kind.Env : List ProjectBeth.HOLOmega.Kind → Type u
  | [] => PUnit
  | K :: Δ => Kind.Val U K × Kind.Env Δ

abbrev Ty (Δ : List ProjectBeth.HOLOmega.Kind) (K : ProjectBeth.HOLOmega.Kind) :=
  Kind.Env U Δ → Kind.Val U K

namespace Ty

def base (A : U.Code) : Ty U Δ .star := fun _ => A
def boolCode : Ty U Δ .star := fun _ => U.boolCode
def arr (A B : Ty U Δ .star) : Ty U Δ .star := fun ρ => U.arr (A ρ) (B ρ)
def lam (A : Ty U (K :: Δ) L) : Ty U Δ (.arr K L) := fun ρ X => A (X, ρ)
def app (F : Ty U Δ (.arr K L)) (A : Ty U Δ K) : Ty U Δ L := fun ρ => F ρ (A ρ)

def Pred (A : Ty U Δ .star) := ∀ ρ, U.El (A ρ) → Prop

def sub (A : Ty U Δ .star) (P : Pred U A) : Ty U Δ .star :=
  fun ρ => U.subCode (A ρ) (P ρ)

abbrev Sub (Δ Δ' : List ProjectBeth.HOLOmega.Kind) := Kind.Env U Δ' → Kind.Env U Δ

def subst (A : Ty U Δ K) (σ : Sub U Δ Δ') : Ty U Δ' K := fun ρ => A (σ ρ)

@[simp] theorem subst_apply (A : Ty U Δ K) (σ : Sub U Δ Δ') (ρ) :
    A.subst U σ ρ = A (σ ρ) := rfl

@[simp] theorem subst_id (A : Ty U Δ K) : A.subst U id = A := rfl

theorem subst_comp (A : Ty U Δ K) (σ : Sub U Δ Δ') (τ : Sub U Δ' Δ'') :
    (A.subst U σ).subst U τ = A.subst U (σ ∘ τ) := rfl

@[simp] theorem beta (A : Ty U (K :: Δ) L) (X : Ty U Δ K) :
    app U (lam U A) X = fun ρ => A (X ρ, ρ) := rfl

theorem eta (F : Ty U Δ (.arr K L)) : lam U (fun ρ => F ρ.2 ρ.1) = F := rfl

end Ty

def Ctx (Δ : List ProjectBeth.HOLOmega.Kind) := List (Ty U Δ .star)

def Ctx.El : (Γ : Ctx U Δ) → (ρ : Kind.Env U Δ) → Type u
  | [], _ => PUnit
  | A :: Γ, ρ => U.El (A ρ) × Ctx.El Γ ρ

abbrev Tm (Γ : Ctx U Δ) (A : Ty U Δ .star) :=
  ∀ ρ, Ctx.El U Γ ρ → U.El (A ρ)

namespace Tm

def vz : Tm U (A :: Γ) A := fun _ γ => γ.1

def vs (x : Tm U Γ A) : Tm U (B :: Γ) A := fun ρ γ => x ρ γ.2

def app (f : Tm U Γ (Ty.arr U A B)) (x : Tm U Γ A) : Tm U Γ B :=
  fun ρ γ => U.arrEquiv (A ρ) (B ρ) (f ρ γ) (x ρ γ)

def lam (t : Tm U (A :: Γ) B) : Tm U Γ (Ty.arr U A B) :=
  fun ρ γ => (U.arrEquiv (A ρ) (B ρ)).symm (fun x => t ρ (x, γ))

def boolCode (b : Bool) : Tm U Γ (Ty.boolCode U) := fun _ _ => U.boolEquiv.symm b

noncomputable def epsilon (p : Tm U Γ (Ty.arr U A (Ty.boolCode U))) : Tm U Γ A :=
  fun ρ γ => by
    classical
    letI := U.inhabited (A ρ)
    let q := fun x => U.boolEquiv (U.arrEquiv (A ρ) U.boolCode (p ρ γ) x)
    exact if h : ∃ x, q x = true then Classical.choose h else default

noncomputable def equal (x y : Tm U Γ A) : Tm U Γ (Ty.boolCode U) := by
  classical
  exact fun ρ γ => U.boolEquiv.symm (decide (x ρ γ = y ρ γ))

noncomputable def abs (P : Ty.Pred U A) (x : Tm U Γ A) :
    Tm U Γ (Ty.sub U A P) :=
  fun ρ γ => by
    letI := U.inhabited (A ρ)
    exact (U.subEquiv (A ρ) (P ρ)).symm
      (ProjectBeth.HOL.TotalSubtype.abs (P ρ) (x ρ γ))

def rep (P : Ty.Pred U A) (x : Tm U Γ (Ty.sub U A P)) : Tm U Γ A :=
  fun ρ γ => ProjectBeth.HOL.TotalSubtype.rep (U.subEquiv (A ρ) (P ρ) (x ρ γ))

abbrev Sub (Γ Γ' : Ctx U Δ) := ∀ ρ, Ctx.El U Γ' ρ → Ctx.El U Γ ρ

def subst (t : Tm U Γ A) (σ : Sub U Γ Γ') : Tm U Γ' A := fun ρ γ => t ρ (σ ρ γ)

@[simp] theorem subst_id (t : Tm U Γ A) : t.subst U (fun _ γ => γ) = t := rfl

theorem subst_comp (t : Tm U Γ A) (σ : Sub U Γ Γ') (τ : Sub U Γ' Γ'') :
    (t.subst U σ).subst U τ = t.subst U (fun ρ γ => σ ρ (τ ρ γ)) := rfl

@[simp] theorem beta (t : Tm U (A :: Γ) B) (x : Tm U Γ A) :
    app U (lam U t) x = fun ρ γ => t ρ (x ρ γ, γ) := by
  funext ρ γ
  change U.arrEquiv (A ρ) (B ρ)
    ((U.arrEquiv (A ρ) (B ρ)).symm (fun y => t ρ (y, γ))) (x ρ γ) = _
  rw [Equiv.apply_symm_apply]

theorem eta (f : Tm U Γ (Ty.arr U A B)) :
    lam U (app U (vs U f) (vz U)) = f := by
  funext ρ γ
  change (U.arrEquiv (A ρ) (B ρ)).symm
    (fun x => U.arrEquiv (A ρ) (B ρ) (f ρ γ) x) = f ρ γ
  rw [show (fun x => U.arrEquiv (A ρ) (B ρ) (f ρ γ) x) =
      U.arrEquiv (A ρ) (B ρ) (f ρ γ) from rfl]
  exact (U.arrEquiv (A ρ) (B ρ)).symm_apply_apply _

end Tm

/-- The equality calculus is intentionally small: congruence is inherited from
Lean equality, while these constructors expose the HOLω proof rules. -/
inductive EqTm {Δ} : (Γ : Ctx U Δ) → {A : Ty U Δ .star} → Tm U Γ A → Tm U Γ A → Prop
  | refl (t) : EqTm Γ t t
  | symm : EqTm Γ t u → EqTm Γ u t
  | trans : EqTm Γ t u → EqTm Γ u v → EqTm Γ t v
  | app : EqTm Γ f g → EqTm Γ x y → EqTm Γ (Tm.app U f x) (Tm.app U g y)
  | lam : EqTm (A :: Γ) t u → EqTm Γ (Tm.lam U t) (Tm.lam U u)
  | beta (t : Tm U (A :: Γ) B) (x : Tm U Γ A) :
      EqTm Γ (Tm.app U (Tm.lam U t) x) (fun ρ γ => t ρ (x ρ γ, γ))
  | eta (f : Tm U Γ (Ty.arr U A B)) :
      EqTm Γ (Tm.lam U (Tm.app U (Tm.vs U f) (Tm.vz U))) f

theorem EqTm.sound {Δ} {Γ : Ctx U Δ} {A : Ty U Δ .star} {t u : Tm U Γ A}
    (h : EqTm U Γ t u) : t = u := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | lam _ ih => simp [ih]
  | beta => exact Tm.beta U _ _
  | eta => exact Tm.eta U _

end ProjectBeth.HOLOmega.Kernel
