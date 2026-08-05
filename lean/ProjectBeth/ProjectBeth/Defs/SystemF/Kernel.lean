import Mathlib

universe u v

namespace ProjectBeth.SystemF

class Universe where
  Code : Type u
  El : Code → Type u
  bool : Code
  boolEquiv : El bool ≃ Bool
  nat : Code
  natEquiv : El nat ≃ Nat
  arr : Code → Code → Code
  arrEquiv : ∀ A B, El (arr A B) ≃ (El A → El B)
  all : (Code → Code) → Code
  allEquiv : ∀ F, El (all F) ≃ ((X : Code) → El (F X))

variable (U : Universe)

abbrev Ty (n : Nat) := (Fin n → U.Code) → U.Code

namespace Ty

def var (i : Fin n) : Ty U n := fun ρ => ρ i
def bool : Ty U n := fun _ => U.bool
def nat : Ty U n := fun _ => U.nat
def arr (A B : Ty U n) : Ty U n := fun ρ => U.arr (A ρ) (B ρ)
def all (A : Ty U (n + 1)) : Ty U n :=
  fun ρ => U.all (fun X => A (Fin.cases X ρ))

abbrev Sub (n m : Nat) := (Fin m → U.Code) → Fin n → U.Code

def subst (A : Ty U n) (σ : Sub U n m) : Ty U m := fun ρ => A (σ ρ)

def liftSub (σ : Sub U n m) : Sub U (n + 1) (m + 1) :=
  fun ρ => Fin.cases (ρ 0) (fun i => σ (fun j => ρ j.succ) i)

def instantiate (A : Ty U (n + 1)) (X : Ty U n) : Ty U n :=
  fun ρ => A (Fin.cases (X ρ) ρ)

@[simp] theorem subst_id (A : Ty U n) : A.subst U (fun ρ => ρ) = A := rfl

theorem subst_comp (A : Ty U n) (σ : Sub U n m) (τ : Sub U m k) :
    (A.subst U σ).subst U τ = A.subst U (fun ρ => σ (τ ρ)) := rfl

theorem subst_arr (A B : Ty U n) (σ : Sub U n m) :
    (arr U A B).subst U σ = arr U (A.subst U σ) (B.subst U σ) := rfl

end Ty

abbrev Ctx (n : Nat) := List (Ty U n)

def Ctx.El : (Γ : Ctx U n) → (ρ : Fin n → U.Code) → Type u
  | [], _ => PUnit
  | A :: Γ, ρ => U.El (A ρ) × Ctx.El Γ ρ

def Ctx.subst (Γ : Ctx U n) (σ : Ty.Sub U n m) : Ctx U m :=
  Γ.map fun A => A.subst U σ

def Ctx.substEl (σ : Ty.Sub U n m) :
    (Γ : Ctx U n) → Ctx.El U (Ctx.subst U Γ σ) ρ → Ctx.El U Γ (σ ρ)
  | [], _ => PUnit.unit
  | _ :: Γ, γ => (γ.1, Ctx.substEl σ Γ γ.2)

def Ctx.weaken (Γ : Ctx U n) : Ctx U (n + 1) :=
  Γ.map fun A ρ => A (fun i => ρ i.succ)

def Ctx.weakenEl : (Γ : Ctx U n) → Ctx.El U Γ ρ →
    Ctx.El U (Ctx.weaken U Γ) (Fin.cases X ρ)
  | [], _ => PUnit.unit
  | _ :: Γ, γ => (γ.1, Ctx.weakenEl Γ γ.2)

abbrev Tm (Γ : Ctx U n) (A : Ty U n) :=
  ∀ ρ, Ctx.El U Γ ρ → U.El (A ρ)

namespace Tm

def vz : Tm U (A :: Γ) A := fun _ γ => γ.1
def vs (x : Tm U Γ A) : Tm U (B :: Γ) A := fun ρ γ => x ρ γ.2
def app (f : Tm U Γ (Ty.arr U A B)) (x : Tm U Γ A) : Tm U Γ B :=
  fun ρ γ => U.arrEquiv (A ρ) (B ρ) (f ρ γ) (x ρ γ)
def lam (t : Tm U (A :: Γ) B) : Tm U Γ (Ty.arr U A B) :=
  fun ρ γ => (U.arrEquiv (A ρ) (B ρ)).symm (fun x => t ρ (x, γ))
def bool (b : Bool) : Tm U Γ (Ty.bool U) := fun _ _ => U.boolEquiv.symm b
def nat (k : Nat) : Tm U Γ (Ty.nat U) := fun _ _ => U.natEquiv.symm k

def tyLam (t : Tm U (Ctx.weaken U Γ) A) : Tm U Γ (Ty.all U A) :=
  fun ρ γ => (U.allEquiv (fun X => A (Fin.cases X ρ))).symm
    (fun X => t (Fin.cases X ρ) (Ctx.weakenEl U Γ γ))

def tyApp {n : Nat} {Γ : Ctx U n} {A : Ty U (n + 1)}
    (f : Tm U Γ (Ty.all U A)) (X : Ty U n) :
    Tm U Γ (Ty.instantiate U A X) :=
  fun ρ γ => U.allEquiv (fun Y => A (Fin.cases Y ρ)) (f ρ γ) (X ρ)

abbrev Sub (Γ Γ' : Ctx U n) := ∀ ρ, Ctx.El U Γ' ρ → Ctx.El U Γ ρ
def subst (t : Tm U Γ A) (σ : Sub U Γ Γ') : Tm U Γ' A := fun ρ γ => t ρ (σ ρ γ)

def substTy {n m : Nat} {Γ : Ctx U n} {A : Ty U n}
    (t : Tm U Γ A) (σ : Ty.Sub U n m) :
    Tm U (Ctx.subst U Γ σ) (A.subst U σ) :=
  fun ρ γ => t (σ ρ) (Ctx.substEl U σ Γ γ)

@[simp] theorem subst_id (t : Tm U Γ A) : t.subst U (fun _ γ => γ) = t := rfl
theorem subst_comp (t : Tm U Γ A) (σ : Sub U Γ Γ') (τ : Sub U Γ' Γ'') :
    (t.subst U σ).subst U τ = t.subst U (fun ρ γ => σ ρ (τ ρ γ)) := rfl
@[simp] theorem substTy_apply {n m : Nat} {Γ : Ctx U n} {A : Ty U n}
    (t : Tm U Γ A) (σ : Ty.Sub U n m) ρ γ :
    Tm.substTy U t σ ρ γ = t (σ ρ) (Ctx.substEl U σ Γ γ) := rfl

@[simp] theorem beta (t : Tm U (A :: Γ) B) (x : Tm U Γ A) :
    app U (lam U t) x = fun ρ γ => t ρ (x ρ γ, γ) := by
  funext ρ γ
  change U.arrEquiv (A ρ) (B ρ)
    ((U.arrEquiv (A ρ) (B ρ)).symm (fun y => t ρ (y, γ))) (x ρ γ) = _
  rw [Equiv.apply_symm_apply]

end Tm

inductive Reduces : {n : Nat} → {Γ : Ctx U n} → {A : Ty U n} →
    Tm U Γ A → Tm U Γ A → Prop
  | refl (t : Tm U Γ A) : Reduces t t
  | trans : Reduces t u → Reduces u v → Reduces t v
  | app : Reduces f g → Reduces x y → Reduces (Tm.app U f x) (Tm.app U g y)
  | lam : Reduces t u → Reduces (Tm.lam U t) (Tm.lam U u)
  | beta (t : Tm U (A :: Γ) B) (x : Tm U Γ A) :
      Reduces (Tm.app U (Tm.lam U t) x) (fun ρ γ => t ρ (x ρ γ, γ))

theorem Reduces.sound (h : Reduces U t u) : t = u := by
  induction h with
  | refl => rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | lam _ ih => simp [ih]
  | beta => exact Tm.beta U _ _

/-- In the shallow intrinsic kernel both endpoints have the same type by the
index of `Reduces`; this is the typed target projection, not an inductive
subject-reduction argument. -/
def Reduces.typedTarget {n : Nat} {Γ : Ctx U n} {A : Ty U n}
    {t u : Tm U Γ A} (_h : Reduces U t u) : Tm U Γ A := u

/-- Compatibility name for `Reduces.typedTarget`.  The raw-syntax preservation
proof lives in `SystemF.Inductive.Semantics.hasType_preservation`. -/
def preservation {n : Nat} {Γ : Ctx U n} {A : Ty U n} {t u : Tm U Γ A}
    (h : Reduces U t u) : Tm U Γ A := h.typedTarget U

structure Quotation (D : Type v) where
  quote : ∀ A, U.El A → D

def Quotation.Rel (Q : Quotation U D) (A : U.Code) (d : D) : Prop :=
  ∃ x : U.El A, d = Q.quote A x

theorem fundamental (Q : Quotation U D) (t : Tm U Γ A) (ρ γ) :
    Q.Rel U (A ρ) (Q.quote (A ρ) (t ρ γ)) := ⟨t ρ γ, rfl⟩

theorem reduction_related {n : Nat} {Γ : Ctx U n} {A : Ty U n}
    {t u : Tm U Γ A} (Q : Quotation U D) (h : Reduces U t u) (ρ γ) :
    Q.quote (A ρ) (t ρ γ) = Q.quote (A ρ) (u ρ γ) := by rw [h.sound U]

end ProjectBeth.SystemF
