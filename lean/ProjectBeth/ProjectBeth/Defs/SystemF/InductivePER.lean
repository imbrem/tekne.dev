import ProjectBeth.Defs.SystemF.Inductive
import ProjectBeth.Defs.SystemF.PER

universe u

namespace ProjectBeth.SystemF.Inductive

open ProjectBeth.SystemF

variable {D : Type u}

structure PERModel (D : Type u) where
  app : D → D → D
  boolPer : PER D
  natPer : PER D
  bool : Bool → D
  nat : Nat → D
  bool_mem : ∀ b, boolPer.Dom (bool b)
  nat_mem : ∀ n, natPer.Dom (nat n)
  lam : (D → D) → D
  lam_rel : ∀ {A B : PER D} (f g : D → D),
    (∀ {x y}, A.Rel x y → B.Rel (f x) (g y)) →
    (PER.arrow A B app).Rel (lam f) (lam g)
  tyApp : D → PER D → D
  tyLam : (PER D → D) → D
  allPer : (PER D → PER D) → PER D
  tyLam_rel : ∀ (f g : PER D → D)
    (body : PER D → PER D),
    (∀ R, (body R).Rel (f R) (g R)) →
    (allPer body).Rel (tyLam f) (tyLam g)
  tyApp_mem : ∀ {body : PER D → PER D} {f : D},
    (allPer body).Dom f → ∀ R, (body R).Dom (tyApp f R)
  tyApp_rel : ∀ {body : PER D → PER D} {f g : D},
    (allPer body).Rel f g → ∀ R, (body R).Rel (tyApp f R) (tyApp g R)

namespace Ty

def denote (M : PERModel D) (η : Nat → PER D) : Ty → PER D
  | .var n => η n
  | .bool => M.boolPer
  | .nat => M.natPer
  | .arr A B => PER.arrow (denote M η A) (denote M η B) M.app
  | .all A => M.allPer (fun R => denote M (fun | 0 => R | n + 1 => η n) A)

end Ty

namespace Tm

def eval (M : PERModel D) : Tm → (Nat → PER D) → (Nat → D) → D
  | .var n, _, γ => γ n
  | .app f x, η, γ => M.app (f.eval M η γ) (x.eval M η γ)
  | .lam _ t, η, γ => M.lam (fun x => t.eval M η (fun | 0 => x | n + 1 => γ n))
  | .tyApp f X, η, γ => M.tyApp (f.eval M η γ) (X.denote M η)
  | .tyLam t, η, γ => M.tyLam (fun R => t.eval M (fun | 0 => R | n + 1 => η n) γ)
  | .bool b, _, _ => M.bool b
  | .nat n, _, _ => M.nat n

end Tm

namespace PERModel

def CtxValid (M : PERModel D) (η : Nat → PER D) (Γ : List Ty) (γ : Nat → D) : Prop :=
  ∀ n (A : Ty), Γ[n]? = some A → (A.denote M η).Dom (γ n)

def CtxRel (M : PERModel D) (η : Nat → PER D) (Γ : List Ty)
    (γ δ : Nat → D) : Prop :=
  ∀ n (A : Ty), Γ[n]? = some A → (A.denote M η).Rel (γ n) (δ n)

theorem Ty.denote_rename (M : PERModel D) (η : Nat → PER D) (ρ : Nat → Nat) (A : Ty) :
    (A.rename ρ).denote M η = A.denote M (fun n => η (ρ n)) := by
  induction A generalizing η ρ with
  | var n => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.rename, Ty.denote, ihA, ihB]
  | all A ih =>
    simp only [Ty.rename, Ty.denote]
    congr 1
    funext R
    rw [ih]
    congr
    funext n
    cases n <;> rfl

theorem Ty.denote_subst (M : PERModel D) (η : Nat → PER D) (σ : Nat → Ty) (A : Ty) :
    (A.subst σ).denote M η = A.denote M (fun n => (σ n).denote M η) := by
  induction A generalizing η σ with
  | var n => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.subst, Ty.denote, ihA, ihB]
  | all A ih =>
    simp only [Ty.subst, Ty.denote]
    congr 1
    funext R
    rw [ih]
    congr
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [upTySub]
      change ((σ n).rename Nat.succ).denote M (fun | 0 => R | n + 1 => η n) = _
      rw [Ty.denote_rename]

theorem Ty.denote_lift (M : PERModel D) (η : Nat → PER D) (R : PER D) (A : Ty) :
    (A.lift.denote M (fun | 0 => R | n + 1 => η n)) = A.denote M η := by
  change (A.rename Nat.succ).denote M (fun | 0 => R | n + 1 => η n) = _
  rw [Ty.denote_rename]

theorem Ty.denote_instantiate (M : PERModel D) (η : Nat → PER D) (A X : Ty) :
    ((A.instantiate X).denote M η) =
      A.denote M (fun | 0 => X.denote M η | n + 1 => η n) := by
  rw [Ty.instantiate, Ty.denote_subst]
  congr
  funext n
  cases n <;> rfl

theorem CtxRel.lift (M : PERModel D) (η : Nat → PER D) (R : PER D)
    (h : CtxRel M η Γ γ δ) :
    CtxRel M (fun | 0 => R | n + 1 => η n) (Γ.map Ty.lift) γ δ := by
  intro n B hn
  cases hA : Γ[n]? with
  | none => simp [List.getElem?_map, hA] at hn
  | some A =>
    have heq : A.lift = B := by simpa [List.getElem?_map, hA] using hn
    subst B
    rw [Ty.denote_lift]
    exact h n A hA

theorem fundamental_rel (M : PERModel D) (h : HasType Δ Γ t A)
    (η : Nat → PER D) (γ δ : Nat → D) (hγ : CtxRel M η Γ γ δ) :
    (A.denote M η).Rel (t.eval M η γ) (t.eval M η δ) := by
  induction h generalizing η γ δ with
  | var h =>
    change ∀ n (A : Ty), _ at hγ
    exact hγ _ _ h
  | app hf hx ihf ihx => exact ihf η γ δ hγ (ihx η γ δ hγ)
  | lam ht ih =>
    apply M.lam_rel
    intro x y hxy
    exact ih η (fun | 0 => x | n + 1 => γ n)
      (fun | 0 => y | n + 1 => δ n) (by
      change ∀ n (B : Ty), _
      intro n B hn
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
        subst B
        exact hxy
      | succ n => exact hγ n B (by simpa using hn))
  | tyApp hf ih =>
    rw [Ty.denote_instantiate]
    exact M.tyApp_rel (ih η γ δ hγ) _
  | tyLam ht ih =>
    apply M.tyLam_rel
    intro R
    apply ih (fun | 0 => R | n + 1 => η n) γ δ
    exact CtxRel.lift M η R hγ
  | bool => exact M.bool_mem _
  | nat => exact M.nat_mem _

theorem fundamental (M : PERModel D) (h : HasType Δ Γ t A)
    (η : Nat → PER D) (γ : Nat → D) (hγ : CtxValid M η Γ γ) :
    (A.denote M η).Dom (t.eval M η γ) :=
  fundamental_rel M h η γ γ hγ

end PERModel

end ProjectBeth.SystemF.Inductive
