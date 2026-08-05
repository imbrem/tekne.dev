import ProjectBeth.Defs.Syntax.Representations

namespace ProjectBeth.Syntax.Untyped

def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

def upSub (σ : Nat → Tm) : Nat → Tm
  | 0 => .var 0
  | i + 1 => lift (σ i)

theorem upRen_comp (ρ τ : Nat → Nat) :
    upRen τ ∘ upRen ρ = upRen (τ ∘ ρ) := by
  funext i
  cases i <;> rfl

theorem rename_comp (ρ τ : Nat → Nat) (t : Tm) :
    rename τ (rename ρ t) = rename (τ ∘ ρ) t := by
  induction t generalizing ρ τ with
  | var i => rfl
  | app f a ihf iha => simp [rename, ihf, iha]
  | lam b ih =>
    simp only [rename]
    rw [ih]
    apply congrArg Tm.lam
    apply rename_congr
    exact congrFun (upRen_comp ρ τ)

theorem rename_lift (ρ : Nat → Nat) (t : Tm) :
    rename (upRen ρ) (lift t) = lift (rename ρ t) := by
  simp only [lift, rename_comp]
  apply rename_congr
  intro i
  rfl

theorem rename_subst (ρ : Nat → Nat) (σ : Nat → Tm) (t : Tm) :
    rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t := by
  induction t generalizing ρ σ with
  | var i => rfl
  | app f a ihf iha => simp [rename, subst, ihf, iha]
  | lam b ih =>
    simp only [rename, subst]
    rw [ih]
    apply congrArg Tm.lam
    apply subst_congr
    intro i
    cases i with
    | zero => rfl
    | succ i => exact rename_lift ρ (σ i)

theorem subst_rename (σ : Nat → Tm) (ρ : Nat → Nat) (t : Tm) :
    subst σ (rename ρ t) = subst (σ ∘ ρ) t := by
  induction t generalizing σ ρ with
  | var i => rfl
  | app f a ihf iha => simp [rename, subst, ihf, iha]
  | lam b ih =>
    simp only [rename, subst]
    rw [ih]
    apply congrArg Tm.lam
    apply subst_congr
    intro i
    cases i <;> rfl

theorem subst_lift (σ : Nat → Tm) (t : Tm) :
    subst (upSub σ) (lift t) = lift (subst σ t) := by
  rw [lift, subst_rename, lift, rename_subst]
  apply subst_congr
  intro i
  rfl

theorem subst_comp (σ τ : Nat → Tm) (t : Tm) :
    subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  induction t generalizing σ τ with
  | var i => rfl
  | app f a ihf iha => simp [subst, ihf, iha]
  | lam b ih =>
    simp only [subst]
    rw [ih]
    apply congrArg Tm.lam
    apply subst_congr
    intro i
    cases i with
    | zero => rfl
    | succ i => exact subst_lift τ (σ i)

@[simp] theorem rename_subst_single (ρ : Nat → Nat) (t x : Tm) :
    rename ρ (subst (fun | 0 => x | i + 1 => .var i) t) =
      subst (fun | 0 => rename ρ x | i + 1 => .var (ρ i)) t := by
  rw [rename_subst]
  apply subst_congr
  intro i
  cases i <;> rfl

end ProjectBeth.Syntax.Untyped
