import ProjectBeth.Defs.Syntax.Substitution

namespace ProjectBeth.Syntax.Bounded

def liftRen (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

def rename (ρ : Fin n → Fin m) : Tm n → Tm m
  | .var i => .var (ρ i)
  | .app p q => .app (rename ρ p) (rename ρ q)
  | .lam b => .lam (rename (liftRen ρ) b)

theorem liftRen_id : liftRen (fun i : Fin n => i) = id := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem liftRen_comp (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    liftRen (τ ∘ ρ) = liftRen τ ∘ liftRen ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem rename_id (t : Tm n) : rename id t = t := by
  induction t with
  | var => rfl
  | app p q ihp ihq => simp [rename, ihp, ihq]
  | lam b ih =>
    simp only [rename]
    rw [show liftRen (fun i : Fin _ => id i) = id from liftRen_id, ih]

theorem rename_comp (ρ : Fin n → Fin m) (τ : Fin m → Fin k) (t : Tm n) :
    rename τ (rename ρ t) = rename (τ ∘ ρ) t := by
  induction t generalizing m k with
  | var => rfl
  | app p q ihp ihq => simp [rename, ihp, ihq]
  | lam b ih =>
    simp only [rename]
    rw [ih, liftRen_comp]

def liftSub (σ : Fin n → Tm m) : Fin (n + 1) → Tm (m + 1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

def subst (σ : Fin n → Tm m) : Tm n → Tm m
  | .var i => σ i
  | .app p q => .app (subst σ p) (subst σ q)
  | .lam b => .lam (subst (liftSub σ) b)

theorem liftSub_var : liftSub (fun i : Fin n => .var i) = fun i => .var i := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem subst_var (t : Tm n) : subst (fun i => .var i) t = t := by
  induction t with
  | var => rfl
  | app p q ihp ihq => simp [subst, ihp, ihq]
  | lam b ih => simp only [subst]; rw [liftSub_var, ih]

def eraseRen (ρ : Fin n → Fin m) (i : Nat) : Nat :=
  if h : i < n then (ρ ⟨i, h⟩).val else i

@[simp] theorem eraseRen_fin (ρ : Fin n → Fin m) (i : Fin n) :
    eraseRen ρ i = (ρ i).val := by simp [eraseRen, i.isLt]

end ProjectBeth.Syntax.Bounded
