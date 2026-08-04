import ProjectBeth.Defs.HOL.Entailment

namespace ProjectBeth.HOL.Kernel

noncomputable section

def Ren.id : Ren Γ Γ := fun v => v
def Ren.comp (τ : Ren Δ Θ) (σ : Ren Γ Δ) : Ren Γ Θ := fun v => τ (σ v)

theorem Ren.lift_id {A : Ty} :
    (Ren.lift (A := A) (Ren.id : Ren Γ Γ) : Ren (A :: Γ) (A :: Γ)) =
      (Ren.id : Ren (A :: Γ) (A :: Γ)) := by
  funext _ v
  cases v <;> rfl

theorem Ren.lift_comp {A : Ty} (τ : Ren Δ Θ) (σ : Ren Γ Δ) :
    (Ren.lift (A := A) (Ren.comp τ σ) : Ren (A :: Γ) (A :: Θ)) =
      (Ren.comp (Ren.lift (A := A) τ) (Ren.lift (A := A) σ) :
        Ren (A :: Γ) (A :: Θ)) := by
  funext _ v
  cases v <;> rfl

@[simp] theorem Tm.rename_id (t : Tm Γ A) : Tm.rename Ren.id t = t := by
  induction t with
  | var => rfl
  | app f x ihf ihx => simp [Tm.rename, ihf, ihx]
  | lam t ih => rw [Tm.rename, Ren.lift_id, ih]
  | bool => rfl
  | conj p q ihp ihq => simp [Tm.rename, ihp, ihq]
  | eq x y ihx ihy => simp [Tm.rename, ihx, ihy]
  | epsilon p ih => simp [Tm.rename, ih]
  | abs P x ih => simp [Tm.rename, ih]
  | rep P x ih => simp [Tm.rename, ih]

theorem Tm.rename_comp (t : Tm Γ A) (σ : Ren Γ Δ) (τ : Ren Δ Θ) :
    Tm.rename τ (Tm.rename σ t) = Tm.rename (Ren.comp τ σ) t := by
  induction t generalizing Δ Θ with
  | var => rfl
  | app f x ihf ihx => simp [Tm.rename, ihf, ihx]
  | lam t ih =>
    simp only [Tm.rename]
    rw [ih, Ren.lift_comp]
  | bool => rfl
  | conj p q ihp ihq => simp [Tm.rename, ihp, ihq]
  | eq x y ihx ihy => simp [Tm.rename, ihx, ihy]
  | epsilon p ih => simp [Tm.rename, ih]
  | abs P x ih => simp [Tm.rename, ih]
  | rep P x ih => simp [Tm.rename, ih]

def Sub.id : Sub Γ Γ := fun v => .var v

theorem Sub.lift_id {A : Ty} :
    (Sub.lift (A := A) (Sub.id : Sub Γ Γ) : Sub (A :: Γ) (A :: Γ)) =
      (Sub.id : Sub (A :: Γ) (A :: Γ)) := by
  funext _ v
  cases v <;> rfl

@[simp] theorem Tm.subst_id (t : Tm Γ A) : Tm.subst Sub.id t = t := by
  induction t with
  | var => rfl
  | app f x ihf ihx => simp [Tm.subst, ihf, ihx]
  | lam t ih => rw [Tm.subst, Sub.lift_id, ih]
  | bool => rfl
  | conj p q ihp ihq => simp [Tm.subst, ihp, ihq]
  | eq x y ihx ihy => simp [Tm.subst, ihx, ihy]
  | epsilon p ih => simp [Tm.subst, ih]
  | abs P x ih => simp [Tm.subst, ih]
  | rep P x ih => simp [Tm.subst, ih]

def Ren.toSub (σ : Ren Γ Δ) : Sub Γ Δ := fun v => .var (σ v)

theorem Ren.toSub_lift {A : Ty} (σ : Ren Γ Δ) :
    (Ren.toSub (Ren.lift (A := A) σ) : Sub (A :: Γ) (A :: Δ)) =
      (Sub.lift (A := A) (Ren.toSub σ) : Sub (A :: Γ) (A :: Δ)) := by
  funext _ v
  cases v <;> rfl

theorem Tm.subst_toSub (t : Tm Γ A) (σ : Ren Γ Δ) :
    Tm.subst (Ren.toSub σ) t = Tm.rename σ t := by
  induction t generalizing Δ with
  | var => rfl
  | app f x ihf ihx => simp [Tm.subst, Tm.rename, ihf, ihx]
  | lam t ih =>
    rw [Tm.subst, Tm.rename]
    rw [← Ren.toSub_lift, ih]
  | bool => rfl
  | conj p q ihp ihq => simp [Tm.subst, Tm.rename, ihp, ihq]
  | eq x y ihx ihy => simp [Tm.subst, Tm.rename, ihx, ihy]
  | epsilon p ih => simp [Tm.subst, Tm.rename, ih]
  | abs P x ih => simp [Tm.subst, Tm.rename, ih]
  | rep P x ih => simp [Tm.subst, Tm.rename, ih]

theorem Tm.eval_rename_square (t : Tm Γ A) (σ : Ren Γ Δ) (ρ : Env Δ) :
    (Tm.rename σ t).eval ρ = t.eval (Ren.env σ ρ) := Tm.eval_rename t σ ρ

theorem Tm.eval_subst_square (t : Tm Γ A) (σ : Sub Γ Δ) (ρ : Env Δ) :
    (Tm.subst σ t).eval ρ = t.eval (Sub.env σ ρ) := Tm.eval_subst t σ ρ

theorem Tm.eval_rename_comp_square (t : Tm Γ A) (σ : Ren Γ Δ)
    (τ : Ren Δ Θ) (ρ : Env Θ) :
    (Tm.rename τ (Tm.rename σ t)).eval ρ =
      t.eval (Ren.env σ (Ren.env τ ρ)) := by
  rw [Tm.eval_rename, Tm.eval_rename]

end

end ProjectBeth.HOL.Kernel
