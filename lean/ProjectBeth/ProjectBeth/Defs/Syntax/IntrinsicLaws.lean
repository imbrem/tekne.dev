import ProjectBeth.Defs.Syntax.BoundedLaws

universe u

namespace ProjectBeth.Syntax.Intrinsic

abbrev Ren {Base : Type u} (Γ Δ : List (Ty Base)) :=
  ∀ {A}, STLC.Var Γ A → STLC.Var Δ A

def liftRen (ρ : Ren Γ Δ) : Ren (A :: Γ) (A :: Δ)
  | _, .here => .here
  | _, .there v => .there (ρ v)

def rename (ρ : Ren Γ Δ) : Tm Γ A → Tm Δ A
  | .var v => .var (ρ v)
  | .app p q => .app (rename ρ p) (rename ρ q)
  | .lam b => .lam (rename (liftRen ρ) b)

theorem rename_congr {ρ τ : Ren Γ Δ} (h : ∀ {A} (v : STLC.Var Γ A), ρ v = τ v)
    (t : Tm Γ A) : rename ρ t = rename τ t := by
  induction t generalizing Δ with
  | var v => simp [rename, h v]
  | app p q ihp ihq => simp [rename, ihp h, ihq h]
  | lam b ih =>
    simp only [rename]
    congr 1
    apply ih
    intro B v
    cases v with
    | here => rfl
    | there v => simp [liftRen, h v]

@[simp] theorem rename_id (t : Tm Γ A) : rename (fun v => v) t = t := by
  induction t with
  | var => rfl
  | app p q ihp ihq => simp [rename, ihp, ihq]
  | lam b ih =>
    simp only [rename]
    congr 1
    calc
      rename (liftRen (fun v => v)) b = rename (fun v => v) b := by
        apply rename_congr
        intro B v
        cases v <;> rfl
      _ = b := ih

theorem rename_comp (t : Tm Γ A) (ρ : Ren Γ Δ) (τ : Ren Δ Θ) :
    rename τ (rename ρ t) = rename (fun v => τ (ρ v)) t := by
  induction t generalizing Δ Θ with
  | var => rfl
  | app p q ihp ihq => simp [rename, ihp, ihq]
  | lam b ih =>
    simp only [rename]
    congr 1
    rw [ih (Δ := _ :: Δ) (Θ := _ :: Θ)]
    apply rename_congr
    intro B v
    cases v <;> rfl

/-- `r` is the finite-index action underlying the intrinsically typed renaming `ρ`. -/
def RepresentsRen {Base : Type u} {Γ Δ : List (Ty Base)}
    (ρ : Ren Γ Δ) (r : Fin Γ.length → Fin Δ.length) : Prop :=
  ∀ {A} (v : STLC.Var Γ A), r (eraseVar v) = eraseVar (ρ v)

theorem RepresentsRen.lift {Base : Type u} {Γ Δ : List (Ty Base)}
    {ρ : Ren Γ Δ} {r : Fin Γ.length → Fin Δ.length} {A : Ty Base}
    (h : RepresentsRen ρ r) :
    RepresentsRen (liftRen (A := A) ρ) (Bounded.liftRen r) := by
  intro B v
  cases v with
  | here => simp [liftRen, Bounded.liftRen, eraseVar]
  | there v =>
    apply Fin.ext
    simp [liftRen, Bounded.liftRen, eraseVar, h v]

/-- Erasing an intrinsic renaming commutes with the corresponding bounded renaming. -/
theorem erase_rename_of_represents {Base : Type u} {Γ Δ : List (Ty Base)}
    {ρ : Ren Γ Δ} {r : Fin Γ.length → Fin Δ.length} {A : Ty Base}
    (h : RepresentsRen ρ r) (t : Tm Γ A) :
    erase (rename ρ t) = Bounded.rename r (erase t) := by
  induction t generalizing Δ with
  | var v => simp [rename, erase, Bounded.rename, h v]
  | app p q ihp ihq =>
    simp only [rename, erase, Bounded.rename]
    rw [ihp h, ihq h]
  | lam b ih =>
    simp only [rename, erase, Bounded.rename]
    congr 1
    simpa using ih (Δ := _ :: Δ) (RepresentsRen.lift h)

/-- The complete intrinsic-to-untyped translation square. -/
theorem erase_rename_untyped_of_represents {Base : Type u} {Γ Δ : List (Ty Base)}
    {ρ : Ren Γ Δ} {r : Fin Γ.length → Fin Δ.length} {A : Ty Base}
    (h : RepresentsRen ρ r) (t : Tm Γ A) :
    Bounded.erase (erase (rename ρ t)) =
      Untyped.rename (Bounded.eraseRen r) (Bounded.erase (erase t)) := by
  rw [erase_rename_of_represents h, Bounded.erase_rename]

end ProjectBeth.Syntax.Intrinsic
