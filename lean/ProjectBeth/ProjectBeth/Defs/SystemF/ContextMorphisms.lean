import ProjectBeth.Defs.SystemF.Soundness

namespace ProjectBeth.SystemF.Inductive.Semantics

/-- A raw de Bruijn renaming together with the lookup condition that makes it
type preserving between two term contexts. -/
structure CtxRen (Γ Γ' : List Inductive.Ty) (ρ : Nat → Nat) : Prop where
  lookup : ∀ {n A}, Γ[n]? = some A → Γ'[ρ n]? = some A

namespace CtxRen

def id (Γ : List Inductive.Ty) : CtxRen Γ Γ id where
  lookup h := by simpa using h

def comp (r : CtxRen Γ Γ' ρ) (s : CtxRen Γ' Γ'' τ) :
    CtxRen Γ Γ'' (τ ∘ ρ) where
  lookup h := s.lookup (r.lookup h)

def lift (r : CtxRen Γ Γ' ρ) :
    CtxRen (A :: Γ) (A :: Γ') (Inductive.upTmRen ρ) where
  lookup := by
    intro n B h
    cases n with
    | zero => simpa [Inductive.upTmRen, Inductive.upRen] using h
    | succ n => simpa [Inductive.upTmRen, Inductive.upRen] using r.lookup (by simpa using h)

def weaken (Γ : List Inductive.Ty) (A : Inductive.Ty) :
    CtxRen Γ (A :: Γ) Nat.succ where
  lookup h := by simpa using h

def mapLift (r : CtxRen Γ Γ' ρ) :
    CtxRen (Γ.map Inductive.Ty.lift) (Γ'.map Inductive.Ty.lift) ρ where
  lookup := by
    intro n B h
    simp only [List.getElem?_map] at h ⊢
    cases hA : Γ[n]? with
    | none => simp [hA] at h
    | some A =>
      simp [hA] at h
      subst B
      rw [r.lookup hA]
      rfl

end CtxRen

def Derivation.renameTm (r : CtxRen Γ Γ' ρ) :
    Derivation Δ Γ t A → Derivation Δ Γ' (t.rename ρ) A
  | .var h => .var (r.lookup h)
  | .app f x => .app (f.renameTm r) (x.renameTm r)
  | .lam body => .lam (body.renameTm r.lift)
  | .tyApp f => .tyApp (f.renameTm r)
  | .tyLam body => .tyLam (body.renameTm r.mapLift)
  | .bool b => .bool b
  | .nat n => .nat n

def Derivation.castCtx {Δ : Nat} {Γ Γ' : List Inductive.Ty}
    {t t' : Inductive.Tm} {A A' : Inductive.Ty}
    (hΓ : Γ = Γ') (ht : t = t') (hA : A = A') :
    Derivation Δ Γ t A → Derivation Δ Γ' t' A' := by
  subst Γ'; subst t'; subst A'; exact id

theorem map_lift_rename (Γ : List Inductive.Ty) (ρ : Nat → Nat) :
    (Γ.map Inductive.Ty.lift).map (Inductive.Ty.rename (Inductive.upRen ρ)) =
      (Γ.map (Inductive.Ty.rename ρ)).map Inductive.Ty.lift := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => simp [ih, Inductive.Ty.rename_lift]

theorem rename_instantiate (A X : Inductive.Ty) (ρ : Nat → Nat) :
    (A.instantiate X).rename ρ =
      (A.rename (Inductive.upRen ρ)).instantiate (X.rename ρ) := by
  rw [Inductive.Ty.instantiate, Inductive.Ty.rename_subst,
    Inductive.Ty.instantiate, Inductive.Ty.subst_rename]
  apply Inductive.Ty.subst_congr
  intro i
  cases i <;> rfl

def Derivation.renameTy (ρ : Nat → Nat) :
    Derivation Δ Γ t A →
      Derivation Δ (Γ.map (Inductive.Ty.rename ρ)) (t.renameTy ρ) (A.rename ρ)
  | .var h => .var (by simp only [List.getElem?_map]; rw [h]; rfl)
  | .app f x => .app (f.renameTy ρ) (x.renameTy ρ)
  | .lam body => .lam (body.renameTy ρ)
  | .tyApp (X := X) f =>
      ((Derivation.tyApp (X := X.rename ρ) (f.renameTy ρ)).castCtx
        rfl rfl (rename_instantiate _ _ ρ).symm)
  | .tyLam body => .tyLam
      ((body.renameTy (Inductive.upRen ρ)).castCtx
        (map_lift_rename _ ρ) rfl rfl)
  | .bool b => .bool b
  | .nat n => .nat n

@[simp] theorem Derivation.renameTm_term (d : Derivation Δ Γ t A)
    (r : CtxRen Γ Γ' ρ) : (d.renameTm r).toHasType = (d.renameTm r).toHasType := rfl

end ProjectBeth.SystemF.Inductive.Semantics
