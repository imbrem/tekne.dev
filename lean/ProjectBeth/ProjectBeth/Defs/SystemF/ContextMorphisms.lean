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

theorem map_lift_subst (Γ : List Inductive.Ty) (σ : Nat → Inductive.Ty) :
    (Γ.map Inductive.Ty.lift).map (Inductive.Ty.subst (Inductive.upTySub σ)) =
      (Γ.map (Inductive.Ty.subst σ)).map Inductive.Ty.lift := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => simp [ih, Inductive.Ty.subst_lift]

theorem subst_instantiate (A X : Inductive.Ty) (σ : Nat → Inductive.Ty) :
    (A.instantiate X).subst σ =
      (A.subst (Inductive.upTySub σ)).instantiate (X.subst σ) := by
  rw [Inductive.Ty.instantiate, Inductive.Ty.subst_comp,
    Inductive.Ty.instantiate, Inductive.Ty.subst_comp]
  apply Inductive.Ty.subst_congr
  intro i
  cases i with
  | zero => rfl
  | succ i => exact (Inductive.Ty.lift_instantiate (σ i) (X.subst σ)).symm

def Derivation.substTy (σ : Nat → Inductive.Ty) :
    Derivation Δ Γ t A →
      Derivation Δ' (Γ.map (Inductive.Ty.subst σ))
        (t.substTy σ) (A.subst σ)
  | .var h => .var (by simp only [List.getElem?_map]; rw [h]; rfl)
  | .app f x => .app (f.substTy σ) (x.substTy σ)
  | .lam body => .lam (body.substTy σ)
  | .tyApp (X := X) f =>
      ((Derivation.tyApp (X := X.subst σ)
        (f.substTy σ)).castCtx rfl rfl (subst_instantiate _ _ σ).symm)
  | .tyLam body => .tyLam
      ((body.substTy (Inductive.upTySub σ)).castCtx
        (map_lift_subst _ σ) rfl rfl)
  | .bool b => .bool b
  | .nat n => .nat n

def Derivation.changeDepth : Derivation Δ Γ t A → Derivation Δ' Γ t A
  | .var h => .var h
  | .app f x => .app f.changeDepth x.changeDepth
  | .lam body => .lam body.changeDepth
  | .tyApp f => .tyApp f.changeDepth
  | .tyLam body => .tyLam body.changeDepth
  | .bool b => .bool b
  | .nat n => .nat n

/-- A simultaneous, intrinsically typed term substitution. -/
structure CtxSub (Δ : Nat) (Γ Γ' : List Inductive.Ty)
    (σ : Nat → Inductive.Tm) : Type where
  lookup : ∀ {n A}, Γ[n]? = some A → Derivation Δ Γ' (σ n) A

namespace CtxSub

def id (Δ : Nat) (Γ : List Inductive.Ty) : CtxSub Δ Γ Γ Inductive.Tm.var where
  lookup h := .var h

def lift (s : CtxSub Δ Γ Γ' σ) :
    CtxSub Δ (A :: Γ) (A :: Γ') (Inductive.upTmSub σ) where
  lookup := by
    intro n B h
    cases n with
    | zero =>
      simp at h
      subst B
      exact .var rfl
    | succ n =>
      exact (s.lookup (by simpa using h)).renameTm (CtxRen.weaken Γ' A)

def mapLift (s : CtxSub Δ Γ Γ' σ) :
    CtxSub (Δ + 1) (Γ.map Inductive.Ty.lift) (Γ'.map Inductive.Ty.lift)
      (Inductive.liftTmSubTy σ) where
  lookup := by
    intro n A h
    simp only [List.getElem?_map] at h
    cases hn : Γ[n]? with
    | none => simp [hn] at h
    | some B =>
      simp [hn] at h
      subst A
      exact (s.lookup hn |>.renameTy Nat.succ |>.changeDepth (Δ' := Δ + 1) |>.castCtx
        (by induction Γ' with
          | nil => rfl
          | cons C Γ' ih => simp [Inductive.Ty.lift, ih])
        rfl rfl)

end CtxSub

def Derivation.substTm (s : CtxSub Δ Γ Γ' σ) :
    Derivation Δ Γ t A → Derivation Δ Γ' (t.subst σ) A
  | .var h => s.lookup h
  | .app f x => .app (f.substTm s) (x.substTm s)
  | .lam body => .lam (body.substTm s.lift)
  | .tyApp f => .tyApp (f.substTm s)
  | .tyLam body => .tyLam (body.substTm s.mapLift)
  | .bool b => .bool b
  | .nat n => .nat n

@[simp] theorem Derivation.renameTm_term (d : Derivation Δ Γ t A)
    (r : CtxRen Γ Γ' ρ) : (d.renameTm r).toHasType = (d.renameTm r).toHasType := rfl

end ProjectBeth.SystemF.Inductive.Semantics
