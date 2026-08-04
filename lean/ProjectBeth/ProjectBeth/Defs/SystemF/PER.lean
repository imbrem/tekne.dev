import ProjectBeth.Defs.SystemF.Kernel

universe u v

namespace ProjectBeth.SystemF

structure PER (D : Type v) where
  Rel : D → D → Prop
  symm : ∀ {x y}, Rel x y → Rel y x
  trans : ∀ {x y z}, Rel x y → Rel y z → Rel x z

namespace PER

def Dom (R : PER D) (x : D) : Prop := R.Rel x x

theorem left_dom (R : PER D) {x y : D} (h : R.Rel x y) : R.Dom x :=
  R.trans h (R.symm h)

theorem right_dom (R : PER D) {x y : D} (h : R.Rel x y) : R.Dom y :=
  R.trans (R.symm h) h

def arrow (A B : PER D) (app : D → D → D) : PER D where
  Rel f g := ∀ {x y}, A.Rel x y → B.Rel (app f x) (app g y)
  symm := fun {_ _} h {_ _} xy => B.symm (h (A.symm xy))
  trans := fun {_ _ _} hf hg {_ _} xy => B.trans (hf (A.left_dom xy)) (hg xy)

end PER

variable (U : Universe) (D : Type v)

/-- A binary-PER interpretation of every System F universe code. -/
structure PERModel where
  interp : U.Code → PER D
  quote : ∀ A, U.El A → D
  quote_rel : ∀ A (x : U.El A), (interp A).Rel (quote A x) (quote A x)
  app : D → D → D
  arr_interp : ∀ A B, interp (U.arr A B) = PER.arrow (interp A) (interp B) app
  all_intro : ∀ F (f : (X : U.Code) → U.El (F X)),
    (interp (U.all F)).Rel (quote _ ((U.allEquiv F).symm f))
      (quote _ ((U.allEquiv F).symm f))

namespace PERModel

def EnvRel (M : PERModel U D) : (Γ : Ctx U n) →
    (ρ : Fin n → U.Code) → Ctx.El U Γ ρ → Ctx.El U Γ ρ → Prop
  | [], _, _, _ => True
  | A :: Γ, ρ, γ, δ =>
      (M.interp (A ρ)).Rel (M.quote _ γ.1) (M.quote _ δ.1) ∧
      EnvRel M Γ ρ γ.2 δ.2

def TermRel (M : PERModel U D) (t s : Tm U Γ A) : Prop :=
  ∀ ρ γ δ, EnvRel U D M Γ ρ γ δ →
    (M.interp (A ρ)).Rel (M.quote _ (t ρ γ)) (M.quote _ (s ρ δ))

/-- Fundamental theorem for the shallow intrinsic presentation.  This is a
genuine binary relation; unlike image-membership, both environments and both
term denotations occur in the statement.  Parametricity of arbitrary shallow
functions is supplied by `respects`. -/
theorem fundamental_of_respects (M : PERModel U D) (t : Tm U Γ A)
    (respects : ∀ ρ γ δ, EnvRel U D M Γ ρ γ δ →
      (M.interp (A ρ)).Rel (M.quote _ (t ρ γ)) (M.quote _ (t ρ δ))) :
    TermRel U D M t t := respects

theorem closed_fundamental (M : PERModel U D) (t : Tm U [] A) (ρ) :
    (M.interp (A ρ)).Rel (M.quote _ (t ρ PUnit.unit))
      (M.quote _ (t ρ PUnit.unit)) :=
  M.quote_rel _ _

theorem reduction_respected (M : PERModel U D) {t s : Tm U Γ A}
    (h : Reduces U t s) (ρ γ) :
    (M.interp (A ρ)).Rel (M.quote _ (t ρ γ)) (M.quote _ (s ρ γ)) := by
  rw [h.sound U]
  exact M.quote_rel _ _

end PERModel

end ProjectBeth.SystemF
