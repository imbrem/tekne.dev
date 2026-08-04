import ProjectBeth.Defs.HOLOmega.Kernel

universe u v

namespace ProjectBeth.HOLOmega.Kernel.ConstantDomain

open ProjectBeth.HOLOmega.Kernel

variable (U : Universe) (D : Type v)

structure Quotation where
  quote : ∀ A : U.Code, U.El A → D

namespace Quotation

def Per (Q : Quotation U D) (A : U.Code) (x y : D) : Prop :=
  ∃ a : U.El A, x = Q.quote A a ∧ y = Q.quote A a

theorem per_refl (Q : Quotation U D) (A : U.Code) (a : U.El A) :
    Per U D Q A (Q.quote A a) (Q.quote A a) := ⟨a, rfl, rfl⟩

theorem per_symm (Q : Quotation U D) (A : U.Code) {x y : D} :
    Per U D Q A x y → Per U D Q A y x := by
  rintro ⟨a, rfl, rfl⟩
  exact per_refl U D Q A a

theorem per_trans (Q : Quotation U D) (A : U.Code) {x y z : D} :
    Per U D Q A x y → Per U D Q A y z → Per U D Q A x z := by
  rintro ⟨a, rfl, rfl⟩ ⟨b, h, rfl⟩
  exact ⟨a, rfl, h.symm⟩

def term {Δ} {Γ : Ctx U Δ} {A : Ty U Δ .star}
    (Q : Quotation U D) (t : Tm U Γ A) :
    ∀ ρ, Ctx.El U Γ ρ → D :=
  fun ρ γ => Q.quote (A ρ) (t ρ γ)

/-- The fundamental PER theorem for the post-evaluation erasure.  It applies to
every shallow-intrinsic HOLω term, independently of the term former used. -/
theorem fundamental {Δ} {Γ : Ctx U Δ} {A : Ty U Δ .star}
    (Q : Quotation U D) (t : Tm U Γ A) (ρ γ) :
    Per U D Q (A ρ) (term U D Q t ρ γ) (term U D Q t ρ γ) :=
  per_refl U D Q _ _

theorem eq_sound {Δ} {Γ : Ctx U Δ} {A : Ty U Δ .star}
    (Q : Quotation U D) {t s : Tm U Γ A} (h : EqTm U Γ t s) (ρ γ) :
    term U D Q t ρ γ = term U D Q s ρ γ := by
  rw [h.sound U]

theorem eq_per {Δ} {Γ : Ctx U Δ} {A : Ty U Δ .star}
    (Q : Quotation U D) {t s : Tm U Γ A} (h : EqTm U Γ t s) (ρ γ) :
    Per U D Q (A ρ) (term U D Q t ρ γ) (term U D Q s ρ γ) := by
  rw [h.sound U]
  exact fundamental U D Q s ρ γ

def TrueCode (Q : Quotation U D) : D :=
  Q.quote U.boolCode (U.boolEquiv.symm true)

/-- Exactly the additional assumption needed to reflect truth from the
constant domain back into the typed Boolean carrier. -/
structure ReflectsBool (Q : Quotation U D) : Prop where
  reflects : ∀ b, Q.quote U.boolCode b = TrueCode U D Q → U.boolEquiv b = true

theorem derives_true_of_reflection {Δ} {Γ : Ctx U Δ}
    (Q : Quotation U D) (R : ReflectsBool U D Q)
    {H : List (Tm U Γ (Ty.boolCode U))}
    {p : Tm U Γ (Ty.boolCode U)} (h : Derives U H p) (ρ γ)
    (hH : ∀ q ∈ H, term U D Q q ρ γ = TrueCode U D Q) :
    term U D Q p ρ γ = TrueCode U D Q := by
  apply congrArg (Q.quote U.boolCode)
  apply U.boolEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply h.sound U ρ γ
  intro q hq
  exact R.reflects _ (hH q hq)

/-- Compositional constant-domain interpretation.  Arrow and Boolean laws are
needed for HOL.  The `all_*` fields isolate the extra parametricity demanded by
HOLω type abstraction/application; they are not consequences of bare PERs. -/
structure Compositional (Q : Quotation U D) where
  app : D → D → D
  lam : (D → D) → D
  bool : Bool → D
  app_quote : ∀ A B (f : U.El (U.arr A B)) (x : U.El A),
    app (Q.quote _ f) (Q.quote _ x) =
      Q.quote B (U.arrEquiv A B f x)
  lam_quote : ∀ A B (f : U.El A → U.El B),
    ∃ fd : D → D, (∀ a, fd (Q.quote A a) = Q.quote B (f a)) ∧
      lam fd = Q.quote (U.arr A B) ((U.arrEquiv A B).symm f)
  bool_quote : ∀ b, bool b = Q.quote U.boolCode (U.boolEquiv.symm b)
  allApp : ∀ (I : Type u) (F : I → U.Code), D → I → D
  allLam : ∀ (I : Type u) (F : I → U.Code), (I → D) → D
  allApp_quote : ∀ (I : Type u) (F : I → U.Code)
      (f : (X : I) → U.El (F X)) (X : I),
    allApp I F
        (Q.quote (U.allCode I F) ((U.allEquiv I F).symm f)) X =
      Q.quote (F X) (f X)
  allLam_quote : ∀ (I : Type u) (F : I → U.Code)
      (f : (X : I) → U.El (F X)),
    allLam I F (fun X => Q.quote (F X) (f X)) =
      Q.quote (U.allCode I F) ((U.allEquiv I F).symm f)

end Quotation

end ProjectBeth.HOLOmega.Kernel.ConstantDomain
