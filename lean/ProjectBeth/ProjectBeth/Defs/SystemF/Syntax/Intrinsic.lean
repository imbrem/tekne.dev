import ProjectBeth.Defs.SystemF.Syntax.Bounded

namespace ProjectBeth.SystemF.Syntax.Intrinsic

/-- The proof-relevant intrinsic representation supplied by the shared kernel. -/
abbrev Tm := Inductive.Typed
abbrev Step {Δ : Nat} {Γ : List Inductive.Ty} {A : Inductive.Ty} :=
  @Inductive.TypedStep Δ Γ A

def erase (t : Tm Δ Γ A) : Inductive.Tm := t.term

@[simp] theorem erase_mk (t : Inductive.Tm) (d : Inductive.HasType Δ Γ t A) :
    erase ⟨t, d⟩ = t := rfl

/-- Intrinsic renaming commutes with erasure to the raw generic hub. -/
def rename (r : Inductive.Semantics.CtxRen Γ Γ' ρ) (t : Tm Δ Γ A) : Tm Δ Γ' A :=
  ⟨t.term.rename ρ, by
    obtain ⟨d⟩ := Inductive.Semantics.derivation_of_hasType t.typing
    exact (d.renameTm r).toHasType⟩

@[simp] theorem erase_rename (r : Inductive.Semantics.CtxRen Γ Γ' ρ) (t : Tm Δ Γ A) :
    erase (rename r t) = (erase t).rename ρ := rfl

/-- Intrinsic substitution commutes with erasure to the raw generic hub. -/
def subst (s : Inductive.Semantics.CtxSub Δ Γ Γ' σ) (t : Tm Δ Γ A) : Tm Δ Γ' A :=
  ⟨t.term.subst σ, by
    obtain ⟨d⟩ := Inductive.Semantics.derivation_of_hasType t.typing
    exact (d.substTm s).toHasType⟩

@[simp] theorem erase_subst (s : Inductive.Semantics.CtxSub Δ Γ Γ' σ) (t : Tm Δ Γ A) :
    erase (subst s t) = (erase t).subst σ := rfl

end ProjectBeth.SystemF.Syntax.Intrinsic
