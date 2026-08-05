import ProjectBeth.Defs.HOLOmega.Syntax.Levels
import ProjectBeth.Defs.Translations

/-! The HOL inclusion factored through the single-index HOLω presentation. -/

universe u
namespace ProjectBeth.HOLOmega.Syntax.HOLBridge

variable {Base : Type u}

def ty (A : HOL.Ty Base) : Indexed.Ty Base :=
  Indexed.ofLegacyTy (Translations.HOLToOmega.ty A)

def tm (t : HOL.Tm Base) : Indexed.Tm Base :=
  Indexed.ofLegacyTm (Translations.HOLToOmega.tm t)

@[simp] theorem ty_legacy_square (A : HOL.Ty Base) :
    (ty A).toLegacy = Translations.HOLToOmega.ty A := by simp [ty]

@[simp] theorem tm_legacy_square (t : HOL.Tm Base) :
    (tm t).toLegacy = Translations.HOLToOmega.tm t := by simp [tm]

theorem wf_square (h : HOL.Ty.Wf A) : Indexed.Kinded [] (ty A) .star := by
  rw [Indexed.kinded_legacy_iff, ty_legacy_square]
  exact Translations.HOLToOmega.wf h

theorem typing_square (h : HOL.HasType Γ t A) :
    Indexed.HasType [] (Γ.map ty) (tm t) (ty A) := by
  rw [Indexed.hasType_legacy_iff, tm_legacy_square, ty_legacy_square]
  have ht := Translations.HOLToOmega.hasType h
  simpa [ty, List.map_map, Function.comp_def] using ht

@[simp] theorem ty_rename_square (A : HOL.Ty Base) (ρ : Nat → Nat) :
    ((ty A).rename ρ).toLegacy = (Translations.HOLToOmega.ty A).rename ρ := by
  simp [ty]

@[simp] theorem tm_rename_square (t : HOL.Tm Base) (ρ : Nat → Nat) :
    ((tm t).rename ρ).toLegacy = (Translations.HOLToOmega.tm t).rename ρ := by
  simp [tm]

/-- The old and new routes from HOL to the indexed HOLω judgement coincide;
proof irrelevance turns the commuting proposition square into equality. -/
theorem judgement_square (h : HOL.HasType Γ t A) :
    (typing_square h).toHasType =
      (by simpa [ty, List.map_map, Function.comp_def] using
        Translations.HOLToOmega.hasType h) := Subsingleton.elim _ _

end ProjectBeth.HOLOmega.Syntax.HOLBridge
