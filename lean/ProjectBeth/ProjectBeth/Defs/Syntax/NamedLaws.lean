import ProjectBeth.Defs.Syntax.LocallyNamelessLaws

universe u v w

namespace ProjectBeth.Syntax.Named

variable {Name : Type u} {Name' : Type v} {Name'' : Type w}

def rename (f : Name → Name') : Tm Name → Tm Name'
  | .var x => .var (f x)
  | .app p q => .app (rename f p) (rename f q)
  | .lam x b => .lam (f x) (rename f b)

@[simp] theorem rename_id (t : Tm Name) : rename id t = t := by
  induction t with
  | var => rfl
  | app p q ihp ihq => simp [rename, ihp, ihq]
  | lam x b ih => simp [rename, ih]

theorem rename_comp (f : Name → Name') (g : Name' → Name'') (t : Tm Name) :
    rename g (rename f t) = rename (g ∘ f) t := by
  induction t with
  | var => rfl
  | app p q ihp ihq => simp [rename, ihp, ihq]
  | lam x b ih => simp [rename, ih]

theorem alpha_iff_aconv [DecidableEq Name] {t u : Tm Name} :
    Alpha t u ↔ aconv t u = true := aconv_correct.symm

theorem aconv_invariant_of_alpha [DecidableEq Name] {t u t' u' : Tm Name}
    (ht : Alpha t t') (hu : Alpha u u') : aconv t u = aconv t' u' := by
  apply Bool.eq_iff_iff.mpr
  simp only [aconv_correct]
  exact ⟨fun h => ht.symm.trans (h.trans hu), fun h => ht.trans (h.trans hu.symm)⟩

end ProjectBeth.Syntax.Named
