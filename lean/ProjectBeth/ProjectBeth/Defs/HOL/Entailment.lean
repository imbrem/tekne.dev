import ProjectBeth.Defs.HOL.Contexts

namespace ProjectBeth.HOL.Kernel

noncomputable section
attribute [local instance] Classical.propDecidable

universe u

def Extend (Assume : Tm Γ Ty.bool → Prop) (p : Tm Γ Ty.bool) :=
  fun q => Assume q ∨ q = p

inductive Derives : (Tm Γ Ty.bool → Prop) → Tm Γ Ty.bool → Type (u + 1)
  | assumption {Assume : Tm Γ Ty.bool → Prop} (p) : Assume p → Derives Assume p
  | truth {Assume : Tm Γ Ty.bool → Prop} : Derives Assume (.bool true)
  | eqRefl {Assume : Tm Γ Ty.bool → Prop} (x : Tm Γ A) : Derives Assume (.eq x x)
  | eqv {Assume : Tm Γ Ty.bool → Prop} (h : Eqv x y) : Derives Assume (.eq x y)
  | eqMp {Assume : Tm Γ Ty.bool → Prop} (p q : Tm Γ Ty.bool) :
      Derives Assume (.eq p q) → Derives Assume p → Derives Assume q
  | deductAntisymm {Assume : Tm Γ Ty.bool → Prop} (p q : Tm Γ Ty.bool) :
      Derives (Extend Assume p) q → Derives (Extend Assume q) p →
      Derives Assume (.eq p q)
  | choice {Assume : Tm Γ Ty.bool → Prop} (pred : Tm Γ (A.arr Ty.bool)) (x : Tm Γ A) :
      Derives Assume (.app pred x) → Derives Assume (.app pred (.epsilon pred))
  | conjIntro {Assume : Tm Γ Ty.bool → Prop} (p q) : Derives Assume p → Derives Assume q → Derives Assume (.conj p q)
  | conjLeft {Assume : Tm Γ Ty.bool → Prop} (p q) : Derives Assume (.conj p q) → Derives Assume p
  | conjRight {Assume : Tm Γ Ty.bool → Prop} (p q) : Derives Assume (.conj p q) → Derives Assume q
  | transport {Assume Assume' : Tm Γ Ty.bool → Prop} :
      (∀ r, Assume r → Assume' r) → Derives Assume p → Derives Assume' p
  | contextChange {Assume Assume' : Tm Γ Ty.bool → Prop} :
      (∀ ρ, (∀ r, Assume' r → r.IsTrue ρ) → ∀ r, Assume r → r.IsTrue ρ) →
      Derives Assume p → Derives Assume' p

def Valid (Assume : Tm Γ Ty.bool → Prop) (p : Tm Γ Ty.bool) : Prop :=
  ∀ ρ, (∀ q, Assume q → q.IsTrue ρ) → p.IsTrue ρ

theorem isTrue_eq_of_eqv {Γ : Ctx} {A : Ty} {x y : Tm Γ A}
    (h : Eqv x y) (ρ : Env Γ) :
    (Tm.eq x y).IsTrue ρ :=
  (Tm.isTrue_eq x y ρ).2 (h.valid ρ)

theorem Derives.valid {Assume : Tm Γ Ty.bool → Prop} {p : Tm Γ Ty.bool}
    (d : Derives Assume p) : Valid Assume p := by
  induction d with
  | assumption p hp => exact fun ρ hρ => hρ p hp
  | truth => intro ρ hρ; simp [Tm.IsTrue, Tm.eval]
  | eqRefl x => intro ρ hρ; exact (Tm.isTrue_eq x x ρ).2 rfl
  | eqv h => intro ρ hρ; exact isTrue_eq_of_eqv h ρ
  | eqMp p q de dp ihe ihp =>
    intro ρ hρ
    have he := (Tm.isTrue_eq p q ρ).1 (ihe ρ hρ)
    simpa [Tm.IsTrue, he] using ihp ρ hρ
  | deductAntisymm p q dq dp ihq ihp =>
    intro ρ hρ
    apply (Tm.isTrue_eq p q ρ).2
    apply uliftBool_ext
    cases hpv : (p.eval ρ).down <;> cases hqv : (q.eval ρ).down
    · rfl
    · have bad := ihp ρ (fun r hr => by
        rcases hr with hr | rfl
        · exact hρ r hr
        · simp [Tm.IsTrue, hqv])
      simp [Tm.IsTrue, hpv] at bad
    · have bad := ihq ρ (fun r hr => by
        rcases hr with hr | rfl
        · exact hρ r hr
        · simp [Tm.IsTrue, hpv])
      simp [Tm.IsTrue, hqv] at bad
    · rfl
  | choice pred x dx ih =>
    intro ρ hρ
    have hx := ih ρ hρ
    simp only [Tm.IsTrue, Tm.eval] at hx ⊢
    split
    · rename_i h
      exact Classical.choose_spec h
    · rename_i h
      exact False.elim (h ⟨x.eval ρ, hx⟩)
  | conjIntro p q dp dq ihp ihq =>
    intro ρ hρ
    exact (Tm.isTrue_conj p q ρ).2 ⟨ihp ρ hρ, ihq ρ hρ⟩
  | conjLeft p q d ih =>
    intro ρ hρ
    exact (Tm.isTrue_conj p q ρ).1 (ih ρ hρ) |>.1
  | conjRight p q d ih =>
    intro ρ hρ
    exact (Tm.isTrue_conj p q ρ).1 (ih ρ hρ) |>.2
  | transport h d ih => exact fun ρ hρ => ih ρ (fun q hq => hρ q (h q hq))
  | contextChange h d ih => exact fun ρ hρ => ih ρ (h ρ hρ)

def Derives.map {Assume Assume' : Tm Γ Ty.bool → Prop} (h : ∀ r, Assume r → Assume' r) :
    Derives Assume p → Derives Assume' p :=
  Derives.transport h

abbrev HOLLightDerives (C : HOLLightContext Γ) := Derives C.Mem
abbrev HOL4Derives (C : HOL4Context Γ) := Derives (fun p => AssumptionTree.Mem p C)
abbrev ConjDerives (c : ConjContext Γ) := Derives (fun p => p = c)

noncomputable def HOLLightDerives.toHOL4 {C : HOLLightContext Γ} :
    HOLLightDerives C p → HOL4Derives C.toTree p :=
  Derives.map (fun p hp => C.mem_toTree p |>.2 hp)

noncomputable def HOL4Derives.toHOLLight {C : HOLLightContext Γ} :
    HOL4Derives C.toTree p → HOLLightDerives C p :=
  Derives.map (fun p hp => C.mem_toTree p |>.1 hp)

def HOL4Derives.toConj {C : HOL4Context Γ} :
    HOL4Derives C p → ConjDerives C.foldConj p := fun d =>
  .contextChange (fun ρ hfold q hq =>
    (AssumptionTree.isTrue_foldConj C ρ).1 (hfold _ rfl) q hq) d

def ConjDerives.toHOL4 {C : HOL4Context Γ} :
    ConjDerives C.foldConj p → HOL4Derives C p := fun d =>
  .contextChange (fun ρ htree q hq => by
    cases hq
    exact (AssumptionTree.isTrue_foldConj C ρ).2 (fun r hr => htree r hr)) d

theorem holLight_hol4_derivable_iff (C : HOLLightContext Γ) (p : Tm Γ Ty.bool) :
    Nonempty (HOLLightDerives C p) ↔ Nonempty (HOL4Derives C.toTree p) :=
  ⟨fun ⟨d⟩ => ⟨d.toHOL4⟩, fun ⟨d⟩ => ⟨d.toHOLLight⟩⟩

theorem hol4_conj_derivable_iff (C : HOL4Context Γ) (p : Tm Γ Ty.bool) :
    Nonempty (HOL4Derives C p) ↔ Nonempty (ConjDerives C.foldConj p) :=
  ⟨fun ⟨d⟩ => ⟨d.toConj⟩, fun ⟨d⟩ => ⟨d.toHOL4⟩⟩

theorem HOLLightDerives.valid_semantics {C : HOLLightContext Γ}
    (d : HOLLightDerives C p) (ρ : Env Γ) (hC : C.holds ρ) : p.IsTrue ρ :=
  d.valid ρ hC

theorem HOL4Derives.valid_semantics {C : HOL4Context Γ}
    (d : HOL4Derives C p) (ρ : Env Γ) (hC : C.holds ρ) : p.IsTrue ρ :=
  d.valid ρ hC

theorem ConjDerives.valid_semantics {c : ConjContext Γ}
    (d : ConjDerives c p) (ρ : Env Γ) (hc : c.holds ρ) : p.IsTrue ρ :=
  d.valid ρ (fun q hq => by cases hq; exact hc)

end


end ProjectBeth.HOL.Kernel
