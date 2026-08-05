import ProjectBeth.Defs.Syntax.LocallyNamelessLaws

namespace ProjectBeth.Syntax

namespace LocallyNameless

variable {Name Name' : Type*}

theorem indexOf?_eq_none_iff [DecidableEq Name] (x : Name) (Γ : List Name) :
    indexOf? x Γ = none ↔ x ∉ Γ := by
  induction Γ with
  | nil => simp [indexOf?]
  | cons y Γ ih =>
    by_cases h : x = y
    · subst y; simp [indexOf?]
    · simp [indexOf?, h, ih]

theorem indexOf?_get [DecidableEq Name] (Γ : List Name) (hΓ : Γ.Nodup)
    (i : Fin Γ.length) : indexOf? (Γ.get i) Γ = some i := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | cons x Γ ih =>
    cases i using Fin.cases with
    | zero => simp [indexOf?]
    | succ i =>
      have hx : x ∉ Γ := (List.nodup_cons.mp hΓ).1
      have hn := (List.nodup_cons.mp hΓ).2
      have hne : Γ.get i ≠ x := by
        intro h
        apply hx
        rw [← h]
        exact List.get_mem Γ i
      change (if Γ.get i = x then some 0 else
        Option.map Nat.succ (indexOf? (Γ.get i) Γ)) = some (i.val + 1)
      rw [if_neg hne, ih hn i]
      rfl

theorem indexOf?_lt [DecidableEq Name] {x : Name} {Γ : List Name} {i : Nat}
    (h : indexOf? x Γ = some i) : i < Γ.length := by
  induction Γ generalizing i with
  | nil => simp [indexOf?] at h
  | cons y Γ ih =>
    by_cases he : x = y
    · subst y
      simp [indexOf?] at h
      subst i
      simp
    · simp [indexOf?, he] at h
      obtain ⟨j, hj, rfl⟩ := h
      simpa using Nat.succ_lt_succ (ih hj)

/-- Bound indices are below `k`; free variables are unrestricted. -/
def Scoped : Nat → Tm Name → Prop
  | k, .var (.bound i) => i < k
  | _, .var (.free _) => True
  | k, .app p q => Scoped k p ∧ Scoped k q
  | k, .lam b => Scoped (k + 1) b

/-- No free variable of the term is captured by a name in `Γ`. -/
def FreeAway (Γ : List Name) : Tm Name → Prop
  | .var (.bound _) => True
  | .var (.free x) => x ∉ Γ
  | .app p q => FreeAway Γ p ∧ FreeAway Γ q
  | .lam b => FreeAway Γ b

theorem Scoped.mono (h : Scoped k t) (hkl : k ≤ l) : Scoped l t := by
  induction t generalizing k l with
  | var v => cases v <;> simp [Scoped] at h ⊢; exact Nat.lt_of_lt_of_le h hkl
  | app p q ihp ihq => exact ⟨ihp h.1 hkl, ihq h.2 hkl⟩
  | lam b ih => exact ih h (Nat.succ_le_succ hkl)

theorem scoped_ofNamed (Γ : List Name) [DecidableEq Name] (t : Named.Tm Name) :
    Scoped Γ.length (ofNamed Γ t) := by
  induction t generalizing Γ with
  | var x =>
    simp only [ofNamed]
    split
    · rename_i i h
      exact indexOf?_lt h
    · trivial
  | app p q ihp ihq => exact ⟨ihp Γ, ihq Γ⟩
  | lam x b ih =>
    change Scoped (Γ.length + 1) (ofNamed (x :: Γ) b)
    simpa using ih (x :: Γ)

theorem scoped_substFree (t : Tm Name) (h : Scoped k t)
    (σ : Name → Tm Name') (hσ : ∀ x, Scoped k (σ x)) :
    Scoped k (substFree σ t) := by
  induction t generalizing k with
  | var v =>
    cases v with
    | bound i => exact h
    | free x => exact hσ x
  | app p q ihp ihq => exact ⟨ihp h.1 hσ, ihq h.2 hσ⟩
  | lam b ih =>
    apply ih h
    intro x
    exact (hσ x).mono (Nat.le_succ k)

namespace NatReifier

def freeNames : Tm Nat → List Nat
  | .var (.bound _) => []
  | .var (.free x) => [x]
  | .app p q => freeNames p ++ freeNames q
  | .lam b => freeNames b

def listMax : List Nat → Nat
  | [] => 0
  | x :: xs => max x (listMax xs)

theorem le_listMax_of_mem {x : Nat} : ∀ {xs}, x ∈ xs → x ≤ listMax xs
  | [], h => by simp at h
  | y :: ys, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_listMax_of_mem h) (Nat.le_max_right _ _)

def fresh (Γ : List Nat) (t : Tm Nat) : Nat :=
  listMax (Γ ++ freeNames t) + 1

theorem fresh_not_mem_left (Γ : List Nat) (t : Tm Nat) : fresh Γ t ∉ Γ := by
  intro h
  have hle := le_listMax_of_mem (List.mem_append_left (freeNames t) h)
  exact (Nat.not_succ_le_self _ hle)

theorem fresh_not_mem_freeNames (Γ : List Nat) (t : Tm Nat) :
    fresh Γ t ∉ freeNames t := by
  intro h
  have hle := le_listMax_of_mem (List.mem_append_right Γ h)
  exact (Nat.not_succ_le_self _ hle)

def reifyAux (Γ : List Nat) : Tm Nat → Named.Tm Nat
  | .var (.bound i) => .var (Γ.getD i 0)
  | .var (.free x) => .var x
  | .app p q => .app (reifyAux Γ p) (reifyAux Γ q)
  | .lam b =>
      let x := fresh Γ b
      .lam x (reifyAux (x :: Γ) b)

def reify (t : Tm Nat) : Named.Tm Nat := reifyAux [] t

theorem freeAway_iff (Γ : List Nat) (t : Tm Nat) :
    FreeAway Γ t ↔ ∀ x ∈ freeNames t, x ∉ Γ := by
  induction t with
  | var v => cases v <;> simp [FreeAway, freeNames]
  | app p q ihp ihq => simp [FreeAway, freeNames, ihp, ihq, or_imp, forall_and]
  | lam b ih => simpa [FreeAway, freeNames] using ih

theorem freeAway_cons_fresh (Γ : List Nat) (b : Tm Nat) (h : FreeAway Γ b) :
    FreeAway (fresh Γ b :: Γ) b := by
  rw [freeAway_iff] at h ⊢
  intro x hx
  simp only [List.mem_cons, not_or]
  exact ⟨fun he => fresh_not_mem_freeNames Γ b (he ▸ hx), h x hx⟩

theorem ofNamed_reifyAux (Γ : List Nat) (hΓ : Γ.Nodup) (t : Tm Nat)
    (hs : Scoped Γ.length t) (hf : FreeAway Γ t) :
    ofNamed Γ (reifyAux Γ t) = t := by
  induction t generalizing Γ with
  | var v =>
    cases v with
    | free x =>
      have hx : indexOf? x Γ = none := (indexOf?_eq_none_iff x Γ).2 hf
      simp [reifyAux, ofNamed, hx]
    | bound i =>
      have hi : i < Γ.length := hs
      let j : Fin Γ.length := ⟨i, hi⟩
      have hget : Γ.getD i 0 = Γ.get j := by simp [List.getD, j, hi]
      have hidx := indexOf?_get Γ hΓ j
      change (match indexOf? (Γ.getD i 0) Γ with
        | some k => Tm.var (.bound k)
        | none => Tm.var (.free (Γ.getD i 0))) = Tm.var (.bound i)
      rw [hget, hidx]
      rfl
  | app p q ihp ihq =>
    simp only [Scoped, FreeAway] at hs hf
    simp [reifyAux, ofNamed, ihp Γ hΓ hs.1 hf.1, ihq Γ hΓ hs.2 hf.2]
  | lam b ih =>
    simp only [Scoped, FreeAway] at hs hf
    simp only [reifyAux, ofNamed]
    apply congrArg Tm.lam
    apply ih
    · exact List.nodup_cons.mpr ⟨fresh_not_mem_left Γ b, hΓ⟩
    · simpa using hs
    · exact freeAway_cons_fresh Γ b hf

theorem ofNamed_reify (t : Tm Nat) (hs : Scoped 0 t) :
    ofNamed [] (reify t) = t := by
  apply ofNamed_reifyAux [] List.nodup_nil t hs
  rw [freeAway_iff]
  simp

def single (x : Nat) (s : Tm Nat) (y : Nat) : Tm Nat :=
  if y = x then s else .var (.free y)

theorem single_scoped (x : Nat) (s : Tm Nat) (hs : Scoped 0 s) (y : Nat) :
    Scoped 0 (single x s y) := by
  by_cases h : y = x <;> simp [single, h, hs, Scoped]

/-- Capture-avoiding substitution on raw named Nat syntax, implemented through
the canonical locally nameless representation and the verified fresh reifier. -/
def substCA (x : Nat) (s t : Named.Tm Nat) : Named.Tm Nat :=
  reify (substFree (single x (ofNamed [] s)) (ofNamed [] t))

theorem ofNamed_substCA (x : Nat) (s t : Named.Tm Nat) :
    ofNamed [] (substCA x s t) =
      substFree (single x (ofNamed [] s)) (ofNamed [] t) := by
  apply ofNamed_reify
  apply scoped_substFree _ (scoped_ofNamed [] t)
  exact single_scoped x _ (scoped_ofNamed [] s)

theorem substCA_alpha {s s' t t' : Named.Tm Nat}
    (hs : Named.Alpha s s') (ht : Named.Alpha t t') (x : Nat) :
    Named.Alpha (substCA x s t) (substCA x s' t') := by
  rw [Named.Alpha, ofNamed_substCA, ofNamed_substCA, hs, ht]

theorem substCA_aconv {s s' t t' : Named.Tm Nat}
    (hs : Named.aconv s s' = true) (ht : Named.aconv t t' = true) (x : Nat) :
    Named.aconv (substCA x s t) (substCA x s' t') = true :=
  Named.aconv_correct.mpr (substCA_alpha (Named.aconv_correct.mp hs)
    (Named.aconv_correct.mp ht) x)

end NatReifier

namespace NatAlphaQuotient

open Named.AlphaQuotient NatReifier

theorem scoped_toScoped (q : Q Nat) : Scoped 0 (toScoped q).1 := by
  rcases (toScoped q).property with ⟨t, ht⟩
  rw [← ht]
  exact scoped_ofNamed [] t

def substScoped (x : Nat) (s t : ScopedNameless Nat) : ScopedNameless Nat :=
  let body := substFree (single x s.1) t.1
  have ht : Scoped 0 t.1 := by
    rcases t.property with ⟨raw, hr⟩
    rw [← hr]
    exact scoped_ofNamed [] raw
  have hs : Scoped 0 s.1 := by
    rcases s.property with ⟨raw, hr⟩
    rw [← hr]
    exact scoped_ofNamed [] raw
  have hb : Scoped 0 body :=
    scoped_substFree t.1 ht (single x s.1) (single_scoped x s.1 hs)
  ⟨body, ⟨reify body, ofNamed_reify body hb⟩⟩

noncomputable def subst (x : Nat) (s t : Q Nat) : Q Nat :=
  ofScoped (substScoped x (toScoped s) (toScoped t))

theorem toScoped_subst (x : Nat) (s t : Q Nat) :
    (toScoped (subst x s t)).1 =
      substFree (single x (toScoped s).1) (toScoped t).1 := by
  change (toScoped (ofScoped (substScoped x (toScoped s) (toScoped t)))).1 = _
  let z := substScoped x (toScoped s) (toScoped t)
  have h : toScoped (ofScoped z) = z :=
    (equivScoped (Name := Nat)).right_inv z
  have hv := congrArg Subtype.val h
  change (toScoped (ofScoped z)).1 = _
  exact hv

theorem subst_mk (x : Nat) (s t : Named.Tm Nat) :
    subst x (Quotient.mk _ s) (Quotient.mk _ t) =
      Quotient.mk _ (substCA x s t) := by
  apply (equivScoped (Name := Nat)).injective
  apply Subtype.ext
  change (toScoped (subst x (Quotient.mk _ s) (Quotient.mk _ t))).1 =
    (toScoped (Quotient.mk _ (substCA x s t))).1
  rw [toScoped_subst]
  exact ofNamed_substCA x s t |>.symm

theorem subst_respects_alpha {s s' t t' : Named.Tm Nat}
    (hs : Named.Alpha s s') (ht : Named.Alpha t t') (x : Nat) :
    subst x (Quotient.mk _ s) (Quotient.mk _ t) =
      subst x (Quotient.mk _ s') (Quotient.mk _ t') := by
  rw [subst_mk, subst_mk]
  exact Quotient.sound (substCA_alpha hs ht x)

end NatAlphaQuotient

end LocallyNameless

end ProjectBeth.Syntax
