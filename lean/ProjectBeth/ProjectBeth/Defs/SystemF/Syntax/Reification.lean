import ProjectBeth.Defs.SystemF.Syntax.Named

namespace ProjectBeth.SystemF.Syntax

namespace Named

universe u
variable {Name : Type u}

theorem lookup_eq_none_iff [DecidableEq Name] (x : Name) (Γ : List Name) :
    lookup x Γ = none ↔ x ∉ Γ := by
  induction Γ with
  | nil => simp [lookup]
  | cons y Γ ih =>
    by_cases h : x = y
    · subst y; simp [lookup]
    · simp [lookup, h, ih]

theorem lookup_get [DecidableEq Name] (Γ : List Name) (hΓ : Γ.Nodup)
    (i : Fin Γ.length) : lookup (Γ.get i) Γ = some i := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | cons x Γ ih =>
    cases i using Fin.cases with
    | zero => simp [lookup]
    | succ i =>
      have hx : x ∉ Γ := (List.nodup_cons.mp hΓ).1
      have hn := (List.nodup_cons.mp hΓ).2
      have hne : Γ.get i ≠ x := by
        intro h
        apply hx
        rw [← h]
        exact List.get_mem Γ i
      change (if Γ.get i = x then some 0 else
        Option.map Nat.succ (lookup (Γ.get i) Γ)) = some (i.val + 1)
      rw [if_neg hne, ih hn i]
      rfl

theorem lookup_lt [DecidableEq Name] {x : Name} {Γ : List Name} {i : Nat}
    (h : lookup x Γ = some i) : i < Γ.length := by
  induction Γ generalizing i with
  | nil => simp [lookup] at h
  | cons y Γ ih =>
    by_cases he : x = y
    · subst y
      simp [lookup] at h
      subst i
      simp
    · simp [lookup, he] at h
      obtain ⟨j, hj, rfl⟩ := h
      simpa using Nat.succ_lt_succ (ih hj)

end Named

namespace LocallyNameless

universe u v
variable {Name : Type u} {TyName : Type u} {TmName : Type v}

/-- A type is scoped by `k` surrounding type binders. -/
def Ty.Scoped : Nat → Ty Name → Prop
  | k, .var (.bound i) => i < k
  | _, .var (.free _) => True
  | _, .bool | _, .nat => True
  | k, .arr A B => A.Scoped k ∧ B.Scoped k
  | k, .all A => A.Scoped (k + 1)

/-- A term is simultaneously scoped by its type and term binder depths. -/
def Tm.Scoped : Nat → Nat → Tm TyName TmName → Prop
  | _, k, .var (.bound i) => i < k
  | _, _, .var (.free _) => True
  | _, _, .bool _ | _, _, .nat _ => True
  | d, k, .app f a => f.Scoped d k ∧ a.Scoped d k
  | d, k, .lam A t => A.Scoped d ∧ t.Scoped d (k + 1)
  | d, k, .tyApp f A => f.Scoped d k ∧ A.Scoped d
  | d, k, .tyLam t => t.Scoped (d + 1) k

def Ty.FreeAway (Γ : List Name) : Ty Name → Prop
  | .var (.bound _) => True
  | .var (.free x) => x ∉ Γ
  | .bool | .nat => True
  | .arr A B => A.FreeAway Γ ∧ B.FreeAway Γ
  | .all A => A.FreeAway Γ

def Tm.FreeAway (ΓTy : List TyName) (ΓTm : List TmName) : Tm TyName TmName → Prop
  | .var (.bound _) => True
  | .var (.free x) => x ∉ ΓTm
  | .bool _ | .nat _ => True
  | .app f a => f.FreeAway ΓTy ΓTm ∧ a.FreeAway ΓTy ΓTm
  | .lam A t => A.FreeAway ΓTy ∧ t.FreeAway ΓTy ΓTm
  | .tyApp f A => f.FreeAway ΓTy ΓTm ∧ A.FreeAway ΓTy
  | .tyLam t => t.FreeAway ΓTy ΓTm

theorem Ty.scoped_toLN [DecidableEq Name] (Γ : List Name) (A : Named.Ty Name) :
    (A.toLN Γ).Scoped Γ.length := by
  induction A generalizing Γ with
  | var x =>
    simp only [Named.Ty.toLN]
    split
    · rename_i i h; exact Named.lookup_lt h
    · trivial
  | bool => trivial
  | nat => trivial
  | arr A B ihA ihB => exact ⟨ihA Γ, ihB Γ⟩
  | all x A ih =>
    change (A.toLN (x :: Γ)).Scoped (Γ.length + 1)
    simpa using ih (x :: Γ)

theorem Tm.scoped_toLN [DecidableEq TyName] [DecidableEq TmName]
    (ΓTy : List TyName) (ΓTm : List TmName) (t : Named.Tm TyName TmName) :
    (t.toLN ΓTy ΓTm).Scoped ΓTy.length ΓTm.length := by
  induction t generalizing ΓTy ΓTm with
  | var x =>
    simp only [Named.Tm.toLN]
    split
    · rename_i i h; exact Named.lookup_lt h
    · trivial
  | app f a ihf iha => exact ⟨ihf ΓTy ΓTm, iha ΓTy ΓTm⟩
  | lam x A t ih => exact ⟨Ty.scoped_toLN ΓTy A, by simpa using ih ΓTy (x :: ΓTm)⟩
  | tyApp f A ih => exact ⟨ih ΓTy ΓTm, Ty.scoped_toLN ΓTy A⟩
  | tyLam x t ih =>
    change (t.toLN (x :: ΓTy) ΓTm).Scoped (ΓTy.length + 1) ΓTm.length
    simpa using ih (x :: ΓTy) ΓTm
  | bool => trivial
  | nat => trivial

namespace NatReifier

def listMax : List Nat → Nat
  | [] => 0
  | x :: xs => max x (listMax xs)

theorem le_listMax_of_mem {x : Nat} : ∀ {xs}, x ∈ xs → x ≤ listMax xs
  | [], h => by simp at h
  | y :: ys, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_listMax_of_mem h) (Nat.le_max_right _ _)

def tyFreeNames : Ty Nat → List Nat
  | .var (.bound _) => []
  | .var (.free x) => [x]
  | .bool | .nat => []
  | .arr A B => tyFreeNames A ++ tyFreeNames B
  | .all A => tyFreeNames A

def tmFreeTyNames : Tm Nat Nat → List Nat
  | .var _ | .bool _ | .nat _ => []
  | .app f a => tmFreeTyNames f ++ tmFreeTyNames a
  | .lam A t => tyFreeNames A ++ tmFreeTyNames t
  | .tyApp f A => tmFreeTyNames f ++ tyFreeNames A
  | .tyLam t => tmFreeTyNames t

def tmFreeTmNames : Tm Nat Nat → List Nat
  | .var (.bound _) => []
  | .var (.free x) => [x]
  | .bool _ | .nat _ => []
  | .app f a => tmFreeTmNames f ++ tmFreeTmNames a
  | .lam _ t | .tyLam t => tmFreeTmNames t
  | .tyApp f _ => tmFreeTmNames f

def fresh (Γ free : List Nat) : Nat := listMax (Γ ++ free) + 1

theorem fresh_not_mem_left (Γ free : List Nat) : fresh Γ free ∉ Γ := by
  intro h
  have hle := le_listMax_of_mem (List.mem_append_left free h)
  exact Nat.not_succ_le_self _ hle

theorem fresh_not_mem_right (Γ free : List Nat) : fresh Γ free ∉ free := by
  intro h
  have hle := le_listMax_of_mem (List.mem_append_right Γ h)
  exact Nat.not_succ_le_self _ hle

def reifyTyAux (Γ : List Nat) : Ty Nat → Named.Ty Nat
  | .var (.bound i) => .var (Γ.getD i 0)
  | .var (.free x) => .var x
  | .bool => .bool
  | .nat => .nat
  | .arr A B => .arr (reifyTyAux Γ A) (reifyTyAux Γ B)
  | .all A =>
      let x := fresh Γ (tyFreeNames A)
      .all x (reifyTyAux (x :: Γ) A)

def reifyTmAux (ΓTy ΓTm : List Nat) : Tm Nat Nat → Named.Tm Nat Nat
  | .var (.bound i) => .var (ΓTm.getD i 0)
  | .var (.free x) => .var x
  | .app f a => .app (reifyTmAux ΓTy ΓTm f) (reifyTmAux ΓTy ΓTm a)
  | .lam A t =>
      let x := fresh ΓTm (tmFreeTmNames t)
      .lam x (reifyTyAux ΓTy A) (reifyTmAux ΓTy (x :: ΓTm) t)
  | .tyApp f A => .tyApp (reifyTmAux ΓTy ΓTm f) (reifyTyAux ΓTy A)
  | .tyLam t =>
      let x := fresh ΓTy (tmFreeTyNames t)
      .tyLam x (reifyTmAux (x :: ΓTy) ΓTm t)
  | .bool b => .bool b
  | .nat n => .nat n

def reifyTy (A : Ty Nat) := reifyTyAux [] A
def reifyTm (t : Tm Nat Nat) := reifyTmAux [] [] t

theorem tyFreeAway_iff (Γ : List Nat) (A : Ty Nat) :
    A.FreeAway Γ ↔ ∀ x ∈ tyFreeNames A, x ∉ Γ := by
  induction A with
  | var v => cases v <;> simp [Ty.FreeAway, tyFreeNames]
  | bool => simp [Ty.FreeAway, tyFreeNames]
  | nat => simp [Ty.FreeAway, tyFreeNames]
  | arr A B ihA ihB => simp [Ty.FreeAway, tyFreeNames, ihA, ihB, or_imp, forall_and]
  | all A ih => simpa [Ty.FreeAway, tyFreeNames] using ih

theorem tyFreeAway_cons_fresh (Γ : List Nat) (A : Ty Nat) (h : A.FreeAway Γ) :
    A.FreeAway (fresh Γ (tyFreeNames A) :: Γ) := by
  rw [tyFreeAway_iff] at h ⊢
  intro x hx
  simp only [List.mem_cons, not_or]
  exact ⟨fun he => fresh_not_mem_right Γ (tyFreeNames A) (he ▸ hx), h x hx⟩

theorem toLN_reifyTyAux (Γ : List Nat) (hΓ : Γ.Nodup) (A : Ty Nat)
    (hs : A.Scoped Γ.length) (hf : A.FreeAway Γ) :
    (reifyTyAux Γ A).toLN Γ = A := by
  induction A generalizing Γ with
  | var v =>
    cases v with
    | free x =>
      have hx := (Named.lookup_eq_none_iff x Γ).2 hf
      simp [reifyTyAux, Named.Ty.toLN, hx]
    | bound i =>
      let j : Fin Γ.length := ⟨i, hs⟩
      have hget : Γ.getD i 0 = Γ.get j := by
        rw [List.getD_eq_getElem Γ 0 hs]
        congr
      have hidx := Named.lookup_get Γ hΓ j
      have hidx' : Named.lookup (Γ.get j) Γ = some i := by simpa [j] using hidx
      rw [show reifyTyAux Γ (.var (.bound i)) = .var (Γ.getD i 0) from rfl,
        hget]
      change (match Named.lookup (Γ.get j) Γ with
        | some n => Ty.var (.bound n)
        | none => Ty.var (.free (Γ.get j))) = Ty.var (.bound i)
      rw [hidx']
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB =>
    exact congrArg₂ Ty.arr (ihA Γ hΓ hs.1 hf.1) (ihB Γ hΓ hs.2 hf.2)
  | all A ih =>
    apply congrArg Ty.all
    apply ih
    · exact List.nodup_cons.mpr ⟨fresh_not_mem_left Γ (tyFreeNames A), hΓ⟩
    · exact hs
    · exact tyFreeAway_cons_fresh Γ A hf

theorem toLN_reifyTy (A : Ty Nat) (hs : A.Scoped 0) : (reifyTy A).toLN [] = A := by
  apply toLN_reifyTyAux [] List.nodup_nil A hs
  rw [tyFreeAway_iff]
  simp

theorem tmFreeAway_iff (ΓTy ΓTm : List Nat) (t : Tm Nat Nat) :
    t.FreeAway ΓTy ΓTm ↔
      (∀ x ∈ tmFreeTyNames t, x ∉ ΓTy) ∧
      (∀ x ∈ tmFreeTmNames t, x ∉ ΓTm) := by
  induction t with
  | var v => cases v <;> simp [Tm.FreeAway, tmFreeTyNames, tmFreeTmNames]
  | app f a ihf iha =>
    simp [Tm.FreeAway, tmFreeTyNames, tmFreeTmNames, ihf, iha, or_imp]
    aesop
  | lam A t ih =>
    rw [Tm.FreeAway, ih, tyFreeAway_iff]
    simp only [tmFreeTyNames, tmFreeTmNames, List.mem_append, or_imp]
    aesop
  | tyApp f A ih =>
    rw [Tm.FreeAway, ih, tyFreeAway_iff]
    simp only [tmFreeTyNames, tmFreeTmNames, List.mem_append, or_imp]
    aesop
  | tyLam t ih => simpa [Tm.FreeAway, tmFreeTyNames, tmFreeTmNames] using ih
  | bool => simp [Tm.FreeAway, tmFreeTyNames, tmFreeTmNames]
  | nat => simp [Tm.FreeAway, tmFreeTyNames, tmFreeTmNames]

theorem tmFreeAway_cons_ty (ΓTy ΓTm : List Nat) (t : Tm Nat Nat)
    (h : t.FreeAway ΓTy ΓTm) :
    t.FreeAway (fresh ΓTy (tmFreeTyNames t) :: ΓTy) ΓTm := by
  rw [tmFreeAway_iff] at h ⊢
  refine ⟨?_, h.2⟩
  intro x hx
  simp only [List.mem_cons, not_or]
  exact ⟨fun he => fresh_not_mem_right ΓTy (tmFreeTyNames t) (he ▸ hx), h.1 x hx⟩

theorem tmFreeAway_cons_tm (ΓTy ΓTm : List Nat) (t : Tm Nat Nat)
    (h : t.FreeAway ΓTy ΓTm) :
    t.FreeAway ΓTy (fresh ΓTm (tmFreeTmNames t) :: ΓTm) := by
  rw [tmFreeAway_iff] at h ⊢
  refine ⟨h.1, ?_⟩
  intro x hx
  simp only [List.mem_cons, not_or]
  exact ⟨fun he => fresh_not_mem_right ΓTm (tmFreeTmNames t) (he ▸ hx), h.2 x hx⟩

theorem toLN_reifyTmAux (ΓTy ΓTm : List Nat)
    (hTy : ΓTy.Nodup) (hTm : ΓTm.Nodup) (t : Tm Nat Nat)
    (hs : t.Scoped ΓTy.length ΓTm.length) (hf : t.FreeAway ΓTy ΓTm) :
    (reifyTmAux ΓTy ΓTm t).toLN ΓTy ΓTm = t := by
  induction t generalizing ΓTy ΓTm with
  | var v =>
    cases v with
    | free x =>
      have hx := (Named.lookup_eq_none_iff x ΓTm).2 hf
      simp [reifyTmAux, Named.Tm.toLN, hx]
    | bound i =>
      let j : Fin ΓTm.length := ⟨i, hs⟩
      have hget : ΓTm.getD i 0 = ΓTm.get j := by
        rw [List.getD_eq_getElem ΓTm 0 hs]
        congr
      have hidx := Named.lookup_get ΓTm hTm j
      have hidx' : Named.lookup (ΓTm.get j) ΓTm = some i := by simpa [j] using hidx
      rw [show reifyTmAux ΓTy ΓTm (.var (.bound i)) = .var (ΓTm.getD i 0) from rfl,
        hget]
      change (match Named.lookup (ΓTm.get j) ΓTm with
        | some n => Tm.var (.bound n)
        | none => Tm.var (.free (ΓTm.get j))) = Tm.var (.bound i)
      rw [hidx']
  | app f a ihf iha =>
    exact congrArg₂ Tm.app (ihf ΓTy ΓTm hTy hTm hs.1 hf.1)
      (iha ΓTy ΓTm hTy hTm hs.2 hf.2)
  | lam A t ih =>
    apply congrArg₂ Tm.lam
    · exact toLN_reifyTyAux ΓTy hTy A hs.1 hf.1
    · apply ih
      · exact hTy
      · exact List.nodup_cons.mpr ⟨fresh_not_mem_left ΓTm (tmFreeTmNames t), hTm⟩
      · exact hs.2
      · exact tmFreeAway_cons_tm ΓTy ΓTm t hf.2
  | tyApp f A ih =>
    exact congrArg₂ Tm.tyApp (ih ΓTy ΓTm hTy hTm hs.1 hf.1)
      (toLN_reifyTyAux ΓTy hTy A hs.2 hf.2)
  | tyLam t ih =>
    apply congrArg Tm.tyLam
    apply ih
    · exact List.nodup_cons.mpr ⟨fresh_not_mem_left ΓTy (tmFreeTyNames t), hTy⟩
    · exact hTm
    · exact hs
    · exact tmFreeAway_cons_ty ΓTy ΓTm t hf
  | bool => rfl
  | nat => rfl

theorem toLN_reifyTm (t : Tm Nat Nat) (hs : t.Scoped 0 0) :
    (reifyTm t).toLN [] [] = t := by
  apply toLN_reifyTmAux [] [] List.nodup_nil List.nodup_nil t hs
  rw [tmFreeAway_iff]
  simp

/-- Every closed locally nameless System F type has a canonical named representative. -/
def ClosedTy := { A : Ty Nat // A.Scoped 0 }

/-- Every closed locally nameless System F term has a canonical named representative. -/
def ClosedTm := { t : Tm Nat Nat // t.Scoped 0 0 }

def ClosedTy.toNamed (A : ClosedTy) : Named.Ty Nat := reifyTy A.1
def ClosedTm.toNamed (t : ClosedTm) : Named.Tm Nat Nat := reifyTm t.1

@[simp] theorem ClosedTy.toLN_toNamed (A : ClosedTy) : A.toNamed.toLN [] = A.1 :=
  toLN_reifyTy A.1 A.2

@[simp] theorem ClosedTm.toLN_toNamed (t : ClosedTm) : t.toNamed.toLN [] [] = t.1 :=
  toLN_reifyTm t.1 t.2

def namedTySetoid : Setoid (Named.Ty Nat) := inferInstance
def namedTmSetoid : Setoid (Named.Tm Nat Nat) := inferInstance
abbrev NamedTyQ := Quotient namedTySetoid
abbrev NamedTmQ := Quotient namedTmSetoid

def namedTyToClosed : NamedTyQ → ClosedTy :=
  Quotient.lift (fun A => ⟨A.toLN [], Ty.scoped_toLN [] A⟩)
    (fun _ _ h => Subtype.ext h)

def namedTmToClosed : NamedTmQ → ClosedTm :=
  Quotient.lift (fun t => ⟨t.toLN [] [], Tm.scoped_toLN [] [] t⟩)
    (fun _ _ h => Subtype.ext h)

def closedTyToNamed (A : ClosedTy) : NamedTyQ := Quotient.mk _ A.toNamed
def closedTmToNamed (t : ClosedTm) : NamedTmQ := Quotient.mk _ t.toNamed

@[simp] theorem namedTyToClosed_closedTyToNamed (A : ClosedTy) :
    namedTyToClosed (closedTyToNamed A) = A := by
  apply Subtype.ext
  exact A.toLN_toNamed

@[simp] theorem namedTmToClosed_closedTmToNamed (t : ClosedTm) :
    namedTmToClosed (closedTmToNamed t) = t := by
  apply Subtype.ext
  exact t.toLN_toNamed

@[simp] theorem closedTyToNamed_namedTyToClosed (q : NamedTyQ) :
    closedTyToNamed (namedTyToClosed q) = q := by
  induction q using Quotient.inductionOn with
  | _ A =>
    apply Quotient.sound
    change (reifyTy (A.toLN [])).toLN [] = A.toLN []
    exact toLN_reifyTy _ (Ty.scoped_toLN [] A)

@[simp] theorem closedTmToNamed_namedTmToClosed (q : NamedTmQ) :
    closedTmToNamed (namedTmToClosed q) = q := by
  induction q using Quotient.inductionOn with
  | _ t =>
    apply Quotient.sound
    change (reifyTm (t.toLN [] [])).toLN [] [] = t.toLN [] []
    exact toLN_reifyTm _ (Tm.scoped_toLN [] [] t)

def namedTyEquivClosed : NamedTyQ ≃ ClosedTy where
  toFun := namedTyToClosed
  invFun := closedTyToNamed
  left_inv := closedTyToNamed_namedTyToClosed
  right_inv := namedTyToClosed_closedTyToNamed

def namedTmEquivClosed : NamedTmQ ≃ ClosedTm where
  toFun := namedTmToClosed
  invFun := closedTmToNamed
  left_inv := closedTmToNamed_namedTmToClosed
  right_inv := namedTmToClosed_closedTmToNamed

end NatReifier

end LocallyNameless

end ProjectBeth.SystemF.Syntax
