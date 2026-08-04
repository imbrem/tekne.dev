import ProjectBeth.Defs.HOL.Syntax.Indexed
import ProjectBeth.Defs.HOL.Syntax.Environment

/-! Commuting bridges between the independent environment grammar, the legacy
mutual grammar, and its single-family indexed presentation. -/

universe u v w

namespace ProjectBeth.HOL.Syntax.Connections


variable {Base : Type u} {TyName : Type v} {ConstName : Type w}
variable {env : Environment.Defined.Env Base TyName ConstName}
  {Γ : Environment.Defined.Ctx Base TyName} {A : Environment.Defined.Ty Base TyName}
  {t : Environment.Defined.Tm Base TyName ConstName}

def minimalTyToIndexed (A : Environment.Minimal.Ty Base) : Indexed.ITy Base :=
  Indexed.encodeTy A.toRaw

def minimalTmToIndexed (t : Environment.Minimal.Tm Base) : Indexed.ITm Base :=
  Indexed.encodeTm t.toRaw

def choiceTyToIndexed (A : Environment.Choice.Ty Base) : Indexed.ITy Base :=
  Indexed.encodeTy A.toRaw

def choiceTmToIndexed (t : Environment.Choice.Tm Base) : Indexed.ITm Base :=
  Indexed.encodeTm t.toRaw

@[simp] theorem decode_minimalTyToIndexed (A : Environment.Minimal.Ty Base) :
    Indexed.decodeTy (minimalTyToIndexed A) = A.toRaw := Indexed.decode_encode_ty _

@[simp] theorem decode_minimalTmToIndexed (t : Environment.Minimal.Tm Base) :
    Indexed.decodeTm (minimalTmToIndexed t) = t.toRaw := Indexed.decode_encode_tm _

@[simp] theorem choice_minimal_ty_square (A : Environment.Minimal.Ty Base) :
    choiceTyToIndexed (Environment.Choice.Ty.ofMinimal A) = minimalTyToIndexed A := by
  simp [choiceTyToIndexed, minimalTyToIndexed]

@[simp] theorem choice_minimal_tm_square (t : Environment.Minimal.Tm Base) :
    choiceTmToIndexed (Environment.Choice.Tm.ofMinimal t) = minimalTmToIndexed t := by
  simp [choiceTmToIndexed, minimalTmToIndexed]

private theorem minimal_ty_rename (A : Environment.Minimal.Ty Base)
    (ρ : Nat → Nat) :
    Indexed.rename ρ (Indexed.encodeTy A.toRaw) = Indexed.encodeTy A.toRaw := by
  induction A <;>
    simp [Environment.Minimal.Ty.toRaw, Indexed.encodeTy, Indexed.rename, *]

private theorem choice_ty_rename (A : Environment.Choice.Ty Base)
    (ρ : Nat → Nat) :
    Indexed.rename ρ (Indexed.encodeTy A.toRaw) = Indexed.encodeTy A.toRaw := by
  induction A <;>
    simp [Environment.Choice.Ty.toRaw, Indexed.encodeTy, Indexed.rename, *]

@[simp] theorem minimal_rename_indexed_square (t : Environment.Minimal.Tm Base)
    (ρ : Nat → Nat) :
    minimalTmToIndexed (t.rename ρ) = Indexed.rename ρ (minimalTmToIndexed t) := by
  induction t generalizing ρ with
  | var n => rfl
  | app f x ihf ihx =>
      simp only [minimalTmToIndexed] at ihf ihx
      simp only [Environment.Minimal.Tm.rename, minimalTmToIndexed,
        Environment.Minimal.Tm.toRaw, Indexed.encodeTm, Indexed.rename]
      rw [← ihf ρ, ← ihx ρ]
  | lam A t ih =>
      simp only [minimalTmToIndexed] at ih
      simp only [Environment.Minimal.Tm.rename, minimalTmToIndexed,
        Environment.Minimal.Tm.toRaw, Indexed.encodeTm, Indexed.rename]
      rw [minimal_ty_rename, ih (Environment.liftRen ρ)]
      rfl
  | bool b => rfl
  | eq A x y ihx ihy =>
      simp only [minimalTmToIndexed] at ihx ihy
      simp only [Environment.Minimal.Tm.rename, minimalTmToIndexed,
        Environment.Minimal.Tm.toRaw, Indexed.encodeTm, Indexed.rename]
      rw [minimal_ty_rename, ← ihx ρ, ← ihy ρ]

@[simp] theorem choice_rename_indexed_square (t : Environment.Choice.Tm Base)
    (ρ : Nat → Nat) :
    choiceTmToIndexed (t.rename ρ) = Indexed.rename ρ (choiceTmToIndexed t) := by
  induction t generalizing ρ with
  | var n => rfl
  | app f x ihf ihx =>
      simp only [choiceTmToIndexed] at ihf ihx
      simp only [Environment.Choice.Tm.rename, choiceTmToIndexed,
        Environment.Choice.Tm.toRaw, Indexed.encodeTm, Indexed.rename]
      rw [← ihf ρ, ← ihx ρ]
  | lam A t ih =>
      simp only [choiceTmToIndexed] at ih
      simp only [Environment.Choice.Tm.rename, choiceTmToIndexed,
        Environment.Choice.Tm.toRaw, Indexed.encodeTm, Indexed.rename]
      rw [choice_ty_rename, ih (Environment.liftRen ρ)]
      rfl
  | bool b => rfl
  | eq A x y ihx ihy =>
      simp only [choiceTmToIndexed] at ihx ihy
      simp only [Environment.Choice.Tm.rename, choiceTmToIndexed,
        Environment.Choice.Tm.toRaw, Indexed.encodeTm, Indexed.rename]
      rw [choice_ty_rename, ← ihx ρ, ← ihy ρ]
  | epsilon A p ih =>
      simp only [choiceTmToIndexed] at ih
      simp only [Environment.Choice.Tm.rename, choiceTmToIndexed,
        Environment.Choice.Tm.toRaw, Indexed.encodeTm, Indexed.rename]
      rw [choice_ty_rename, ← ih ρ]

def definedTyToIndexed (J : Environment.Defined.Interpretation env)
    (A : Environment.Defined.Ty Base TyName) : Indexed.ITy Base :=
  Indexed.encodeTy (J.elabTy A)

def definedTmToIndexed (J : Environment.Defined.Interpretation env)
    (t : Environment.Defined.Tm Base TyName ConstName) : Indexed.ITm Base :=
  Indexed.encodeTm (J.elabTm t)

@[simp] theorem decode_definedTyToIndexed (J : Environment.Defined.Interpretation env)
    (A : Environment.Defined.Ty Base TyName) :
    Indexed.decodeTy (definedTyToIndexed J A) = J.elabTy A := Indexed.decode_encode_ty _

@[simp] theorem decode_definedTmToIndexed (J : Environment.Defined.Interpretation env)
    (t : Environment.Defined.Tm Base TyName ConstName) :
    Indexed.decodeTm (definedTmToIndexed J t) = J.elabTm t := Indexed.decode_encode_tm _

@[simp] theorem defined_choice_ty_square (J : Environment.Defined.Interpretation env)
    (A : Environment.Choice.Ty Base) :
    definedTyToIndexed J (Environment.Defined.Ty.ofChoice A) = choiceTyToIndexed A := by
  simp [definedTyToIndexed, choiceTyToIndexed, J.ty_ofChoice]

@[simp] theorem defined_choice_tm_square (J : Environment.Defined.Interpretation env)
    (t : Environment.Choice.Tm Base) :
    definedTmToIndexed J (Environment.Defined.Tm.ofChoice t) = choiceTmToIndexed t := by
  simp [definedTmToIndexed, choiceTmToIndexed, J.tm_ofChoice]

/-- Proof-relevant typing support for an elaboration.  It is kept separate from
the homomorphism because clients may use an untyped elaborator first. -/
structure TypedInterpretation
    (env : Environment.Defined.Env Base TyName ConstName) where
  toInterpretation : Environment.Defined.Interpretation env
  wf : ∀ {A}, Environment.Defined.Ty.Wf env A → HOL.Ty.Wf (toInterpretation.elabTy A)
  typing : ∀ {Γ t A}, Environment.Defined.HasType env Γ t A →
    HOL.HasType (Γ.map toInterpretation.elabTy)
      (toInterpretation.elabTm t) (toInterpretation.elabTy A)

theorem environment_typing_legacy_square (J : TypedInterpretation env)
    (h : Environment.Defined.HasType env Γ t A) :
    HOL.HasType (Γ.map J.toInterpretation.elabTy)
      (J.toInterpretation.elabTm t) (J.toInterpretation.elabTy A) := J.typing h

theorem environment_typing_indexed_square (J : TypedInterpretation env)
    (h : Environment.Defined.HasType env Γ t A) :
    Indexed.HasType (Γ.map (definedTyToIndexed J.toInterpretation))
      (definedTmToIndexed J.toInterpretation t)
      (definedTyToIndexed J.toInterpretation A) := by
  simpa [Indexed.HasType, definedTyToIndexed, definedTmToIndexed,
    List.map_map, Function.comp_def] using J.typing h

theorem environment_judgement_square (J : TypedInterpretation env)
    (h : Environment.Defined.HasType env Γ t A) :
    HOL.Judgement (.hasType (Γ.map J.toInterpretation.elabTy)
      (J.toInterpretation.elabTm t) (J.toInterpretation.elabTy A)) :=
  (HOL.judgement_hasType_iff).2 (J.typing h)

end ProjectBeth.HOL.Syntax.Connections
