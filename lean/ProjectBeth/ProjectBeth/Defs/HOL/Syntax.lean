import ProjectBeth.Defs.STLC.Core

/-! Raw, extrinsically typed HOL syntax.  Both `Ty Base` and `Tm Base` are
small in the universe of `Base`; well-formedness and typing are separate
judgements below. -/

universe u

namespace ProjectBeth.HOL

mutual
  inductive Ty (Base : Type u) : Type u
    | base : Base → Ty Base
    | bool : Ty Base
    | arr : Ty Base → Ty Base → Ty Base
    | sub : Ty Base → Tm Base → Ty Base

  inductive Tm (Base : Type u) : Type u
    | var : Nat → Tm Base
    | app : Tm Base → Tm Base → Tm Base
    | lam : Ty Base → Tm Base → Tm Base
    | bool : Bool → Tm Base
    | eq : Ty Base → Tm Base → Tm Base → Tm Base
    | epsilon : Ty Base → Tm Base → Tm Base
    | abs : Ty Base → Tm Base → Tm Base → Tm Base
    | rep : Ty Base → Tm Base → Tm Base → Tm Base
end

abbrev Ctx (Base : Type u) := List (Ty Base)

mutual
  inductive Ty.Wf {Base : Type u} : Ty Base → Prop
    | base : Ty.Wf (.base A)
    | bool : Ty.Wf .bool
    | arr : Ty.Wf A → Ty.Wf B → Ty.Wf (.arr A B)
    | sub : Ty.Wf A → HasType [A] p .bool → Ty.Wf (.sub A p)

  inductive HasType {Base : Type u} : Ctx Base → Tm Base → Ty Base → Prop
    | var : Γ[n]? = some A → HasType Γ (.var n) A
    | app : HasType Γ f (.arr A B) → HasType Γ x A → HasType Γ (.app f x) B
    | lam : Ty.Wf A → HasType (A :: Γ) t B → HasType Γ (.lam A t) (.arr A B)
    | bool : HasType Γ (.bool b) .bool
    | eq : Ty.Wf A → HasType Γ x A → HasType Γ y A →
        HasType Γ (.eq A x y) .bool
    | epsilon : Ty.Wf A → HasType Γ p (.arr A .bool) →
        HasType Γ (.epsilon A p) A
    | abs : Ty.Wf A → HasType [A] p .bool → HasType Γ x A →
        HasType Γ (.abs A p x) (.sub A p)
    | rep : Ty.Wf A → HasType [A] p .bool → HasType Γ x (.sub A p) →
        HasType Γ (.rep A p x) A
end

/-- A single index family for the mutually defined well-formedness and typing
judgements.  This view has an ordinary (non-mutual) induction principle. -/
inductive JudgementIndex (Base : Type u) : Type u
  | wf (A : Ty Base)
  | hasType (Γ : Ctx Base) (t : Tm Base) (A : Ty Base)

/-- Indexed presentation of `Ty.Wf` and `HasType`.  The original judgements
remain available, including all of their constructor names. -/
inductive Judgement {Base : Type u} : JudgementIndex Base → Prop
  | wfBase : Judgement (.wf (.base A))
  | wfBool : Judgement (.wf .bool)
  | wfArr : Judgement (.wf A) → Judgement (.wf B) →
      Judgement (.wf (.arr A B))
  | wfSub : Judgement (.wf A) → Judgement (.hasType [A] p .bool) →
      Judgement (.wf (.sub A p))
  | var : Γ[n]? = some A → Judgement (.hasType Γ (.var n) A)
  | app : Judgement (.hasType Γ f (.arr A B)) →
      Judgement (.hasType Γ x A) → Judgement (.hasType Γ (.app f x) B)
  | lam : Judgement (.wf A) → Judgement (.hasType (A :: Γ) t B) →
      Judgement (.hasType Γ (.lam A t) (.arr A B))
  | bool : Judgement (.hasType Γ (.bool b) .bool)
  | eq : Judgement (.wf A) → Judgement (.hasType Γ x A) →
      Judgement (.hasType Γ y A) → Judgement (.hasType Γ (.eq A x y) .bool)
  | epsilon : Judgement (.wf A) → Judgement (.hasType Γ p (.arr A .bool)) →
      Judgement (.hasType Γ (.epsilon A p) A)
  | abs : Judgement (.wf A) → Judgement (.hasType [A] p .bool) →
      Judgement (.hasType Γ x A) → Judgement (.hasType Γ (.abs A p x) (.sub A p))
  | rep : Judgement (.wf A) → Judgement (.hasType [A] p .bool) →
      Judgement (.hasType Γ x (.sub A p)) → Judgement (.hasType Γ (.rep A p x) A)

abbrev IndexedWf {Base : Type u} (A : Ty Base) : Prop :=
  Judgement (.wf A)

abbrev IndexedHasType {Base : Type u} (Γ : Ctx Base) (t : Tm Base)
    (A : Ty Base) : Prop :=
  Judgement (.hasType Γ t A)

mutual
  theorem Ty.Wf.toJudgement : Ty.Wf A → Judgement (.wf A)
    | .base => .wfBase
    | .bool => .wfBool
    | .arr hA hB => .wfArr hA.toJudgement hB.toJudgement
    | .sub hA hp => .wfSub hA.toJudgement hp.toJudgement

  theorem HasType.toJudgement : HasType Γ t A → Judgement (.hasType Γ t A)
    | .var h => .var h
    | .app hf hx => .app hf.toJudgement hx.toJudgement
    | .lam hA ht => .lam hA.toJudgement ht.toJudgement
    | .bool => .bool
    | .eq hA hx hy => .eq hA.toJudgement hx.toJudgement hy.toJudgement
    | .epsilon hA hp => .epsilon hA.toJudgement hp.toJudgement
    | .abs hA hp hx => .abs hA.toJudgement hp.toJudgement hx.toJudgement
    | .rep hA hp hx => .rep hA.toJudgement hp.toJudgement hx.toJudgement
end

mutual
  theorem Judgement.toWf : Judgement (.wf A) → Ty.Wf A
    | .wfBase => .base
    | .wfBool => .bool
    | .wfArr hA hB => .arr hA.toWf hB.toWf
    | .wfSub hA hp => .sub hA.toWf hp.toHasType

  theorem Judgement.toHasType : Judgement (.hasType Γ t A) → HasType Γ t A
    | .var h => .var h
    | .app hf hx => .app hf.toHasType hx.toHasType
    | .lam hA ht => .lam hA.toWf ht.toHasType
    | .bool => .bool
    | .eq hA hx hy => .eq hA.toWf hx.toHasType hy.toHasType
    | .epsilon hA hp => .epsilon hA.toWf hp.toHasType
    | .abs hA hp hx => .abs hA.toWf hp.toHasType hx.toHasType
    | .rep hA hp hx => .rep hA.toWf hp.toHasType hx.toHasType
end

theorem judgement_wf_iff : Judgement (.wf A) ↔ Ty.Wf A :=
  ⟨Judgement.toWf, Ty.Wf.toJudgement⟩

theorem judgement_hasType_iff : Judgement (.hasType Γ t A) ↔ HasType Γ t A :=
  ⟨Judgement.toHasType, HasType.toJudgement⟩

@[simp] theorem Ty.Wf.toJudgement_toWf (h : Ty.Wf A) :
    h.toJudgement.toWf = h := Subsingleton.elim _ _

@[simp] theorem HasType.toJudgement_toHasType (h : HasType Γ t A) :
    h.toJudgement.toHasType = h := Subsingleton.elim _ _

@[simp] theorem Judgement.toWf_toJudgement (h : Judgement (.wf A)) :
    h.toWf.toJudgement = h := Subsingleton.elim _ _

@[simp] theorem Judgement.toHasType_toJudgement
    (h : Judgement (.hasType Γ t A)) : h.toHasType.toJudgement = h :=
  Subsingleton.elim _ _

def TotalSubtype (α : Type u) (P : α → Prop) :=
  {x : α // P x ∨ ¬∃ y, P y}

namespace TotalSubtype

def rep {α : Type u} {P : α → Prop} : TotalSubtype α P → α :=
  Subtype.val

noncomputable def abs {α : Type u} [Inhabited α] (P : α → Prop) :
    α → TotalSubtype α P := by
  classical
  intro x
  exact if hx : P x then ⟨x, Or.inl hx⟩
    else if hP : ∃ y, P y then ⟨Classical.choose hP, Or.inl (Classical.choose_spec hP)⟩
    else ⟨x, Or.inr hP⟩

noncomputable instance {α : Type u} [Inhabited α] (P : α → Prop) :
    Inhabited (TotalSubtype α P) where
  default := abs P default

@[simp]
theorem rep_abs_of {α : Type u} [Inhabited α] {P : α → Prop}
    {x : α} (hx : P x) : rep (abs P x) = x := by
  classical
  simp [abs, hx, rep]

@[simp]
theorem abs_rep {α : Type u} [Inhabited α] {P : α → Prop}
    (x : TotalSubtype α P) : abs P (rep x) = x := by
  classical
  apply Subtype.ext
  rcases x.property with hx | hP
  · simp [abs, rep, hx]
  · have hx : ¬P x.val := fun hp => hP ⟨x.val, hp⟩
    simp [abs, rep, hx, hP]

theorem nonempty {α : Type u} [Inhabited α] (P : α → Prop) :
    Nonempty (TotalSubtype α P) :=
  ⟨abs P default⟩

end TotalSubtype

end ProjectBeth.HOL
