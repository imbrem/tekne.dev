universe u

namespace ProjectBeth.HOLOmega

inductive Kind : Type
  | star : Kind
  | arr : Kind → Kind → Kind

mutual
  inductive Ty (Base : Type u) : Type u
    | base : Base → Ty Base
    | var : Nat → Ty Base
    | lam : Kind → Ty Base → Ty Base
    | app : Ty Base → Ty Base → Ty Base
    | bool : Ty Base
    | arr : Ty Base → Ty Base → Ty Base
    | sub : Ty Base → Tm Base → Ty Base

  inductive Tm (Base : Type u) : Type u
    | var : Nat → Tm Base
    | app : Tm Base → Tm Base → Tm Base
    | lam : Ty Base → Tm Base → Tm Base
    | tyApp : Tm Base → Ty Base → Tm Base
    | tyLam : Kind → Tm Base → Tm Base
    | bool : Bool → Tm Base
    | eq : Ty Base → Tm Base → Tm Base → Tm Base
    | epsilon : Ty Base → Tm Base → Tm Base
    | abs : Ty Base → Tm Base → Tm Base → Tm Base
    | rep : Ty Base → Tm Base → Tm Base → Tm Base
end

mutual
  inductive Kinded {Base : Type u} : List Kind → Ty Base → Kind → Prop
    | base : Kinded Δ (.base A) .star
    | var : Δ[n]? = some K → Kinded Δ (.var n) K
    | lam : Kinded (K :: Δ) t L → Kinded Δ (.lam K t) (.arr K L)
    | app : Kinded Δ f (.arr K L) → Kinded Δ x K → Kinded Δ (.app f x) L
    | bool : Kinded Δ .bool .star
    | arr : Kinded Δ A .star → Kinded Δ B .star → Kinded Δ (.arr A B) .star
    | sub : Kinded Δ A .star → HasType Δ [A] p .bool → Kinded Δ (.sub A p) .star

  inductive HasType {Base : Type u} :
      List Kind → List (Ty Base) → Tm Base → Ty Base → Prop
    | var : Γ[n]? = some A → HasType Δ Γ (.var n) A
    | app : HasType Δ Γ f (.arr A B) → HasType Δ Γ x A →
        HasType Δ Γ (.app f x) B
    | lam : Kinded Δ A .star → HasType Δ (A :: Γ) t B →
        HasType Δ Γ (.lam A t) (.arr A B)
    | tyApp : HasType Δ Γ f (.app F X) → Kinded Δ A K →
        HasType Δ Γ (.tyApp f A) (.app F A)
    | tyLam : HasType (K :: Δ) Γ t A →
        HasType Δ Γ (.tyLam K t) (.lam K A)
    | bool : HasType Δ Γ (.bool b) .bool
    | eq : Kinded Δ A .star → HasType Δ Γ x A → HasType Δ Γ y A →
        HasType Δ Γ (.eq A x y) .bool
    | epsilon : Kinded Δ A .star → HasType Δ Γ p (.arr A .bool) →
        HasType Δ Γ (.epsilon A p) A
    | abs : Kinded Δ A .star → HasType Δ [A] p .bool → HasType Δ Γ x A →
        HasType Δ Γ (.abs A p x) (.sub A p)
    | rep : Kinded Δ A .star → HasType Δ [A] p .bool →
        HasType Δ Γ x (.sub A p) → HasType Δ Γ (.rep A p x) A
end

/-- A common index for kinding and term typing. -/
inductive JudgementIndex (Base : Type u) : Type u
  | kinded (Δ : List Kind) (A : Ty Base) (K : Kind)
  | hasType (Δ : List Kind) (Γ : List (Ty Base)) (t : Tm Base) (A : Ty Base)

/-- Non-mutual indexed presentation of the mutually recursive HOLω
judgements.  It supplies a single ordinary induction principle while the
original `Kinded` and `HasType` APIs remain available. -/
inductive Judgement {Base : Type u} : JudgementIndex Base → Prop
  | kBase : Judgement (.kinded Δ (.base A) .star)
  | kVar : Δ[n]? = some K → Judgement (.kinded Δ (.var n) K)
  | kLam : Judgement (.kinded (K :: Δ) t L) →
      Judgement (.kinded Δ (.lam K t) (.arr K L))
  | kApp : Judgement (.kinded Δ f (.arr K L)) → Judgement (.kinded Δ x K) →
      Judgement (.kinded Δ (.app f x) L)
  | kBool : Judgement (.kinded Δ .bool .star)
  | kArr : Judgement (.kinded Δ A .star) → Judgement (.kinded Δ B .star) →
      Judgement (.kinded Δ (.arr A B) .star)
  | kSub : Judgement (.kinded Δ A .star) →
      Judgement (.hasType Δ [A] p .bool) → Judgement (.kinded Δ (.sub A p) .star)
  | var : Γ[n]? = some A → Judgement (.hasType Δ Γ (.var n) A)
  | app : Judgement (.hasType Δ Γ f (.arr A B)) →
      Judgement (.hasType Δ Γ x A) → Judgement (.hasType Δ Γ (.app f x) B)
  | lam : Judgement (.kinded Δ A .star) →
      Judgement (.hasType Δ (A :: Γ) t B) →
      Judgement (.hasType Δ Γ (.lam A t) (.arr A B))
  | tyApp : Judgement (.hasType Δ Γ f (.app F X)) →
      Judgement (.kinded Δ A K) → Judgement (.hasType Δ Γ (.tyApp f A) (.app F A))
  | tyLam : Judgement (.hasType (K :: Δ) Γ t A) →
      Judgement (.hasType Δ Γ (.tyLam K t) (.lam K A))
  | bool : Judgement (.hasType Δ Γ (.bool b) .bool)
  | eq : Judgement (.kinded Δ A .star) → Judgement (.hasType Δ Γ x A) →
      Judgement (.hasType Δ Γ y A) → Judgement (.hasType Δ Γ (.eq A x y) .bool)
  | epsilon : Judgement (.kinded Δ A .star) →
      Judgement (.hasType Δ Γ p (.arr A .bool)) →
      Judgement (.hasType Δ Γ (.epsilon A p) A)
  | abs : Judgement (.kinded Δ A .star) → Judgement (.hasType Δ [A] p .bool) →
      Judgement (.hasType Δ Γ x A) →
      Judgement (.hasType Δ Γ (.abs A p x) (.sub A p))
  | rep : Judgement (.kinded Δ A .star) → Judgement (.hasType Δ [A] p .bool) →
      Judgement (.hasType Δ Γ x (.sub A p)) →
      Judgement (.hasType Δ Γ (.rep A p x) A)

abbrev IndexedKinded {Base : Type u} (Δ : List Kind) (A : Ty Base)
    (K : Kind) : Prop :=
  Judgement (.kinded Δ A K)

abbrev IndexedHasType {Base : Type u} (Δ : List Kind) (Γ : List (Ty Base))
    (t : Tm Base) (A : Ty Base) : Prop :=
  Judgement (.hasType Δ Γ t A)

mutual
  theorem Kinded.toJudgement : Kinded Δ A K → Judgement (.kinded Δ A K)
    | .base => .kBase
    | .var h => .kVar h
    | .lam h => .kLam h.toJudgement
    | .app hf hx => .kApp hf.toJudgement hx.toJudgement
    | .bool => .kBool
    | .arr hA hB => .kArr hA.toJudgement hB.toJudgement
    | .sub hA hp => .kSub hA.toJudgement hp.toJudgement

  theorem HasType.toJudgement : HasType Δ Γ t A → Judgement (.hasType Δ Γ t A)
    | .var h => .var h
    | .app hf hx => .app hf.toJudgement hx.toJudgement
    | .lam hA ht => .lam hA.toJudgement ht.toJudgement
    | .tyApp hf hA => .tyApp hf.toJudgement hA.toJudgement
    | .tyLam ht => .tyLam ht.toJudgement
    | .bool => .bool
    | .eq hA hx hy => .eq hA.toJudgement hx.toJudgement hy.toJudgement
    | .epsilon hA hp => .epsilon hA.toJudgement hp.toJudgement
    | .abs hA hp hx => .abs hA.toJudgement hp.toJudgement hx.toJudgement
    | .rep hA hp hx => .rep hA.toJudgement hp.toJudgement hx.toJudgement
end

mutual
  theorem Judgement.toKinded : Judgement (.kinded Δ A K) → Kinded Δ A K
    | .kBase => .base
    | .kVar h => .var h
    | .kLam h => .lam h.toKinded
    | .kApp hf hx => .app hf.toKinded hx.toKinded
    | .kBool => .bool
    | .kArr hA hB => .arr hA.toKinded hB.toKinded
    | .kSub hA hp => .sub hA.toKinded hp.toHasType

  theorem Judgement.toHasType : Judgement (.hasType Δ Γ t A) → HasType Δ Γ t A
    | .var h => .var h
    | .app hf hx => .app hf.toHasType hx.toHasType
    | .lam hA ht => .lam hA.toKinded ht.toHasType
    | .tyApp hf hA => .tyApp hf.toHasType hA.toKinded
    | .tyLam ht => .tyLam ht.toHasType
    | .bool => .bool
    | .eq hA hx hy => .eq hA.toKinded hx.toHasType hy.toHasType
    | .epsilon hA hp => .epsilon hA.toKinded hp.toHasType
    | .abs hA hp hx => .abs hA.toKinded hp.toHasType hx.toHasType
    | .rep hA hp hx => .rep hA.toKinded hp.toHasType hx.toHasType
end

theorem judgement_kinded_iff : Judgement (.kinded Δ A K) ↔ Kinded Δ A K :=
  ⟨Judgement.toKinded, Kinded.toJudgement⟩

theorem judgement_hasType_iff : Judgement (.hasType Δ Γ t A) ↔ HasType Δ Γ t A :=
  ⟨Judgement.toHasType, HasType.toJudgement⟩

@[simp] theorem Kinded.toJudgement_toKinded (h : Kinded Δ A K) :
    h.toJudgement.toKinded = h := Subsingleton.elim _ _

@[simp] theorem HasType.toJudgement_toHasType (h : HasType Δ Γ t A) :
    h.toJudgement.toHasType = h := Subsingleton.elim _ _

@[simp] theorem Judgement.toKinded_toJudgement
    (h : Judgement (.kinded Δ A K)) : h.toKinded.toJudgement = h :=
  Subsingleton.elim _ _

@[simp] theorem Judgement.toHasType_toJudgement
    (h : Judgement (.hasType Δ Γ t A)) : h.toHasType.toJudgement = h :=
  Subsingleton.elim _ _

end ProjectBeth.HOLOmega
