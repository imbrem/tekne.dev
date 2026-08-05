import ProjectBeth.Defs.STLC.Semantics

universe u

namespace ProjectBeth.STLC.Arrow.Beth

/-- A family of base types interpreted as subsets of the concrete carrier
`BethOmega`. -/
abbrev BaseSet (Base : Type u) := Base → Set BethOmega

/-- The direct semantics: at a base type, values carry a proof of membership in
the chosen subset of `BethOmega`. -/
abbrev Direct {Base : Type u} (baseSet : BaseSet Base) :=
  Ty.Direct baseSet

/-- The shape semantics forgets base-type membership and interprets every base
type by the common carrier `BethOmega`. -/
abbrev Shape {Base : Type u} := Ty.Shape (Base := Base) BethOmega

/-- The inductively generated membership predicate on shape values. -/
abbrev Member {Base : Type u} (baseSet : BaseSet Base) :=
  Ty.Rel baseSet

/-- Agreement between a direct value and its underlying shape value. -/
abbrev Agree {Base : Type u} (baseSet : BaseSet Base) :=
  Ty.Agree baseSet

abbrev DirectEnv {Base : Type u} (baseSet : BaseSet Base) :=
  STLC.Env (Direct baseSet)

abbrev ShapeEnv {Base : Type u} := STLC.Env (Shape (Base := Base))

def direct {Base : Type u} (baseSet : BaseSet Base)
    {Γ : List (Ty Base)} {A : Ty Base} (t : Tm Γ A) :
    DirectEnv baseSet Γ → Direct baseSet A :=
  Tm.direct baseSet t

def shape {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base}
    (t : Tm Γ A) : ShapeEnv Γ → Shape A :=
  Tm.shape BethOmega t

theorem shape_mem {Base : Type u} (baseSet : BaseSet Base)
    {Γ : List (Ty Base)} {A : Ty Base} (t : Tm Γ A)
    {env : ShapeEnv Γ} (henv : Env.Rel baseSet env) :
    Member baseSet A (shape t env) :=
  Tm.fundamental baseSet t henv

theorem direct_shape_agree {Base : Type u} (baseSet : BaseSet Base)
    {Γ : List (Ty Base)} {A : Ty Base} (t : Tm Γ A)
    {directEnv : DirectEnv baseSet Γ} {shapeEnv : ShapeEnv Γ}
    (henv : Env.Agree baseSet directEnv shapeEnv) :
    Agree baseSet A (direct baseSet t directEnv) (shape t shapeEnv) :=
  Tm.agreement baseSet t henv

/-- Data selecting concrete `BethOmega` codes for the direct denotations of
open terms.  Keeping this explicit records the cardinality obligation instead
of silently assuming that every function space embeds into `BethOmega`. -/
abbrev Coding {Base : Type u} (baseSet : BaseSet Base) :=
  Tm.Coding BethOmega baseSet

def coded {Base : Type u} {baseSet : BaseSet Base}
    (M : Coding baseSet) {Γ : List (Ty Base)} {A : Ty Base}
    (t : Tm Γ A) : BethOmega :=
  Tm.coded M t

theorem decode_coded {Base : Type u} {baseSet : BaseSet Base}
    (M : Coding baseSet) {Γ : List (Ty Base)} {A : Ty Base}
    (t : Tm Γ A) :
    ProjectBeth.Code.decode (M.term Γ A)
      ⟨coded M t, by simp [coded, Tm.coded]⟩ = direct baseSet t :=
  Tm.decode_coded M t

end ProjectBeth.STLC.Arrow.Beth
