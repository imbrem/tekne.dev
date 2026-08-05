import ProjectBeth.Defs.HOL.Semantics
import ProjectBeth.Defs.HOLOmega.Semantics
import ProjectBeth.Defs.STLC.FixedPoints

universe u v

namespace ProjectBeth.Translations

/-! Full polynomial functors are embedded as semantic atoms.  This is intentionally
different from claiming Church encodings of sums and products in the small HOL
signature, which does not contain the required polymorphic type former. -/

inductive PolyAtom (Const : Type u) : Type u
  | constant : Const → PolyAtom Const
  | family : STLC.Poly Const → PolyAtom Const
  | least : STLC.Poly Const → PolyAtom Const
  | greatest : STLC.Poly Const → PolyAtom Const

namespace PolyAtom

def polyMap (f : C → D) : STLC.Poly C → STLC.Poly D
  | .var => .var
  | .const c => .const (f c)
  | .pow c => .pow (f c)
  | .sum P Q => .sum (polyMap f P) (polyMap f Q)
  | .prod P Q => .prod (polyMap f P) (polyMap f Q)

def map (f : C → D) : PolyAtom C → PolyAtom D
  | .constant c => .constant (f c)
  | .family P => .family (polyMap f P)
  | .least P => .least (polyMap f P)
  | .greatest P => .greatest (polyMap f P)

@[simp] theorem map_family (f : C → D) (P : STLC.Poly C) :
    map f (.family P) = .family (polyMap f P) := rfl

@[simp] theorem polyMap_id (P : STLC.Poly C) : polyMap id P = P := by
  induction P <;> simp [polyMap, *]

@[simp] theorem polyMap_comp (g : D → E) (f : C → D) (P : STLC.Poly C) :
    polyMap g (polyMap f P) = polyMap (g ∘ f) P := by
  induction P <;> simp [polyMap, *, Function.comp_def]

theorem denote_polyMap (f : C → D) (El : D → Type v) (P : STLC.Poly C) (X : Type v) :
    STLC.Poly.denote El (polyMap f P) X = STLC.Poly.denote (El ∘ f) P X := by
  induction P <;> simp [polyMap, STLC.Poly.denote, *, Function.comp_def]

end PolyAtom

namespace Polynomial

variable {Const : Type u}

def familyHOL (P : STLC.Poly Const) : HOL.Ty (PolyAtom Const) :=
  .base (.family P)

def leastHOL (P : STLC.Poly Const) : HOL.Ty (PolyAtom Const) :=
  .base (.least P)

def greatestHOL (P : STLC.Poly Const) : HOL.Ty (PolyAtom Const) :=
  .base (.greatest P)

/-- A polynomial as a kind `★ → ★` family in HOLω.  Its application remains an
opaque semantic atom because the current object language has no sum/product type
constants. -/
def familyOmega (P : STLC.Poly Const) : HOLOmega.Ty (PolyAtom Const) :=
  .lam .star (.base (.family P))

def familyOmegaApp (P : STLC.Poly Const) (X : HOLOmega.Ty (PolyAtom Const)) :
    HOLOmega.Ty (PolyAtom Const) := .app (familyOmega P) X

def familyHOL_wf (P : STLC.Poly Const) : HOL.Ty.Wf (familyHOL P) := .base

theorem familyOmega_kinded (P : STLC.Poly Const) :
    HOLOmega.Kinded [] (familyOmega P) (.arr .star .star) :=
  .lam .base

theorem familyOmegaApp_kinded (P : STLC.Poly Const)
    (hX : HOLOmega.Kinded [] X .star) :
    HOLOmega.Kinded [] (familyOmegaApp P X) .star :=
  .app (familyOmega_kinded P) hX

/-- The interpretations assigned to the three atom embeddings.  Their commuting
squares are definitional, so clients may use `rfl`. -/
def familyDenote (El : Const → Type v) (X : Type v) (P : STLC.Poly Const) : Type v :=
  STLC.Poly.denote El P X

def leastDenote (El : Const → Type v) (P : STLC.Poly Const) : Type v :=
  STLC.Poly.Mu El P

def greatestDenote (El : Const → Type v) (P : STLC.Poly Const) : Type (v + 1) :=
  STLC.Poly.CoFix El P

@[simp] theorem family_semantic_square (El : Const → Type v) (X : Type v)
    (P : STLC.Poly Const) : familyDenote El X P = STLC.Poly.denote El P X := rfl

@[simp] theorem least_semantic_square (El : Const → Type v) (P : STLC.Poly Const) :
    leastDenote El P = STLC.Poly.Mu El P := rfl

@[simp] theorem greatest_semantic_square (El : Const → Type v) (P : STLC.Poly Const) :
    greatestDenote El P = STLC.Poly.CoFix El P := rfl

end Polynomial

namespace HOLToOmega

variable {Base : Type u}

mutual
  def ty : HOL.Ty Base → HOLOmega.Ty Base
    | .base A => .base A
    | .bool => .bool
    | .arr A B => .arr (ty A) (ty B)
    | .sub A p => .sub (ty A) (tm p)

  def tm : HOL.Tm Base → HOLOmega.Tm Base
    | .var n => .var n
    | .app f x => .app (tm f) (tm x)
    | .lam A b => .lam (ty A) (tm b)
    | .bool b => .bool b
    | .eq A x y => .eq (ty A) (tm x) (tm y)
    | .epsilon A p => .epsilon (ty A) (tm p)
    | .abs A p x => .abs (ty A) (tm p) (tm x)
    | .rep A p x => .rep (ty A) (tm p) (tm x)
end

@[simp] theorem ty_base (A : Base) : ty (.base A) = .base A := rfl
@[simp] theorem ty_bool : ty (Base := Base) .bool = .bool := rfl
@[simp] theorem ty_arr (A B : HOL.Ty Base) : ty (.arr A B) = .arr (ty A) (ty B) := rfl

mutual
  def wf : {A : HOL.Ty Base} → HOL.Ty.Wf A → HOLOmega.Kinded [] (ty A) .star
    | _, .base => .base
    | _, .bool => .bool
    | _, .arr hA hB => .arr (wf hA) (wf hB)
    | _, .sub hA hp => .sub (wf hA) (hasType hp)

  def hasType : {Γ : HOL.Ctx Base} → {t : HOL.Tm Base} → {A : HOL.Ty Base} →
      HOL.HasType Γ t A → HOLOmega.HasType [] (Γ.map ty) (tm t) (ty A)
    | _, _, _, .var h => .var (by simp [List.getElem?_map, h])
    | _, _, _, .app hf hx => .app (hasType hf) (hasType hx)
    | _, _, _, .lam hA hb => .lam (wf hA) (by simpa using hasType hb)
    | _, _, _, .bool => .bool
    | _, _, _, .eq hA hx hy => .eq (wf hA) (hasType hx) (hasType hy)
    | _, _, _, .epsilon hA hp => .epsilon (wf hA) (hasType hp)
    | _, _, _, .abs hA hp hx => .abs (wf hA) (by simpa using hasType hp) (hasType hx)
    | _, _, _, .rep hA hp hx => .rep (wf hA) (by simpa using hasType hp) (hasType hx)
end

/-- Target of the single-index HOL judgement translation. -/
def judgementTarget : HOL.JudgementIndex Base → Prop
  | .wf A => HOLOmega.IndexedKinded [] (ty A) .star
  | .hasType Γ t A => HOLOmega.IndexedHasType [] (Γ.map ty) (tm t) (ty A)

/-- The typing translation expressed with ordinary induction over the indexed
judgement view.  This avoids a custom mutual recursor in clients that need to
translate well-formed types and typed terms together. -/
theorem judgement : {i : HOL.JudgementIndex Base} →
    HOL.Judgement i → judgementTarget i
  | _, .wfBase => .kBase
  | _, .wfBool => .kBool
  | _, .wfArr hA hB => .kArr (judgement hA) (judgement hB)
  | _, .wfSub hA hp => .kSub (judgement hA) (judgement hp)
  | _, .var h => .var (by simp [List.getElem?_map, h])
  | _, .app hf hx => .app (judgement hf) (judgement hx)
  | _, .lam hA ht => .lam (judgement hA)
      (by simpa [judgementTarget] using judgement ht)
  | _, .bool => .bool
  | _, .eq hA hx hy => .eq (judgement hA) (judgement hx) (judgement hy)
  | _, .epsilon hA hp => .epsilon (judgement hA) (judgement hp)
  | _, .abs hA hp hx =>
      .abs (judgement hA) (by simpa [judgementTarget] using judgement hp)
        (judgement hx)
  | _, .rep hA hp hx =>
      .rep (judgement hA) (by simpa [judgementTarget] using judgement hp)
        (judgement hx)

theorem judgement_wf_agrees (h : HOL.Ty.Wf A) :
    (judgement h.toJudgement).toKinded = wf h :=
  Subsingleton.elim _ _

theorem judgement_hasType_agrees (h : HOL.HasType Γ t A) :
    (judgement h.toJudgement).toHasType = hasType h :=
  Subsingleton.elim _ _

/-- The embedding preserves all HOL typing derivations, not merely raw syntax. -/
theorem sound (d : HOL.HasType Γ t A) :
    HOLOmega.HasType [] (Γ.map ty) (tm t) (ty A) := hasType d

end HOLToOmega

end ProjectBeth.Translations
