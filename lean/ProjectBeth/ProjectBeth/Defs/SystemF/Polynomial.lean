import ProjectBeth.Defs.SystemF.Untyped
import ProjectBeth.Defs.STLC.FixedPoints

universe u v

namespace ProjectBeth.SystemF.Polynomial

open ProjectBeth.STLC

variable {Const : Type u} {El : Const → Type v}

abbrev FMap (P : Poly Const) {X Y : Type v} (f : X → Y) :=
  Poly.map (El := El) f P

theorem map_id (P : Poly Const) (x : P.denote El X) : FMap P id x = x := by
  induction P with
  | var => rfl
  | const => rfl
  | pow => rfl
  | sum P Q ihP ihQ =>
    cases x with
    | inl x => exact congrArg Sum.inl (ihP x)
    | inr x => exact congrArg Sum.inr (ihQ x)
  | prod P Q ihP ihQ => exact Prod.ext (ihP x.1) (ihQ x.2)

theorem map_comp (P : Poly Const) (f : X → Y) (g : Y → Z)
    (x : P.denote El X) : FMap P g (FMap P f x) = FMap P (g ∘ f) x := by
  induction P with
  | var => rfl
  | const => rfl
  | pow => rfl
  | sum P Q ihP ihQ =>
    cases x with
    | inl x => exact congrArg Sum.inl (ihP x)
    | inr x => exact congrArg Sum.inr (ihQ x)
  | prod P Q ihP ihQ => exact Prod.ext (ihP x.1) (ihQ x.2)

/-- The impredicative Church representation of the least fixed point. -/
def ChurchMu (P : Poly Const) :=
  (X : Type v) → (P.denote El X → X) → X

def ChurchMu.fold (m : ChurchMu (El := El) P) (alg : P.denote El X → X) : X :=
  m X alg

/-- Parametricity is stated explicitly: raw System F does not by itself prove
that every inhabitant of an impredicative encoding is canonical. -/
def ChurchParametric (m : ChurchMu (El := El) P) : Prop :=
  ∀ (X Y : Type v) (algX : P.denote El X → X) (algY : P.denote El Y → Y)
    (h : X → Y),
    (∀ px, h (algX px) = algY (FMap P h px)) →
    h (m X algX) = m Y algY

theorem fold_natural (m : ChurchMu (El := El) P) (hm : ChurchParametric m)
    (algX : P.denote El X → X) (algY : P.denote El Y → Y) (h : X → Y)
    (hh : ∀ px, h (algX px) = algY (FMap P h px)) :
    h (m.fold algX) = m.fold algY := hm X Y algX algY h hh

theorem mu_fold_roll (alg : ∀ s, (Poly.Pos El P s → X) → X)
    (s) (child : Poly.Pos El P s → Poly.Mu El P) :
    Poly.Mu.fold alg (.roll s child) = alg s (fun p => Poly.Mu.fold alg (child p)) := rfl

/-- Genuine initiality of the container least fixed point: the algebra
homomorphism equation alone determines the morphism. -/
theorem mu_fold_unique (alg : ∀ s, (Poly.Pos El P s → X) → X)
    (h : Poly.Mu El P → X)
    (hhom : ∀ s child, h (.roll s child) = alg s (fun p => h (child p))) :
    h = Poly.Mu.fold alg := by
  funext m
  induction m with
  | roll s child ih =>
    rw [hhom, mu_fold_roll]
    congr 1
    funext p
    exact ih p

/-- Existential/co-Church representation of the greatest fixed point. -/
abbrev CoChurch (P : Poly Const) := Poly.CoFix El P

def CoChurch.unfold (step : Poly.Coalgebra El P X) (seed : X) : CoChurch (El := El) P :=
  ⟨X, seed, step⟩

def CoChurch.observe (x : CoChurch (El := El) P) :
    Σ s, Poly.Pos El P s → CoChurch (El := El) P := Poly.CoFix.observe x

theorem unfold_observe (step : Poly.Coalgebra El P X) (seed : X) :
    CoChurch.unfold step seed = ⟨X, seed, step⟩ := rfl

theorem unfold_fusion (stepX : Poly.Coalgebra El P X)
    (stepY : Poly.Coalgebra El P Y) (h : X → Y)
    (hh : ∀ x, stepY (h x) =
      ⟨(stepX x).1, fun p => h ((stepX x).2 p)⟩) (x : X) :
    CoChurch.observe (CoChurch.unfold stepY (h x)) =
      ⟨(stepX x).1, fun p => CoChurch.unfold stepY (h ((stepX x).2 p))⟩ := by
  simp only [CoChurch.observe, CoChurch.unfold, Poly.CoFix.observe]
  rw [hh]

/-- Finality is conditional on the intended coinductive extensional equality;
Leibniz equality of existential packages is deliberately not assumed. -/
theorem unfold_unique
    (step : Poly.Coalgebra El P X) (h : X → CoChurch (El := El) P)
    (hhom : ∀ x, CoChurch.observe (h x) =
      ⟨(step x).1, fun p => h ((step x).2 p)⟩)
    (BisimExt : ∀ (f g : X → CoChurch (El := El) P),
      (∀ x, CoChurch.observe (f x) =
        ⟨(step x).1, fun p => f ((step x).2 p)⟩) →
      (∀ x, CoChurch.observe (g x) =
        ⟨(step x).1, fun p => g ((step x).2 p)⟩) → f = g) :
    h = CoChurch.unfold step := by
  apply BisimExt h (CoChurch.unfold step) hhom
  intro x
  rfl

namespace Syntax

open ProjectBeth.SystemF.Inductive

def sumTy (A B : Ty) : Ty :=
  .all (.arr (.arr A.lift (.var 0)) (.arr (.arr B.lift (.var 0)) (.var 0)))

def prodTy (A B : Ty) : Ty :=
  .all (.arr (.arr A.lift (.arr B.lift (.var 0))) (.var 0))

def polyTy (base : Const → Ty) : Poly Const → Ty → Ty
  | .var, X => X
  | .const c, _ => base c
  | .pow c, X => .arr (base c) X
  | .sum P Q, X => sumTy (polyTy base P X) (polyTy base Q X)
  | .prod P Q, X => prodTy (polyTy base P X) (polyTy base Q X)

/-- `∀X. (P X → X) → X`. -/
def churchMuTy (base : Const → Ty) (P : Poly Const) : Ty :=
  .all (.arr (.arr (polyTy (fun c => (base c).lift) P (.var 0)) (.var 0)) (.var 0))

/-- Erasure ignores the polynomial type annotation, as required for System F
type abstraction/application squares. -/
theorem erase_tyApp_square (S : ProjectBeth.Untyped.Signature) (t : Tm)
    (base : Const → Ty) (P : Poly Const) :
    Inductive.Untyped.erase S (.tyApp t (churchMuTy base P)) =
      Inductive.Untyped.erase S t := rfl

theorem erase_tyLam_square (S : ProjectBeth.Untyped.Signature) (t : Tm) :
    Inductive.Untyped.erase S (.tyLam t) = Inductive.Untyped.erase S t := rfl

end Syntax

end ProjectBeth.SystemF.Polynomial
