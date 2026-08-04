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

def sumInl (A B : Ty) (a : Tm) : Tm :=
  .tyLam (.lam (.arr A.lift (.var 0))
    (.lam (.arr B.lift (.var 0))
      (.app (.var 1) (((a.renameTy Nat.succ).rename Nat.succ).rename Nat.succ))))

def sumInr (A B : Ty) (b : Tm) : Tm :=
  .tyLam (.lam (.arr A.lift (.var 0))
    (.lam (.arr B.lift (.var 0))
      (.app (.var 0) (((b.renameTy Nat.succ).rename Nat.succ).rename Nat.succ))))

def sumElim (s : Tm) (R : Ty) (left right : Tm) : Tm :=
  .app (.app (.tyApp s R) left) right

def prodPair (A B : Ty) (a b : Tm) : Tm :=
  .tyLam (.lam (.arr A.lift (.arr B.lift (.var 0)))
    (.app (.app (.var 0) ((a.renameTy Nat.succ).rename Nat.succ))
      ((b.renameTy Nat.succ).rename Nat.succ)))

def prodElim (p : Tm) (R : Ty) (k : Tm) : Tm := .app (.tyApp p R) k

def polyTy (base : Const → Ty) : Poly Const → Ty → Ty
  | .var, X => X
  | .const c, _ => base c
  | .pow c, X => .arr (base c) X
  | .sum P Q, X => sumTy (polyTy base P X) (polyTy base Q X)
  | .prod P Q, X => prodTy (polyTy base P X) (polyTy base Q X)

/-- Raw System F action of a polynomial on a morphism.  The accompanying
typing theorem can be layered independently; this definition is useful for
erasure and reduction squares already. -/
def fmapTm (base : Const → Ty) : (P : Poly Const) →
    (X Y : Ty) → Tm → Tm → Tm
  | .var, _, _, f, x => .app f x
  | .const _, _, _, _, x => x
  | .pow c, _, _, f, x =>
      .lam (base c) (.app (f.rename Nat.succ) (.app (x.rename Nat.succ) (.var 0)))
  | .sum P Q, X, Y, f, x =>
      sumElim x (sumTy (polyTy base P Y) (polyTy base Q Y))
        (.lam (polyTy base P X)
          (sumInl (polyTy base P Y) (polyTy base Q Y)
            (fmapTm base P X Y (f.rename Nat.succ) (.var 0))))
        (.lam (polyTy base Q X)
          (sumInr (polyTy base P Y) (polyTy base Q Y)
            (fmapTm base Q X Y (f.rename Nat.succ) (.var 0))))
  | .prod P Q, X, Y, f, x =>
      prodElim x (prodTy (polyTy base P Y) (polyTy base Q Y))
        (.lam (polyTy base P X) (.lam (polyTy base Q X)
          (prodPair (polyTy base P Y) (polyTy base Q Y)
            (fmapTm base P X Y ((f.rename Nat.succ).rename Nat.succ) (.var 1))
            (fmapTm base Q X Y ((f.rename Nat.succ).rename Nat.succ) (.var 0)))))

/-- `∀X. (P X → X) → X`. -/
def churchMuTy (base : Const → Ty) (P : Poly Const) : Ty :=
  .all (.arr (.arr (polyTy (fun c => (base c).lift) P (.var 0)) (.var 0)) (.var 0))

def churchFold (m : Tm) (X : Ty) (alg : Tm) : Tm := .app (.tyApp m X) alg

def churchRoll (base : Const → Ty) (P : Poly Const) (layer : Tm) : Tm :=
  .tyLam (.lam (.arr (polyTy (fun c => (base c).lift) P (.var 0)) (.var 0))
    (.app (.var 0)
      (fmapTm (fun c => (base c).lift) P (churchMuTy base P).lift (.var 0)
        (.lam (churchMuTy base P).lift
          (churchFold (.var 0) (.var 0) (.var 1)))
        (layer.rename Nat.succ))))

/-- `∃X. X × (X → P X)`, encoded impredicatively as
`∀R. (∀X. X → (X → P X) → R) → R`. -/
def coChurchTy (base : Const → Ty) (P : Poly Const) : Ty :=
  .all (.arr
    (.all (.arr (.var 0)
      (.arr (.arr (.var 0)
        (polyTy (fun c => ((base c).lift).lift) P (.var 0))) (.var 1))))
    (.var 0))

def coPack (base : Const → Ty) (P : Poly Const)
    (X : Ty) (seed step : Tm) : Tm :=
  .tyLam (.lam
    (.all (.arr (.var 0)
      (.arr (.arr (.var 0)
        (polyTy (fun c => ((base c).lift).lift) P (.var 0))) (.var 1))))
    (.app (.app (.tyApp (.var 0) X.lift) (seed.rename Nat.succ))
      (step.rename Nat.succ)))

def coElim (co : Tm) (R : Ty) (handler : Tm) : Tm :=
  .app (.tyApp co R) handler

def coiter (base : Const → Ty) (P : Poly Const)
    (X : Ty) (step seed : Tm) : Tm := coPack base P X seed step

def observe (base : Const → Ty) (P : Poly Const) (co : Tm) : Tm :=
  coElim co (polyTy base P (coChurchTy base P))
    (.tyLam (.lam (.var 0) (.lam
      (.arr (.var 0) (polyTy (fun c => (base c).lift) P (.var 0)))
      (fmapTm (fun c => ((base c).lift).lift) P (.var 0)
        (coChurchTy base P).lift
        (.lam (.var 0)
          (coiter (fun c => (base c).lift) P (.var 0) (.var 1) (.var 0)))
        (.app (.var 0) (.var 1))))))

theorem erase_churchFold_square (S : ProjectBeth.Untyped.Signature)
    (m alg : Tm) (X : Ty) :
    Inductive.Untyped.erase S (churchFold m X alg) =
      .app (Inductive.Untyped.erase S m) (Inductive.Untyped.erase S alg) := rfl

theorem erase_sumElim_square (S : ProjectBeth.Untyped.Signature)
    (s l r : Tm) (R : Ty) :
    Inductive.Untyped.erase S (sumElim s R l r) =
      .app (.app (Inductive.Untyped.erase S s) (Inductive.Untyped.erase S l))
        (Inductive.Untyped.erase S r) := rfl

theorem erase_prodElim_square (S : ProjectBeth.Untyped.Signature)
    (p k : Tm) (R : Ty) :
    Inductive.Untyped.erase S (prodElim p R k) =
      .app (Inductive.Untyped.erase S p) (Inductive.Untyped.erase S k) := rfl

theorem erase_coElim_square (S : ProjectBeth.Untyped.Signature)
    (co handler : Tm) (R : Ty) :
    Inductive.Untyped.erase S (coElim co R handler) =
      .app (Inductive.Untyped.erase S co) (Inductive.Untyped.erase S handler) := rfl

theorem erase_coiter_square (S : ProjectBeth.Untyped.Signature)
    (base : Const → Ty) (P : Poly Const) (X : Ty) (step seed : Tm) :
    Inductive.Untyped.erase S (coiter base P X step seed) =
      .lam (.app (.app (.var 0)
        ((Inductive.Untyped.erase S seed).rename Nat.succ))
        ((Inductive.Untyped.erase S step).rename Nat.succ)) := by
  simp [coiter, coPack, Inductive.Untyped.erase]

theorem coElim_pack_typeBeta (base : Const → Ty) (P : Poly Const)
    (X R : Ty) (seed step handler : Tm) :
    SmallStep (coElim (coPack base P X seed step) R handler)
      (Tm.app
        ((Tm.lam
          (.all (.arr (.var 0)
            (.arr (.arr (.var 0)
              (polyTy (fun c => ((base c).lift).lift) P (.var 0))) (.var 1))))
          (Tm.app (Tm.app (.tyApp (.var 0) X.lift) (seed.rename Nat.succ))
            (step.rename Nat.succ))).instantiateTy R)
        handler) := by
  exact SmallStep.app_left SmallStep.tyBeta

theorem erase_coElim_pack_steps (S : ProjectBeth.Untyped.Signature)
    (base : Const → Ty) (P : Poly Const) (X R : Ty)
    (seed step handler : Tm) :
    ProjectBeth.Untyped.Steps S
      (Inductive.Untyped.erase S (coElim (coPack base P X seed step) R handler))
      (Inductive.Untyped.erase S
        ((Tm.app
          ((Tm.lam
            (.all (.arr (.var 0)
              (.arr (.arr (.var 0)
                (polyTy (fun c => ((base c).lift).lift) P (.var 0))) (.var 1))))
            (Tm.app (Tm.app (.tyApp (.var 0) X.lift) (seed.rename Nat.succ))
              (step.rename Nat.succ))).instantiateTy R)
          handler))) :=
  Inductive.Untyped.smallStep_steps S
    (coElim_pack_typeBeta base P X R seed step handler)

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
