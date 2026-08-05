/-! Polynomial functors and their container-based least and greatest fixed points. -/

universe u v

namespace ProjectBeth.STLC

inductive Poly (Const : Type u) : Type u
  | var : Poly Const
  | const : Const → Poly Const
  | pow : Const → Poly Const
  | sum : Poly Const → Poly Const → Poly Const
  | prod : Poly Const → Poly Const → Poly Const

namespace Poly

variable {Const : Type u}

def denote (El : Const → Type v) : Poly Const → Type v → Type v
  | .var, X => X
  | .const A, _ => El A
  | .pow A, X => El A → X
  | .sum P Q, X => denote El P X ⊕ denote El Q X
  | .prod P Q, X => denote El P X × denote El Q X

def map {El : Const → Type v} {X Y : Type v} (g : X → Y) :
    (P : Poly Const) → denote El P X → denote El P Y
  | .var, x => g x
  | .const _, x => x
  | .pow _, h => g ∘ h
  | .sum P _, .inl x => .inl (map g P x)
  | .sum _ Q, .inr x => .inr (map g Q x)
  | .prod P Q, x => (map g P x.1, map g Q x.2)

@[simp]
theorem map_id {El : Const → Type v} (P : Poly Const) (x : denote El P X) :
    map id P x = x := by
  induction P with
  | var => rfl
  | const => rfl
  | pow =>
      funext a
      rfl
  | sum P Q ihP ihQ =>
      cases x with
      | inl x => exact congrArg Sum.inl (ihP x)
      | inr x => exact congrArg Sum.inr (ihQ x)
  | prod P Q ihP ihQ => exact Prod.ext (ihP x.1) (ihQ x.2)

theorem map_comp {El : Const → Type v} (P : Poly Const)
    (g : Y → Z) (f : X → Y) (x : denote El P X) :
    map (g ∘ f) P x = map g P (map f P x) := by
  induction P with
  | var => rfl
  | const => rfl
  | pow =>
      funext a
      rfl
  | sum P Q ihP ihQ =>
      cases x with
      | inl x => exact congrArg Sum.inl (ihP x)
      | inr x => exact congrArg Sum.inr (ihQ x)
  | prod P Q ihP ihQ => exact Prod.ext (ihP x.1) (ihQ x.2)

def Shape (El : Const → Type v) : Poly Const → Type v
  | .var => PUnit
  | .const A => El A
  | .pow _ => PUnit
  | .sum P Q => Shape El P ⊕ Shape El Q
  | .prod P Q => Shape El P × Shape El Q

def Pos (El : Const → Type v) : (P : Poly Const) → Shape El P → Type v
  | .var, _ => PUnit
  | .const _, _ => PEmpty
  | .pow A, _ => El A
  | .sum P _, .inl s => Pos El P s
  | .sum _ Q, .inr s => Pos El Q s
  | .prod P Q, s => Pos El P s.1 ⊕ Pos El Q s.2

inductive Mu (El : Const → Type v) (P : Poly Const) : Type v
  | roll (shape : Shape El P) (child : Pos El P shape → Mu El P) : Mu El P

def Mu.fold {El : Const → Type v} {P : Poly Const} {X : Type v}
    (alg : ∀ s, (Pos El P s → X) → X) : Mu El P → X
  | .roll s child => alg s (fun p => fold alg (child p))

abbrev Coalgebra (El : Const → Type v) (P : Poly Const) (X : Type v) :=
  X → Σ s, Pos El P s → X

def CoFix (El : Const → Type v) (P : Poly Const) : Type (v + 1) :=
  Σ X : Type v, X × Coalgebra El P X

def CoFix.unfold {El : Const → Type v} {P : Poly Const} {X : Type v}
    (step : Coalgebra El P X) (seed : X) : CoFix El P :=
  ⟨X, seed, step⟩

def CoFix.observe {El : Const → Type v} {P : Poly Const} (x : CoFix El P) :
    Σ s, Pos El P s → CoFix El P :=
  let next := x.2.2 x.2.1
  ⟨next.1, fun p => ⟨x.1, next.2 p, x.2.2⟩⟩

end Poly

end ProjectBeth.STLC
