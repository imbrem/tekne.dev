import ProjectBeth.Defs.STLC.FixedPoints
import ProjectBeth.Defs.STLC.Variants

universe u v

namespace ProjectBeth.STLC

namespace Let

abbrev Ty := Arrow.Ty

inductive Tm {Base : Type u} : List (Ty Base) → Ty Base → Type u
  | var : Var Γ A → Tm Γ A
  | app : Tm Γ (.arr A B) → Tm Γ A → Tm Γ B
  | lam : Tm (A :: Γ) B → Tm Γ (.arr A B)
  | letE : Tm Γ A → Tm (A :: Γ) B → Tm Γ B

end Let

namespace Cases

abbrev Ty := ArrowProdSum.Ty
abbrev Tm := @ArrowProdSum.Tm

end Cases

namespace LetCases

abbrev Ty := ArrowProdSum.Ty

inductive Tm {Base : Type u} : List (Ty Base) → Ty Base → Type u
  | var : Var Γ A → Tm Γ A
  | app : Tm Γ (.arr A B) → Tm Γ A → Tm Γ B
  | lam : Tm (A :: Γ) B → Tm Γ (.arr A B)
  | letE : Tm Γ A → Tm (A :: Γ) B → Tm Γ B
  | pair : Tm Γ A → Tm Γ B → Tm Γ (.prod A B)
  | fst : Tm Γ (.prod A B) → Tm Γ A
  | snd : Tm Γ (.prod A B) → Tm Γ B
  | inl : Tm Γ A → Tm Γ (.sum A B)
  | inr : Tm Γ B → Tm Γ (.sum A B)
  | case : Tm Γ (.sum A B) → Tm (A :: Γ) C → Tm (B :: Γ) C → Tm Γ C

end LetCases

namespace Inductive

inductive Ty (Base : Type u) : Type u
  | base : Base → Ty Base
  | arr : Ty Base → Ty Base → Ty Base
  | mu : Poly Base → Ty Base

inductive Tm (Base : Type u) : Type u
  | var : Nat → Tm Base
  | app : Tm Base → Tm Base → Tm Base
  | lam : Ty Base → Tm Base → Tm Base
  | roll : Poly Base → Tm Base → Tm Base
  | fold : Poly Base → Ty Base → Tm Base → Tm Base → Tm Base

abbrev Carrier {Base : Type u} (El : Base → Type v) (P : Poly Base) := Poly.Mu El P

def recursor {Base : Type u} {El : Base → Type v} {P : Poly Base} {X : Type v}
    (alg : ∀ s, (Poly.Pos El P s → X) → X) :
    Carrier El P → X :=
  Poly.Mu.fold alg

end Inductive

namespace Coinductive

inductive Ty (Base : Type u) : Type u
  | base : Base → Ty Base
  | arr : Ty Base → Ty Base → Ty Base
  | nu : Poly Base → Ty Base

inductive Tm (Base : Type u) : Type u
  | var : Nat → Tm Base
  | app : Tm Base → Tm Base → Tm Base
  | lam : Ty Base → Tm Base → Tm Base
  | observe : Poly Base → Tm Base → Tm Base
  | corec : Poly Base → Ty Base → Tm Base → Tm Base → Tm Base

abbrev Carrier {Base : Type u} (El : Base → Type v) (P : Poly Base) := Poly.CoFix El P

def corecursor {Base : Type u} {El : Base → Type v} {P : Poly Base} {X : Type v}
    (step : Poly.Coalgebra El P X) : X → Carrier El P :=
  fun seed => Poly.CoFix.unfold step seed

def observe {Base : Type u} {El : Base → Type v} {P : Poly Base} :
    Carrier El P → Σ s, Poly.Pos El P s → Carrier El P :=
  Poly.CoFix.observe

end Coinductive

end ProjectBeth.STLC
