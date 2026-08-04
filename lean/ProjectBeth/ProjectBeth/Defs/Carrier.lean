import ProjectBeth.Basic
import ProjectBeth.Defs.PowerTower

universe u v w

namespace ProjectBeth

abbrev BaseCarrier (BaseTy : Type u) (El : BaseTy → Type v) :=
  Σ A, El A

def BaseCarrier.of {BaseTy : Type u} (El : BaseTy → Type v) (A : BaseTy) :
    El A ↪ BaseCarrier BaseTy El where
  toFun x := ⟨A, x⟩
  inj' _ _ h := by cases h; rfl

abbrev TypeCarrier (BaseTy : Type u) (El : BaseTy → Type v) :=
  PowerTower (BaseCarrier BaseTy El)

def TypeCarrier.ofBase {BaseTy : Type u} (El : BaseTy → Type v) (A : BaseTy) :
    El A ↪ TypeCarrier BaseTy El :=
  (BaseCarrier.of El A).trans PowerTower.base

def TypeCarrier.mapBase
    {BaseTy : Type u} {BaseTy' : Type v}
    {El : BaseTy → Type w} {El' : BaseTy' → Type w}
    (onTy : BaseTy ↪ BaseTy')
    (onEl : ∀ A, El A ↪ El' (onTy A)) :
    BaseCarrier BaseTy El ↪ BaseCarrier BaseTy' El' where
  toFun x := ⟨onTy x.1, onEl x.1 x.2⟩
  inj' x y h := by
    cases x with
    | mk A x =>
      cases y with
      | mk B y =>
        have hA : onTy A = onTy B := congrArg Sigma.fst h
        have hAB : A = B := onTy.injective hA
        subst B
        have hxy : onEl A x = onEl A y := eq_of_heq (Sigma.mk.inj_iff.mp h).2
        have := (onEl A).injective hxy
        cases this
        rfl

namespace Code

noncomputable def decode (coding : _root_.Code α κ) (x : coding.car) : α :=
  Classical.choose ((_root_.Code.mem_code_iff coding x).mp x.property)

theorem code_decode (coding : _root_.Code α κ) (x : coding.car) :
    coding.code (decode coding x) = x :=
  Classical.choose_spec ((_root_.Code.mem_code_iff coding x).mp x.property)

theorem decode_code (coding : _root_.Code α κ) (x : α) :
    decode coding ⟨coding.code x, by simp⟩ = x := by
  apply coding.code_inj
  exact code_decode coding _

def intoPowerTower {Base : Type u} (coding : _root_.Code α (PowerLevel Base n)) :
    _root_.Code α (PowerTower Base) :=
  coding.comp (_root_.Code.emb (PowerTower.ofLevel n))

end Code

end ProjectBeth
