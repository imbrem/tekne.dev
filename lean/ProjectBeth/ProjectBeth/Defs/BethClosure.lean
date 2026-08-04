import ProjectBeth.Defs.Closure

universe u

namespace ProjectBeth

namespace PowerLevel

def raise {Base : Type u} : {n m : Nat} → n ≤ m → PowerLevel Base n ↪ PowerLevel Base m
  | 0, 0, _ => Function.Embedding.refl _
  | 0, m + 1, _ => (raise (Nat.zero_le m)).trans ix
  | n + 1, 0, h => nomatch h
  | n + 1, m + 1, h =>
      mapEmbedding (raise (Nat.succ_le_succ_iff.mp h)) 1

@[simp]
theorem raise_ix {Base : Type u} {n m : Nat} (h : n ≤ m)
    (x : PowerLevel Base n) :
    raise (Nat.succ_le_succ h) (ix x) = ix (raise h x) := by
  change Set.image (raise h) {x} = {raise h x}
  simp

end PowerLevel

structure BethLevel where
  level : Nat

instance : CoeSort BethLevel Type where
  coe A := PowerLevel Nat A.level

namespace BethLevel

private def common (A B : BethLevel) := max A.level B.level

private def leftCode {X : Type u} (x : X) : Set (Set X) := {{x}}
private def rightCode {X : Type u} (x : X) : Set (Set X) := {∅, {x}}

private theorem leftCode_injective {X : Type u} : Function.Injective (@leftCode X) := by
  intro x y h
  simpa [leftCode] using h

private theorem rightCode_injective {X : Type u} : Function.Injective (@rightCode X) := by
  intro x y h
  have h' : ({x} : Set X) ∈ rightCode x := by simp [rightCode]
  rw [h] at h'
  simpa [rightCode] using h'

private theorem left_ne_right {X : Type u} (x y : X) : leftCode x ≠ rightCode y := by
  intro h
  have h' : (∅ : Set X) ∈ leftCode x := by simpa [h, rightCode]
  simpa [leftCode] using h'

private def sumCode {X : Type u} : (X ⊕ X) ↪ Set (Set X) where
  toFun
    | Sum.inl x => leftCode x
    | Sum.inr y => rightCode y
  inj' a b h := by
    cases a with
    | inl x =>
      cases b with
      | inl y => exact congrArg Sum.inl (leftCode_injective h)
      | inr y => exact False.elim (left_ne_right x y h)
    | inr x =>
      cases b with
      | inl y => exact False.elim (left_ne_right y x h.symm)
      | inr y => exact congrArg Sum.inr (rightCode_injective h)

private def pairCode {X : Type u} : (X × X) ↪ Set (Set (Set X)) where
  toFun p := {leftCode p.1, rightCode p.2}
  inj' a b h := by
    change ({leftCode a.1, rightCode a.2} : Set (Set (Set X))) =
      {leftCode b.1, rightCode b.2} at h
    have ha : leftCode a.1 ∈ ({leftCode b.1, rightCode b.2} : Set (Set (Set X))) := by
      rw [← h]
      simp
    have hb : rightCode a.2 ∈ ({leftCode b.1, rightCode b.2} : Set (Set (Set X))) := by
      rw [← h]
      simp
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact False.elim (left_ne_right b.1 a.2 hb.symm)
      · exact Prod.ext (leftCode_injective ha) (rightCode_injective hb)
    · exact False.elim (left_ne_right a.1 b.2 ha)

private def intoCommon (A B : BethLevel) : UEl A ↪ PowerLevel Nat (common A B) :=
  PowerLevel.raise (Nat.le_max_left _ _)

private def intoCommonRight (A B : BethLevel) : UEl B ↪ PowerLevel Nat (common A B) :=
  PowerLevel.raise (Nat.le_max_right _ _)

private def sumEmbedding (A B : BethLevel) :
    (UEl A ⊕ UEl B) ↪ PowerLevel Nat (common A B + 2) :=
  (Function.Embedding.sumMap (intoCommon A B) (intoCommonRight A B)).trans sumCode

private def prodEmbedding (A B : BethLevel) :
    (UEl A × UEl B) ↪ PowerLevel Nat (common A B + 3) :=
  (Function.Embedding.prodMap (intoCommon A B) (intoCommonRight A B)).trans pairCode

private def graphCode {A B X : Type u} (ea : A ↪ X) (eb : B ↪ X) :
    (A → B) ↪ Set (Set (Set (Set X))) :=
  let pair : Code (A × B) (Set (Set (Set X))) := {
    code := (ea.prodMap eb).trans pairCode
    code_inj := ((ea.prodMap eb).trans pairCode).injective
  }
  let graph := FunCode.graph₂.comp pair.set
  { toFun := graph.code, inj' := graph.code_inj }

private def arrowEmbedding (A B : BethLevel) :
    (UEl A → UEl B) ↪ PowerLevel Nat (common A B + 4) :=
  graphCode (intoCommon A B) (intoCommonRight A B)

instance : SumClosed BethLevel where
  sum A B := ⟨common A B + 2⟩
  embed := sumEmbedding

instance : ProdClosed BethLevel where
  prod A B := ⟨common A B + 3⟩
  embed := prodEmbedding

instance : ArrowClosed BethLevel where
  arrow A B := ⟨common A B + 4⟩
  embed := arrowEmbedding

end BethLevel

end ProjectBeth
