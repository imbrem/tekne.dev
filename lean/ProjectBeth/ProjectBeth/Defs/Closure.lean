import ProjectBeth.Basic
import ProjectBeth.Defs.PowerTower
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set

universe u v

namespace ProjectBeth

abbrev UEl {U : Type v} [CoeSort U (Type u)] (A : U) : Type u := A

class SumClosed (U : Type v) [CoeSort U (Type u)] where
  sum : U → U → U
  embed : ∀ (A B : U), (UEl A ⊕ UEl B) ↪ UEl (sum A B)

class ProdClosed (U : Type v) [CoeSort U (Type u)] where
  prod : U → U → U
  embed : ∀ (A B : U), (UEl A × UEl B) ↪ UEl (prod A B)

class ArrowClosed (U : Type v) [CoeSort U (Type u)] where
  arrow : U → U → U
  embed : ∀ (A B : U), (UEl A → UEl B) ↪ UEl (arrow A B)

class SumExact (U : Type v) [CoeSort U (Type u)] extends SumClosed U where
  equiv : ∀ (A B : U), (UEl A ⊕ UEl B) ≃ UEl (sum A B)
  embed_eq : ∀ (A B : U), toSumClosed.embed A B = (equiv A B).toEmbedding

class ProdExact (U : Type v) [CoeSort U (Type u)] extends ProdClosed U where
  equiv : ∀ (A B : U), (UEl A × UEl B) ≃ UEl (prod A B)
  embed_eq : ∀ (A B : U), toProdClosed.embed A B = (equiv A B).toEmbedding

class ArrowExact (U : Type v) [CoeSort U (Type u)] extends ArrowClosed U where
  equiv : ∀ (A B : U), (UEl A → UEl B) ≃ UEl (arrow A B)
  embed_eq : ∀ (A B : U), toArrowClosed.embed A B = (equiv A B).toEmbedding

class NatClosed (U : Type v) [CoeSort U (Type u)] where
  nat : U
  embed : Nat ↪ UEl nat

class NatExact (U : Type v) [CoeSort U (Type u)] extends NatClosed U where
  equiv : Nat ≃ UEl nat
  embed_eq : toNatClosed.embed = equiv.toEmbedding

class PowersetClosed (U : Type v) [CoeSort U (Type u)] where
  powerset : U → U
  embed : ∀ A, Set (UEl A) ↪ UEl (powerset A)

class PowersetExact (U : Type v) [CoeSort U (Type u)] extends PowersetClosed U where
  equiv : ∀ A, Set (UEl A) ≃ UEl (powerset A)
  embed_eq : ∀ A, toPowersetClosed.embed A = (equiv A).toEmbedding

structure FinLevel where
  card : Nat

instance : CoeSort FinLevel Type where
  coe n := Fin n.card

noncomputable instance : SumExact FinLevel where
  sum A B := ⟨Fintype.card (Fin A.card ⊕ Fin B.card)⟩
  embed A B := (Fintype.equivFin (Fin A.card ⊕ Fin B.card)).toEmbedding
  equiv A B := Fintype.equivFin (Fin A.card ⊕ Fin B.card)
  embed_eq _ _ := rfl

noncomputable instance : ProdExact FinLevel where
  prod A B := ⟨Fintype.card (Fin A.card × Fin B.card)⟩
  embed A B := (Fintype.equivFin (Fin A.card × Fin B.card)).toEmbedding
  equiv A B := Fintype.equivFin (Fin A.card × Fin B.card)
  embed_eq _ _ := rfl

noncomputable instance : ArrowExact FinLevel where
  arrow A B := ⟨Fintype.card (Fin A.card → Fin B.card)⟩
  embed A B := (Fintype.equivFin (Fin A.card → Fin B.card)).toEmbedding
  equiv A B := Fintype.equivFin (Fin A.card → Fin B.card)
  embed_eq _ _ := rfl

structure BoundedSet (Base : Type u) where
  level : Nat
  carrier : Set (PowerLevel Base level)

instance {Base : Type u} : CoeSort (BoundedSet Base) (Type u) where
  coe A := A.carrier

end ProjectBeth
