import ProjectBeth.Defs.Closure
import ProjectBeth.Defs.STLC.FixedPoints

universe u v

namespace ProjectBeth

structure InductiveTree (Label : Type u) where
  nodes : Set (Nat × Label)
  finite : nodes.Finite

abbrev CoinductiveTree (Label : Type u) := Set (Nat × Label)

namespace InductiveTree

def code {Label : Type u} : _root_.Code (InductiveTree Label) (Set (Nat × Label)) where
  code := nodes
  code_inj x y h := by
    cases x
    cases y
    cases h
    rfl

end InductiveTree

namespace FixedPointClosure

variable {U : Type v} [CoeSort U (Type u)]

def path (A : U) [NatClosed U] [ProdClosed U] : U :=
  ProdClosed.prod NatClosed.nat A

def tree (A : U) [NatClosed U] [ProdClosed U] [PowersetClosed U] : U :=
  PowersetClosed.powerset (path A)

noncomputable def pathEquiv (A : U) [NatExact U] [ProdExact U] :
    (Nat × UEl A) ≃ UEl (path A) :=
  ((NatExact.equiv (U := U)).prodCongr (Equiv.refl _)).trans
    (ProdExact.equiv NatClosed.nat A)

noncomputable def treeEquiv (A : U)
    [NatExact U] [ProdExact U] [PowersetExact U] :
    Set (Nat × UEl A) ≃ UEl (tree A) :=
  (Equiv.Set.congr (pathEquiv A)).trans
    (PowersetExact.equiv (path A))

noncomputable def inductiveCode (A : U)
    [NatExact U] [ProdExact U] [PowersetExact U] :
    _root_.Code (InductiveTree (UEl A)) (UEl (tree A)) :=
  InductiveTree.code.comp (_root_.Code.eqv (treeEquiv A))

noncomputable def coinductiveCode (A : U)
    [NatExact U] [ProdExact U] [PowersetExact U] :
    _root_.Code (CoinductiveTree (UEl A)) (UEl (tree A)) :=
  _root_.Code.eqv (treeEquiv A)

end FixedPointClosure

end ProjectBeth
