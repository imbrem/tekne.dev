import ProjectBeth.Defs.HOLOmega.Semantics
import ProjectBeth.Defs.FixedPointClosure
import ProjectBeth.Snapshots.A11

namespace ProjectBeth.Snapshots.A12

def finiteToNat (n : Nat) :
    NatHierarchy.Hom (PowerLevel.hierarchy (Fin n)) (PowerLevel.hierarchy Nat) :=
  PowerLevel.mapHom (finToNat n)

def natToTypes :
    NatHierarchy.Hom (PowerLevel.hierarchy Nat) (PowerLevel.hierarchy BethOmega) :=
  PowerLevel.mapHom natToBethOmega

def finiteToTypes (n : Nat) :
    NatHierarchy.Hom (PowerLevel.hierarchy (Fin n))
      (PowerLevel.hierarchy BethOmega) :=
  NatHierarchy.Hom.comp natToTypes (finiteToNat n)

theorem finite_ix_commutes (n level : Nat) (x : PowerLevel (Fin n) level) :
    (finiteToNat n).app (level + 1) (PowerLevel.ix x) =
      PowerLevel.ix ((finiteToNat n).app level x) :=
  (finiteToNat n).naturality level x

theorem nat_ix_commutes (level : Nat) (x : PowerLevel Nat level) :
    natToTypes.app (level + 1) (PowerLevel.ix x) =
      PowerLevel.ix (natToTypes.app level x) :=
  natToTypes.naturality level x

end ProjectBeth.Snapshots.A12
