import ProjectBeth.Defs.HOLOmega.Semantics
import ProjectBeth.Snapshots.A10

namespace ProjectBeth.Snapshots.A11

open ProjectBeth.HOLOmega

def higherKind : Kind := .arr (.arr .star .star) .star

example : Kind.denote BethOmega higherKind =
    ((Set BethOmega → Set BethOmega) → Set BethOmega) :=
  rfl

def natIntoKinds : Nat ↪ KindOmega :=
  natToBethOmega.trans bethOmegaToKindOmega

def typesIntoKinds : BethOmega ↪ KindOmega :=
  bethOmegaToKindOmega

end ProjectBeth.Snapshots.A11
