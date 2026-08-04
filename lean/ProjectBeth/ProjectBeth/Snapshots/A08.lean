import ProjectBeth.Defs.STLC.Variants
import ProjectBeth.Snapshots.A07

universe u

namespace ProjectBeth.Snapshots.A08

namespace Arrow

abbrev Ty := STLC.Arrow.Ty

def id {Base : Type u} {A : Ty Base} :
    STLC.Arrow.Tm (Base := Base) [] (.arr A A) :=
  .lam (.var .here)

end Arrow

namespace ArrowProd

abbrev Ty := STLC.ArrowProd.Ty

def swap {Base : Type u} {A B : Ty Base} :
    STLC.ArrowProd.Tm (Base := Base) [] (.arr (.prod A B) (.prod B A)) :=
  .lam (.pair (.snd (.var .here)) (.fst (.var .here)))

end ArrowProd

namespace ArrowProdSum

abbrev Ty := STLC.ArrowProdSum.Ty

def swap {Base : Type u} {A B : Ty Base} :
    STLC.ArrowProdSum.Tm (Base := Base) [] (.arr (.sum A B) (.sum B A)) :=
  .lam (.case (.var .here)
    (.inr (.var .here))
    (.inl (.var .here)))

end ArrowProdSum

namespace Full

abbrev Ty := STLC.Full.Ty

def not {Base : Type u} :
    STLC.Full.Tm (Base := Base) [] (.arr .bool .bool) :=
  .lam (.ite (.var .here) (.bool false) (.bool true))

def one {Base : Type u} : STLC.Full.Tm (Base := Base) [] .nat := .nat 1

end Full

end ProjectBeth.Snapshots.A08
