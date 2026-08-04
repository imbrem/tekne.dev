import ProjectBeth.Defs.STLC.Syntax.Representations

namespace ProjectBeth.STLC.Syntax.Intrinsic

universe u

abbrev Typed {Base : Type u} (Gamma : List (Ty Base)) (A : Ty Base) :=
  Tm Gamma A

end ProjectBeth.STLC.Syntax.Intrinsic
