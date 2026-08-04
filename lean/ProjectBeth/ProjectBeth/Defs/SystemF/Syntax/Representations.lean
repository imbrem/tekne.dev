import ProjectBeth.Defs.SystemF.Kernel
import ProjectBeth.Defs.SystemF.Syntax.Named
import ProjectBeth.Defs.SystemF.Syntax.LocallyNameless
import ProjectBeth.Defs.SystemF.Syntax.DeBruijn
import ProjectBeth.Defs.SystemF.Syntax.Bounded
import ProjectBeth.Defs.SystemF.Syntax.Intrinsic
import ProjectBeth.Defs.SystemF.Syntax.Types

namespace ProjectBeth.SystemF.Syntax

namespace Raw
abbrev Ty := DeBruijn.Ty
abbrev Tm := DeBruijn.Tm
abbrev HasType := DeBruijn.HasType
abbrev renameTy := DeBruijn.renameTypes
abbrev rename := DeBruijn.rename
abbrev substTy := DeBruijn.substTypes
abbrev subst := DeBruijn.subst
end Raw

namespace DerivationBounded
/-- The former proof-carrying bounded view, retained independently of the
finitely scoped syntax in `Syntax.Bounded`. -/
abbrev Tm (Delta : Nat) (Gamma : List Inductive.Ty) :=
  { p : Inductive.Tm × Inductive.Ty // Inductive.HasType Delta Gamma p.1 p.2 }
end DerivationBounded

namespace Shallow
abbrev Universe := ProjectBeth.SystemF.Universe
abbrev Ty := ProjectBeth.SystemF.Ty
abbrev Tm := ProjectBeth.SystemF.Tm
end Shallow

end ProjectBeth.SystemF.Syntax
