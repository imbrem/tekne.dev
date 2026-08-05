import ProjectBeth.Defs.SystemF.ContextMorphisms

namespace ProjectBeth.SystemF.Syntax.DeBruijn

/-- The shared System F kernel is the unbounded, fully de Bruijn representation. -/
abbrev Ty := Inductive.Ty
abbrev Tm := Inductive.Tm
abbrev HasType := Inductive.HasType
abbrev Derivation := Inductive.Semantics.Derivation
abbrev renameTy := Inductive.Ty.rename
abbrev substTy := Inductive.Ty.subst
abbrev rename := Inductive.Tm.rename
abbrev renameTypes := Inductive.Tm.renameTy
abbrev subst := Inductive.Tm.subst
abbrev substTypes := Inductive.Tm.substTy

end ProjectBeth.SystemF.Syntax.DeBruijn
