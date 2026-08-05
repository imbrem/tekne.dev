import ProjectBeth.Defs.Syntax.Alpha
import ProjectBeth.Defs.Syntax.BoundedLaws
import ProjectBeth.Defs.Syntax.IntrinsicLaws
import ProjectBeth.Defs.Syntax.LocallyNamelessLaws
import ProjectBeth.Defs.Syntax.NamedLaws
import ProjectBeth.Defs.Syntax.NatReifier

universe u v

namespace ProjectBeth.STLC.Syntax

variable {Name : Type u} {Name' : Type v}

namespace DeBruijn
abbrev Tm := ProjectBeth.Syntax.Untyped.Tm
abbrev rename := ProjectBeth.Syntax.Untyped.rename
abbrev subst := ProjectBeth.Syntax.Untyped.subst
end DeBruijn

namespace Bounded
abbrev Tm := ProjectBeth.Syntax.Bounded.Tm
def erase (t : Tm n) : DeBruijn.Tm := ProjectBeth.Syntax.Bounded.erase t
def check (n : Nat) (t : DeBruijn.Tm) : Option (Tm n) :=
  ProjectBeth.Syntax.Bounded.check n t
end Bounded

namespace Named
abbrev Tm (Name : Type u) := ProjectBeth.Syntax.Named.Tm Name
def rename (f : Name → Name') (t : Tm Name) : Tm Name' :=
  ProjectBeth.Syntax.Named.rename f t
end Named

namespace LocallyNameless
abbrev Var (Name : Type u) := ProjectBeth.Syntax.LocallyNameless.Var Name
abbrev Tm (Name : Type u) := ProjectBeth.Syntax.LocallyNameless.Tm Name
def ofNamed [DecidableEq Name] (Γ : List Name) (t : Named.Tm Name) : Tm Name :=
  ProjectBeth.Syntax.LocallyNameless.ofNamed Γ t
def close [DecidableEq Name] (x : Name) (k : Nat) (t : Tm Name) : Tm Name :=
  ProjectBeth.Syntax.LocallyNameless.close x k t
def openAt (x : Name) (k : Nat) (t : Tm Name) : Tm Name :=
  ProjectBeth.Syntax.LocallyNameless.openAt x k t
end LocallyNameless

namespace Intrinsic
abbrev Ty := ProjectBeth.Syntax.Intrinsic.Ty
abbrev Tm := @ProjectBeth.Syntax.Intrinsic.Tm
abbrev erase := @ProjectBeth.Syntax.Intrinsic.erase
abbrev HasType := @ProjectBeth.Syntax.Intrinsic.HasType
end Intrinsic

namespace Alpha
abbrev Relation [DecidableEq Name] (t s : Named.Tm Name) : Prop :=
  ProjectBeth.Syntax.Named.Alpha t s
abbrev QuotientTm (Name : Type u) [DecidableEq Name] :=
  ProjectBeth.Syntax.Named.AlphaQuotient.Q Name
def aconv [DecidableEq Name] (t s : Named.Tm Name) : Bool :=
  ProjectBeth.Syntax.Named.aconv t s
end Alpha

end ProjectBeth.STLC.Syntax
