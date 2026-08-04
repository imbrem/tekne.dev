import ProjectBeth.Defs.HOL.Semantics
import ProjectBeth.Snapshots.A09

universe u

namespace ProjectBeth.Snapshots.A10

open ProjectBeth.HOL

theorem sub_wf {Base : Type u} {A : Ty Base} {p : Tm Base}
    (hA : A.Wf) (hp : HasType [A] p .bool) : (Ty.sub A p).Wf :=
  .sub hA hp

theorem sub_inhabited (α : Type u) [Inhabited α] (P : α → Prop) :
    Nonempty (TotalSubtype α P) :=
  TotalSubtype.nonempty P

theorem rep_abs {α : Type u} [Inhabited α] {P : α → Prop}
    {x : α} (hx : P x) :
    TotalSubtype.rep (TotalSubtype.abs P x) = x :=
  TotalSubtype.rep_abs_of hx

theorem abs_rep {α : Type u} [Inhabited α] {P : α → Prop}
    (x : TotalSubtype α P) :
    TotalSubtype.abs P (TotalSubtype.rep x) = x :=
  TotalSubtype.abs_rep x

theorem conservative_expansion (α : Type u) [Inhabited α] (P : α → Prop) :
    Nonempty (Expansion α P) :=
  total_expansion_exists α P

end ProjectBeth.Snapshots.A10
