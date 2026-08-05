import ProjectBeth.Defs.FixedPointClosure
import ProjectBeth.Defs.STLC.ExtendedVariants
import ProjectBeth.Defs.STLC.Extenders
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

namespace Let

def id {Base : Type u} {A : STLC.Let.Ty Base} :
    STLC.Let.Tm (Base := Base) [] (.arr A A) :=
  .lam (.letE (.var .here) (.var .here))

end Let

namespace Cases

def either {Base : Type u} {A B C : STLC.Cases.Ty Base} :
    STLC.Cases.Tm (Base := Base) []
      (.arr (.sum A B) (.arr (.arr A C) (.arr (.arr B C) C))) :=
  .lam (.lam (.lam
    (.case (.var (.there (.there .here)))
      (.app (.var (.there (.there .here))) (.var .here))
      (.app (.var (.there .here)) (.var .here)))))

end Cases

namespace LetCases

def bind {Base : Type u} {A B : STLC.LetCases.Ty Base} :
    STLC.LetCases.Tm (Base := Base) [] (.arr A (.arr (.arr A B) B)) :=
  .lam (.lam (.letE (.var (.there .here))
    (.app (.var (.there .here)) (.var .here))))

end LetCases

namespace Inductive

def listPoly {Base : Type u} (A : Base) : STLC.Poly Base :=
  .sum (.const A) (.prod (.const A) .var)

abbrev ListCarrier {Base : Type u} (El : Base → Type u) (A : Base) :=
  STLC.Inductive.Carrier El (listPoly A)

end Inductive

namespace Coinductive

def streamPoly {Base : Type u} (A : Base) : STLC.Poly Base :=
  .prod (.const A) .var

def readerTreePoly {Base : Type u} (A : Base) : STLC.Poly Base :=
  .pow A

abbrev StreamCarrier {Base : Type u} (El : Base → Type u) (A : Base) :=
  STLC.Coinductive.Carrier El (streamPoly A)

end Coinductive

namespace Extenders


open STLC.Ext

abbrev Ty (Base : Type u) := STLC.Arrow.Ty Base
abbrev Ctx (Base : Type u) := List (Ty Base)
abbrev Variables {Base : Type u} : Lang (Ctx Base) (Ty Base) := STLC.Var

def push {Base : Type u} : Ty Base → Ctx Base → Ctx Base := List.cons

abbrev Lam {Base : Type u} (V : Lang (Ctx Base) (Ty Base)) :=
  STLC.Ext.Lam push STLC.Arrow.Ty.arr V

abbrev Let {Base : Type u} (V : Lang (Ctx Base) (Ty Base)) :=
  STLC.Ext.Let push V

abbrev LetLam {Base : Type u} (V : Lang (Ctx Base) (Ty Base)) :=
  STLC.Ext.LetLam push STLC.Arrow.Ty.arr V

def flattenLam {Base : Type u} :
    Hom (Lam (Lam (Variables (Base := Base)))) (Lam (Variables (Base := Base))) :=
  STLC.Ext.Lam.flatten

def eliminateLet {Base : Type u} :
    Hom (Let (Lam (Variables (Base := Base)))) (Lam (Variables (Base := Base))) :=
  STLC.Ext.Let.intoLam

def lamLetToCombined {Base : Type u} :
    Hom (Lam (Let (Variables (Base := Base)))) (LetLam (Variables (Base := Base))) :=
  STLC.Ext.LetLam.fromLamLet

def letLamToCombined {Base : Type u} :
    Hom (Let (Lam (Variables (Base := Base)))) (LetLam (Variables (Base := Base))) :=
  STLC.Ext.LetLam.fromLetLam

end Extenders

end ProjectBeth.Snapshots.A08
