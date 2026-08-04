import ProjectBeth.Defs.Closure

universe u v

namespace ProjectBeth

/-- Every closure embedding determines a code whose carrier is precisely its
image.  No surjectivity is asserted by a plain closure class. -/
def Code.ofEmbedding (e : α ↪ β) : _root_.Code α β where
  code := e
  code_inj := e.injective

@[simp]
theorem Code.car_ofEmbedding (e : α ↪ β) :
    (Code.ofEmbedding e : Set β) = Set.range e := rfl

namespace SumClosed

def code [CoeSort U (Type u)] [SumClosed U] (A B : U) :
    _root_.Code (UEl A ⊕ UEl B) (UEl (sum A B)) :=
  Code.ofEmbedding (embed A B)

end SumClosed

namespace ProdClosed

def code [CoeSort U (Type u)] [ProdClosed U] (A B : U) :
    _root_.Code (UEl A × UEl B) (UEl (prod A B)) :=
  Code.ofEmbedding (embed A B)

end ProdClosed

namespace ArrowClosed

def code [CoeSort U (Type u)] [ArrowClosed U] (A B : U) :
    _root_.Code (UEl A → UEl B) (UEl (arrow A B)) :=
  Code.ofEmbedding (embed A B)

end ArrowClosed

namespace PowersetClosed

def code [CoeSort U (Type u)] [PowersetClosed U] (A : U) :
    _root_.Code (Set (UEl A)) (UEl (powerset A)) :=
  Code.ofEmbedding (embed A)

end PowersetClosed

theorem SumExact.embed_surjective [CoeSort U (Type u)] [SumExact U]
    (A B : U) : Function.Surjective (SumClosed.embed A B) := by
  rw [SumExact.embed_eq]
  exact (SumExact.equiv A B).surjective

theorem ProdExact.embed_surjective [CoeSort U (Type u)] [ProdExact U]
    (A B : U) : Function.Surjective (ProdClosed.embed A B) := by
  rw [ProdExact.embed_eq]
  exact (ProdExact.equiv A B).surjective

theorem ArrowExact.embed_surjective [CoeSort U (Type u)] [ArrowExact U]
    (A B : U) : Function.Surjective (ArrowClosed.embed A B) := by
  rw [ArrowExact.embed_eq]
  exact (ArrowExact.equiv A B).surjective

theorem NatExact.embed_surjective [CoeSort U (Type u)] [NatExact U] :
    Function.Surjective (NatClosed.embed (U := U)) := by
  rw [NatExact.embed_eq]
  exact NatExact.equiv.surjective

theorem PowersetExact.embed_surjective [CoeSort U (Type u)] [PowersetExact U]
    (A : U) : Function.Surjective (PowersetClosed.embed A) := by
  rw [PowersetExact.embed_eq]
  exact (PowersetExact.equiv A).surjective

end ProjectBeth
