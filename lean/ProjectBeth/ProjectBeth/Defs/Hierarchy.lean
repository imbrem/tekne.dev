import Mathlib.Data.FunLike.Embedding
import Mathlib.Order.Hom.Basic

universe u v w

namespace ProjectBeth

class FamilyLike (F : Type w) (I : outParam (Type u))
    (U : outParam (Type v)) extends FunLike F I U

structure NatHierarchy where
  level : Nat → Type v
  lift : ∀ i, level i ↪ level (i + 1)

namespace NatHierarchy

structure Hom (F G : NatHierarchy) where
  app : ∀ i, F.level i ↪ G.level i
  naturality : ∀ i x, app (i + 1) (F.lift i x) = G.lift i (app i x)

def Hom.id (F : NatHierarchy) : Hom F F where
  app _ := Function.Embedding.refl _
  naturality _ _ := rfl

def Hom.comp {F G H : NatHierarchy}
    (g : Hom G H) (f : Hom F G) : Hom F H where
  app i := (f.app i).trans (g.app i)
  naturality i x := by
    change g.app (i + 1) (f.app (i + 1) (F.lift i x)) =
      H.lift i (g.app i (f.app i x))
    rw [f.naturality, g.naturality]

end NatHierarchy

structure OrderHierarchy (I : Type u) [Preorder I] where
  level : I → Type v
  lift : ∀ {i j}, i ≤ j → level i ↪ level j
  lift_refl : ∀ i x, lift (i := i) (j := i) le_rfl x = x
  lift_trans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) x,
    lift (hij.trans hjk) x = lift hjk (lift hij x)

namespace OrderHierarchy

structure Hom {I : Type u} [Preorder I]
    (F G : OrderHierarchy I) where
  app : ∀ i, F.level i ↪ G.level i
  naturality : ∀ {i j} (h : i ≤ j) x,
    app j (F.lift h x) = G.lift h (app i x)

def Hom.id {I : Type u} [Preorder I] (F : OrderHierarchy I) : Hom F F where
  app _ := Function.Embedding.refl _
  naturality _ _ := rfl

def Hom.comp {I : Type u} [Preorder I] {F G H : OrderHierarchy I}
    (g : Hom G H) (f : Hom F G) : Hom F H where
  app i := (f.app i).trans (g.app i)
  naturality h x := by
    change g.app _ (f.app _ (F.lift h x)) = H.lift h (g.app _ (f.app _ x))
    rw [f.naturality, g.naturality]

structure ReindexHom {I : Type u} {J : Type v} [Preorder I] [Preorder J]
    (F : OrderHierarchy I) (G : OrderHierarchy J) where
  onIndex : I →o J
  app : ∀ i, F.level i ↪ G.level (onIndex i)
  naturality : ∀ {i j} (h : i ≤ j) x,
    app j (F.lift h x) = G.lift (onIndex.monotone h) (app i x)

end OrderHierarchy

end ProjectBeth
