import ProjectBeth.Defs.Hierarchy
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Image

universe u v

namespace ProjectBeth

def PowerLevel (Base : Type u) : Nat → Type u
  | 0 => Base
  | n + 1 => Set (PowerLevel Base n)

abbrev PowerTower (Base : Type u) := Σ n, PowerLevel Base n

namespace PowerLevel

def ix {Base : Type u} {n : Nat} : PowerLevel Base n ↪ PowerLevel Base (n + 1) where
  toFun x := by
    change Set (PowerLevel Base n)
    exact {x}
  inj' x y h := by
    change ({x} : Set (PowerLevel Base n)) = {y} at h
    exact Set.singleton_injective h

def hierarchy (Base : Type u) : NatHierarchy where
  level := PowerLevel Base
  lift _ := ix

def map (f : α → β) : ∀ n, PowerLevel α n → PowerLevel β n
  | 0 => f
  | n + 1 => Set.image (map f n)

theorem map_injective (hf : Function.Injective f) :
    ∀ n, Function.Injective (map f n)
  | 0 => hf
  | n + 1 => Set.image_injective.mpr (map_injective hf n)

def mapEmbedding (f : α ↪ β) (n : Nat) : PowerLevel α n ↪ PowerLevel β n where
  toFun := map f n
  inj' := map_injective f.injective n

@[simp]
theorem map_zero (f : α → β) (x : α) : map f 0 x = f x := rfl

@[simp]
theorem map_succ (f : α → β) (n) (s : Set (PowerLevel α n)) :
    map f (n + 1) s = (map f n) '' s := rfl

@[simp]
theorem map_ix (f : α → β) (n) (x : PowerLevel α n) :
    map f (n + 1) (ix x) = ix (map f n x) := by
  change (map f n) '' {x} = {map f n x}
  simp

def mapHom (f : α ↪ β) :
    NatHierarchy.Hom (hierarchy α) (hierarchy β) where
  app := mapEmbedding f
  naturality := map_ix f

end PowerLevel

namespace PowerTower

def ofLevel {Base : Type u} (n : Nat) : PowerLevel Base n ↪ PowerTower Base where
  toFun x := ⟨n, x⟩
  inj' _ _ h := by cases h; rfl

def base {Base : Type u} : Base ↪ PowerTower Base := ofLevel 0

def map (f : α → β) : PowerTower α → PowerTower β
  | ⟨n, x⟩ => ⟨n, PowerLevel.map f n x⟩

def mapEmbedding (f : α ↪ β) : PowerTower α ↪ PowerTower β where
  toFun := map f
  inj' x y h := by
    cases x with
    | mk nx x =>
      cases y with
      | mk ny y =>
        have hn : nx = ny := congrArg Sigma.fst h
        subst ny
        have hxy : PowerLevel.map f nx x = PowerLevel.map f nx y :=
          eq_of_heq (Sigma.mk.inj_iff.mp h).2
        have := PowerLevel.map_injective f.injective nx hxy
        subst y
        rfl

@[simp]
theorem map_ofLevel (f : α → β) (n) (x : PowerLevel α n) :
    map f (ofLevel n x) = ofLevel n (PowerLevel.map f n x) := rfl

end PowerTower

abbrev Beth := PowerLevel Nat
abbrev BethOmega := PowerTower Nat
abbrev KindOmega := PowerTower BethOmega

def finToNat (n : Nat) : Fin n ↪ Nat where
  toFun := Fin.val
  inj' := Fin.val_injective

def finToBethOmega (n : Nat) : Fin n ↪ BethOmega :=
  (finToNat n).trans PowerTower.base

def natToBethOmega : Nat ↪ BethOmega := PowerTower.base

def bethOmegaToKindOmega : BethOmega ↪ KindOmega := PowerTower.base

end ProjectBeth
