import ProjectBeth.Defs.Hierarchy
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Image

/-! Iterated powersets, their sigma tower, and functorial maps. -/

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

theorem map_surjective {f : α → β} (hf : Function.Surjective f) :
    ∀ n, Function.Surjective (map f n)
  | 0 => hf
  | n + 1 => by
      change Function.Surjective (Set.image (map f n))
      intro s
      let preimage : Set (PowerLevel α n) := {x | map f n x ∈ s}
      refine ⟨preimage, Set.Subset.antisymm ?_ ?_⟩
      · rintro y ⟨x, hx, rfl⟩
        exact hx
      · intro y hy
        obtain ⟨x, rfl⟩ := map_surjective hf n y
        exact ⟨x, hy, rfl⟩

def mapEmbedding (f : α ↪ β) (n : Nat) : PowerLevel α n ↪ PowerLevel β n where
  toFun := map f n
  inj' := map_injective f.injective n

noncomputable def mapEquiv (f : α ≃ β) (n : Nat) :
    PowerLevel α n ≃ PowerLevel β n :=
  Equiv.ofBijective (map f n) ⟨map_injective f.injective n, map_surjective f.surjective n⟩

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

@[simp]
theorem map_id (n : Nat) (x : PowerLevel α n) : map id n x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (map id n) '' x = x
      rw [show map id n = id from funext ih]
      exact Set.image_id x

theorem map_comp (g : β → γ) (f : α → β) (n : Nat)
    (x : PowerLevel α n) : map (g ∘ f) n x = map g n (map f n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (map (g ∘ f) n) '' x = (map g n) '' ((map f n) '' x)
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨map f n z, ⟨z, hz, rfl⟩, (ih z).symm⟩
      · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, ih a⟩

def mapHom (f : α ↪ β) :
    NatHierarchy.Hom (hierarchy α) (hierarchy β) where
  app := mapEmbedding f
  naturality := map_ix f

@[simp]
theorem mapHom_refl :
    mapHom (Function.Embedding.refl α) = NatHierarchy.Hom.id (hierarchy α) := by
  ext n x
  exact map_id n x

theorem mapHom_trans (f : α ↪ β) (g : β ↪ γ) :
    mapHom (f.trans g) = NatHierarchy.Hom.comp (mapHom g) (mapHom f) := by
  ext n x
  exact map_comp g f n x

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

noncomputable def mapEquiv (f : α ≃ β) : PowerTower α ≃ PowerTower β :=
  Equiv.ofBijective (map f) ⟨(mapEmbedding f.toEmbedding).injective, fun y => by
    rcases y with ⟨n, y⟩
    obtain ⟨x, rfl⟩ := PowerLevel.map_surjective f.surjective n y
    exact ⟨⟨n, x⟩, rfl⟩⟩

@[simp]
theorem map_ofLevel (f : α → β) (n) (x : PowerLevel α n) :
    map f (ofLevel n x) = ofLevel n (PowerLevel.map f n x) := rfl

@[simp]
theorem map_id (x : PowerTower α) : map id x = x := by
  rcases x with ⟨n, x⟩
  simp [map]

theorem map_comp (g : β → γ) (f : α → β) (x : PowerTower α) :
    map (g ∘ f) x = map g (map f x) := by
  rcases x with ⟨n, x⟩
  simp [map, PowerLevel.map_comp]

@[simp]
theorem mapEmbedding_refl :
    mapEmbedding (Function.Embedding.refl α) = Function.Embedding.refl (PowerTower α) := by
  apply Function.Embedding.ext
  intro x
  exact map_id x

theorem mapEmbedding_trans (f : α ↪ β) (g : β ↪ γ) :
    mapEmbedding (f.trans g) = (mapEmbedding f).trans (mapEmbedding g) := by
  apply Function.Embedding.ext
  intro x
  exact map_comp g f x

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
