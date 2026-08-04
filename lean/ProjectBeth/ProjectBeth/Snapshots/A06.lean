import ProjectBeth.Defs.PowerTower

universe u

namespace ProjectBeth.Snapshots.A06

abbrev Beth := PowerLevel Nat
abbrev BethOmega := PowerTower Nat

def ix {Base : Type u} {n : Nat} :
    PowerLevel Base n ↪ PowerLevel Base (n + 1) :=
  PowerLevel.ix

theorem cantor (f : α → Set α) : ¬Function.Surjective f := by
  intro hf
  let diagonal : Set α := {x | x ∉ f x}
  obtain ⟨x, hx⟩ := hf diagonal
  by_cases h : x ∈ f x
  · have hd : x ∈ diagonal := by rw [← hx]; exact h
    have hn : x ∉ f x := by simpa only [diagonal, Set.mem_setOf_eq] using hd
    exact hn h
  · have hd : x ∈ diagonal := by simpa only [diagonal, Set.mem_setOf_eq]
    have : x ∈ f x := by rw [hx]; exact hd
    exact h this

def map (f : α → β) (n : Nat) :
    PowerLevel α n → PowerLevel β n :=
  PowerLevel.map f n

def mapEmbedding (f : α ↪ β) (n : Nat) :
    PowerLevel α n ↪ PowerLevel β n :=
  PowerLevel.mapEmbedding f n

theorem map_ix (f : α → β) (n : Nat) (x : PowerLevel α n) :
    map f (n + 1) (ix x) = ix (map f n x) :=
  PowerLevel.map_ix f n x

def finTowerMap (n : Nat) : PowerTower (Fin n) ↪ BethOmega :=
  PowerTower.mapEmbedding (finToNat n)

end ProjectBeth.Snapshots.A06
