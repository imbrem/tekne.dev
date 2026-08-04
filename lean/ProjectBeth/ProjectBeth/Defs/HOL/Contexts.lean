import ProjectBeth.Defs.HOL.Kernel
import Mathlib.Data.Finset.Basic

namespace ProjectBeth.HOL.Kernel

noncomputable section
attribute [local instance] Classical.propDecidable

def Tm.IsTrue (p : Tm Γ Ty.bool) (ρ : Env Γ) : Prop :=
  (p.eval ρ).down = true

theorem uliftBool_eq_iff {x y : ULift Bool} : x = y ↔ x.down = y.down := by
  constructor
  · exact congrArg ULift.down
  · exact uliftBool_ext

theorem Tm.isTrue_eq (x y : Tm Γ A) (ρ : Env Γ) :
    (Tm.eq x y).IsTrue ρ ↔ x.eval ρ = y.eval ρ := by
  by_cases h : x.eval ρ = y.eval ρ <;> simp [IsTrue, Tm.eval, h]

theorem Tm.isTrue_conj (p q : Tm Γ Ty.bool) (ρ : Env Γ) :
    (p.conj q).IsTrue ρ ↔ p.IsTrue ρ ∧ q.IsTrue ρ := by
  cases hp : (p.eval ρ).down <;> cases hq : (q.eval ρ).down <;>
    simp [IsTrue, Tm.eval, hp, hq]

inductive AssumptionTree (α : Type 2)
  | empty
  | leaf (value : α)
  | node (left right : AssumptionTree α)

namespace AssumptionTree

def Mem (x : α) : AssumptionTree α → Prop
  | .empty => False
  | .leaf y => x = y
  | .node l r => Mem x l ∨ Mem x r

def holds (C : AssumptionTree (Tm Γ Ty.bool)) (ρ : Env Γ) : Prop :=
  ∀ p, Mem p C → p.IsTrue ρ

def ofList : List α → AssumptionTree α
  | [] => .empty
  | x :: xs => .node (.leaf x) (ofList xs)

theorem mem_ofList {x : α} {xs : List α} : Mem x (ofList xs) ↔ x ∈ xs := by
  induction xs with
  | nil => simp [ofList, Mem]
  | cons y ys ih => simp [ofList, Mem, ih]

def foldConj : AssumptionTree (Tm Γ Ty.bool) → Tm Γ Ty.bool
  | .empty => .bool true
  | .leaf p => p
  | .node l r => l.foldConj.conj r.foldConj

theorem isTrue_foldConj (C : AssumptionTree (Tm Γ Ty.bool)) (ρ : Env Γ) :
    C.foldConj.IsTrue ρ ↔ C.holds ρ := by
  induction C with
  | empty => simp [foldConj, holds, Mem, Tm.IsTrue, Tm.eval]
  | leaf p => simp [foldConj, holds, Mem]
  | node l r ihl ihr =>
    rw [foldConj, Tm.isTrue_conj, ihl, ihr]
    simp only [holds, Mem]
    constructor
    · rintro ⟨hl, hr⟩ p (hp | hp)
      · exact hl p hp
      · exact hr p hp
    · intro h
      exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩

end AssumptionTree

abbrev HOLLightContext (Γ : Ctx) := Finset (Tm Γ Ty.bool)

noncomputable def HOLLightContext.Mem (p : Tm Γ Ty.bool) (C : HOLLightContext Γ) : Prop := by
  letI : DecidableEq (Tm Γ Ty.bool) := Classical.decEq _
  exact p ∈ C

def HOLLightContext.holds (C : HOLLightContext Γ) (ρ : Env Γ) : Prop :=
  ∀ p, C.Mem p → p.IsTrue ρ

noncomputable def HOLLightContext.toTree (C : HOLLightContext Γ) :
    AssumptionTree (Tm Γ Ty.bool) :=
  AssumptionTree.ofList C.toList

theorem HOLLightContext.mem_toTree (C : HOLLightContext Γ) (p : Tm Γ Ty.bool) :
    AssumptionTree.Mem p C.toTree ↔ C.Mem p := by
  letI : DecidableEq (Tm Γ Ty.bool) := Classical.decEq _
  simp [toTree, AssumptionTree.mem_ofList, Mem]

theorem HOLLightContext.holds_toTree (C : HOLLightContext Γ) (ρ : Env Γ) :
    C.toTree.holds ρ ↔ C.holds ρ := by
  simp only [AssumptionTree.holds, HOLLightContext.holds, mem_toTree]

abbrev HOL4Context (Γ : Ctx) := AssumptionTree (Tm Γ Ty.bool)

abbrev ConjContext (Γ : Ctx) := Tm Γ Ty.bool

def ConjContext.holds (p : ConjContext Γ) (ρ : Env Γ) : Prop := p.IsTrue ρ

noncomputable def HOLLightContext.toConj (C : HOLLightContext Γ) : ConjContext Γ :=
  C.toTree.foldConj

theorem HOLLightContext.semantic_equivalence (C : HOLLightContext Γ) (ρ : Env Γ) :
    C.holds ρ ↔ C.toTree.holds ρ ∧ C.toConj.holds ρ := by
  change C.holds ρ ↔ C.toTree.holds ρ ∧ C.toTree.foldConj.IsTrue ρ
  rw [AssumptionTree.isTrue_foldConj]
  exact ⟨fun h => ⟨C.holds_toTree ρ |>.2 h, C.holds_toTree ρ |>.2 h⟩,
    fun h => C.holds_toTree ρ |>.1 h.1⟩

end


end ProjectBeth.HOL.Kernel
