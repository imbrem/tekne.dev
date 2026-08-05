import ProjectBeth.Defs.SystemF.Kernel

universe u

namespace ProjectBeth.SystemF.Church

open ProjectBeth.SystemF

variable (U : Universe)

def BoolTy : Ty U 0 :=
  Ty.all U (Ty.arr U (Ty.var U 0) (Ty.arr U (Ty.var U 0) (Ty.var U 0)))

def NatTy : Ty U 0 :=
  Ty.all U (Ty.arr U (Ty.arr U (Ty.var U 0) (Ty.var U 0))
    (Ty.arr U (Ty.var U 0) (Ty.var U 0)))

def iterate (n : Nat) (s : α → α) (z : α) : α :=
  Nat.rec z (fun _ x => s x) n

def true : Tm U Γ (BoolTy U) :=
  fun _ _ => (U.allEquiv fun X => U.arr X (U.arr X X)).symm
    (fun X => (U.arrEquiv X (U.arr X X)).symm
      (fun x => (U.arrEquiv X X).symm (fun _ => x)))

def false : Tm U Γ (BoolTy U) :=
  fun _ _ => (U.allEquiv fun X => U.arr X (U.arr X X)).symm
    (fun X => (U.arrEquiv X (U.arr X X)).symm
      (fun _ => (U.arrEquiv X X).symm (fun y => y)))

def numeral (n : Nat) : Tm U Γ (NatTy U) :=
  fun _ _ => (U.allEquiv fun X => U.arr (U.arr X X) (U.arr X X)).symm
    (fun X => (U.arrEquiv (U.arr X X) (U.arr X X)).symm
      (fun s => (U.arrEquiv X X).symm (fun z =>
        iterate n (fun x => U.arrEquiv X X s x) z)))

def decodeBool (t : Tm U Γ (BoolTy U)) : Tm U Γ (Ty.bool U) :=
  fun ρ γ =>
    let f := U.allEquiv (fun X => U.arr X (U.arr X X)) (t ρ γ) U.bool
    U.arrEquiv U.bool (U.arr U.bool U.bool) f (U.boolEquiv.symm Bool.true)
      |> fun g => U.arrEquiv U.bool U.bool g (U.boolEquiv.symm Bool.false)

def decodeNat (t : Tm U Γ (NatTy U)) : Tm U Γ (Ty.nat U) :=
  fun ρ γ =>
    let f := U.allEquiv (fun X => U.arr (U.arr X X) (U.arr X X)) (t ρ γ) U.nat
    let succCode := (U.arrEquiv U.nat U.nat).symm
      (fun x => U.natEquiv.symm (U.natEquiv x + 1))
    let g := U.arrEquiv (U.arr U.nat U.nat) (U.arr U.nat U.nat) f succCode
    U.arrEquiv U.nat U.nat g (U.natEquiv.symm 0)

@[simp] theorem decode_true : decodeBool U (Γ := Γ) (true U) = Tm.bool U Bool.true := by
  funext ρ γ
  simp [decodeBool, true, Tm.bool]
  rfl

@[simp] theorem decode_false : decodeBool U (Γ := Γ) (false U) = Tm.bool U Bool.false := by
  funext ρ γ
  simp [decodeBool, false, Tm.bool]
  rfl

@[simp] theorem decode_numeral (n : Nat) :
    decodeNat U (Γ := Γ) (numeral U n) = Tm.nat U n := by
  funext ρ γ
  simp [decodeNat, numeral, Tm.nat]
  induction n with
  | zero => rfl
  | succ n ih =>
    change U.natEquiv.symm
      (U.natEquiv (iterate n (fun x => U.natEquiv.symm (U.natEquiv x + 1))
        (U.natEquiv.symm 0)) + 1) = U.natEquiv.symm (n + 1)
    rw [ih, Equiv.apply_symm_apply]

/-- Classical research semantics for Hilbert choice over representable System F
terms.  The predicate ranges over syntax/denotations supplied by the caller;
there is no claim that arbitrary semantic elements are representable. -/
noncomputable def epsilonTerm (fallback : Tm U Γ A) (P : Tm U Γ A → Prop) :
    Tm U Γ A := by
  classical
  exact if h : ∃ t, P t then Classical.choose h else fallback

theorem epsilonTerm_spec (fallback : Tm U Γ A) (P : Tm U Γ A → Prop)
    (h : ∃ t, P t) : P (epsilonTerm U fallback P) := by
  classical
  simp [epsilonTerm, h, Classical.choose_spec h]

theorem epsilonTerm_fallback (fallback : Tm U Γ A) (P : Tm U Γ A → Prop)
    (h : ¬∃ t, P t) : epsilonTerm U fallback P = fallback := by
  classical
  simp [epsilonTerm, h]

def Representable {n : Nat} {Γ : Ctx U n} {A : Ty U n}
    (ρ : Fin n → U.Code) (γ : Ctx.El U Γ ρ) (P : U.El (A ρ) → Prop) : Prop :=
  ∃ t : Tm U Γ A, P (t ρ γ)

theorem conditional_choice {n : Nat} {Γ : Ctx U n} {A : Ty U n}
    (fallback : Tm U Γ A) (ρ : Fin n → U.Code) (γ : Ctx.El U Γ ρ)
    (P : U.El (A ρ) → Prop) (h : Representable U ρ γ P) :
    P (epsilonTerm U fallback (fun t => P (t ρ γ)) ρ γ) :=
  epsilonTerm_spec U fallback _ h

end ProjectBeth.SystemF.Church
