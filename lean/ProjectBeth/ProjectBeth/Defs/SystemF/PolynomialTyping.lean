import ProjectBeth.Defs.SystemF.Polynomial
import ProjectBeth.Defs.SystemF.ContextMorphisms

universe u

namespace ProjectBeth.SystemF.Polynomial.Syntax.Typing

open ProjectBeth.SystemF.Inductive
open ProjectBeth.SystemF.Inductive.Semantics

variable {Const : Type u}

def liftTy (d : Derivation Δ Γ t A) :
    Derivation (Δ + 1) (Γ.map Inductive.Ty.lift) (t.renameTy Nat.succ) A.lift :=
  ((d.renameTy Nat.succ).changeDepth (Δ' := Δ + 1)).castCtx
    (by simp [Inductive.Ty.lift]) rfl (by rfl)

@[simp] theorem lift_instantiate (A X : Inductive.Ty) : A.lift.instantiate X = A := by
  rw [Inductive.Ty.lift, Inductive.Ty.instantiate, Inductive.Ty.subst_rename]
  calc
    A.subst ((fun | 0 => X | n + 1 => .var n) ∘ Nat.succ) =
        A.subst Inductive.Ty.var := by
          apply Inductive.Ty.subst_congr
          intro n
          rfl
    _ = A := Inductive.Ty.subst_var A

@[simp] theorem subst_lift_inst (A X : Inductive.Ty) :
    A.lift.subst (fun | 0 => X | n + 1 => .var n) = A :=
  lift_instantiate A X

theorem polyTy_rename (base : Const → Inductive.Ty) (P : STLC.Poly Const)
    (X : Inductive.Ty) (ρ : Nat → Nat) :
    (Syntax.polyTy base P X).rename ρ =
      Syntax.polyTy (fun c => (base c).rename ρ) P (X.rename ρ) := by
  induction P generalizing X ρ with
  | var => rfl
  | const => rfl
  | pow => rfl
  | sum P Q ihP ihQ =>
    simp only [Syntax.polyTy, Syntax.sumTy, Inductive.Ty.rename]
    rw [Inductive.Ty.rename_lift, ihP, Inductive.Ty.rename_lift, ihQ]
    simp [Inductive.upRen]
  | prod P Q ihP ihQ =>
    simp only [Syntax.polyTy, Syntax.prodTy, Inductive.Ty.rename]
    rw [Inductive.Ty.rename_lift, ihP, Inductive.Ty.rename_lift, ihQ]
    simp [Inductive.upRen]

theorem polyTy_subst (base : Const → Inductive.Ty) (P : STLC.Poly Const)
    (X : Inductive.Ty) (σ : Nat → Inductive.Ty) :
    (Syntax.polyTy base P X).subst σ =
      Syntax.polyTy (fun c => (base c).subst σ) P (X.subst σ) := by
  induction P generalizing X σ with
  | var => rfl
  | const => rfl
  | pow => rfl
  | sum P Q ihP ihQ =>
    simp only [Syntax.polyTy, Syntax.sumTy, Inductive.Ty.subst]
    rw [Inductive.Ty.subst_lift, ihP, Inductive.Ty.subst_lift, ihQ]
    rfl
  | prod P Q ihP ihQ =>
    simp only [Syntax.polyTy, Syntax.prodTy, Inductive.Ty.subst]
    rw [Inductive.Ty.subst_lift, ihP, Inductive.Ty.subst_lift, ihQ]
    rfl

@[simp] theorem polyTy_lift_instantiate (base : Const → Inductive.Ty)
    (P : STLC.Poly Const) (X : Inductive.Ty) :
    (Syntax.polyTy (fun c => (base c).lift) P (.var 0)).instantiate X =
      Syntax.polyTy base P X := by
  rw [Inductive.Ty.instantiate, polyTy_subst]
  congr 1
  funext c
  exact subst_lift_inst (base c) X
def sumInl (d : Derivation Δ Γ a A) :
    Derivation Δ Γ (Syntax.sumInl A B a) (Syntax.sumTy A B) := by
  apply Derivation.tyLam
  apply Derivation.lam
  apply Derivation.lam
  apply Derivation.app
  · exact Derivation.var (n := 1) (A := .arr A.lift (.var 0)) (by simp)
  · exact (((liftTy d).renameTm
      (CtxRen.weaken _ (.arr A.lift (.var 0)))).renameTm
        (CtxRen.weaken _ (.arr B.lift (.var 0))))

def sumInr (d : Derivation Δ Γ b B) :
    Derivation Δ Γ (Syntax.sumInr A B b) (Syntax.sumTy A B) := by
  apply Derivation.tyLam
  apply Derivation.lam
  apply Derivation.lam
  apply Derivation.app
  · exact Derivation.var (n := 0) (A := .arr B.lift (.var 0)) (by simp)
  · exact (((liftTy d).renameTm
      (CtxRen.weaken _ (.arr A.lift (.var 0)))).renameTm
        (CtxRen.weaken _ (.arr B.lift (.var 0))))

def prodPair (da : Derivation Δ Γ a A) (db : Derivation Δ Γ b B) :
    Derivation Δ Γ (Syntax.prodPair A B a b) (Syntax.prodTy A B) := by
  apply Derivation.tyLam
  apply Derivation.lam
  apply Derivation.app
  · apply Derivation.app
    · exact Derivation.var (n := 0)
        (A := .arr A.lift (.arr B.lift (.var 0))) (by simp)
    · exact (liftTy da).renameTm (CtxRen.weaken _ _)
  · exact (liftTy db).renameTm (CtxRen.weaken _ _)

def sumElim (ds : Derivation Δ Γ s (Syntax.sumTy A B))
    (dl : Derivation Δ Γ l (.arr A R)) (dr : Derivation Δ Γ r (.arr B R)) :
    Derivation Δ Γ (Syntax.sumElim s R l r) R := by
  have hsum :
      ((.arr (.arr A.lift (.var 0)) (.arr (.arr B.lift (.var 0)) (.var 0)) : Inductive.Ty).instantiate R) =
        Inductive.Ty.arr (Inductive.Ty.arr A R)
          (Inductive.Ty.arr (Inductive.Ty.arr B R) R) := by
    simp only [Inductive.Ty.instantiate, Inductive.Ty.subst]
    congr 1 <;> congr 1
    · exact subst_lift_inst A R
    · exact congrArg (fun Z => Inductive.Ty.arr Z R) (subst_lift_inst B R)
  have ds' : Derivation Δ Γ (.tyApp s R)
      (Inductive.Ty.arr (Inductive.Ty.arr A R)
        (Inductive.Ty.arr (Inductive.Ty.arr B R) R)) :=
    (Derivation.tyApp (X := R) ds).castCtx rfl rfl hsum
  apply Derivation.app
  · apply Derivation.app
    · exact ds'
    · exact dl
  · exact dr

def prodElim (dp : Derivation Δ Γ p (Syntax.prodTy A B))
    (dk : Derivation Δ Γ k (.arr A (.arr B R))) :
    Derivation Δ Γ (Syntax.prodElim p R k) R := by
  have hprod :
      ((.arr (.arr A.lift (.arr B.lift (.var 0))) (.var 0) : Inductive.Ty).instantiate R) =
        Inductive.Ty.arr (Inductive.Ty.arr A (Inductive.Ty.arr B R)) R := by
    simp only [Inductive.Ty.instantiate, Inductive.Ty.subst]
    congr 1
    congr 1
    · exact subst_lift_inst A R
    · exact congrArg (fun Z => Inductive.Ty.arr Z R) (subst_lift_inst B R)
  have dp' : Derivation Δ Γ (.tyApp p R)
      (Inductive.Ty.arr (Inductive.Ty.arr A (Inductive.Ty.arr B R)) R) :=
    (Derivation.tyApp (X := R) dp).castCtx rfl rfl hprod
  apply Derivation.app
  · exact dp'
  · exact dk

noncomputable def fmapTm (base : Const → Inductive.Ty) (P : STLC.Poly Const)
    (df : Derivation Δ Γ f (.arr X Y))
    (dx : Derivation Δ Γ x (Syntax.polyTy base P X)) :
    Derivation Δ Γ (Syntax.fmapTm base P X Y f x) (Syntax.polyTy base P Y) := by
  induction P generalizing Γ f x with
  | var => exact .app df dx
  | const => exact dx
  | pow c =>
    apply Derivation.lam
    apply Derivation.app
    · exact df.renameTm (CtxRen.weaken _ (base c))
    · apply Derivation.app
      · exact dx.renameTm (CtxRen.weaken _ (base c))
      · exact .var (by simp)
  | sum P Q ihP ihQ =>
    apply sumElim dx
    · apply Derivation.lam
      apply sumInl
      apply ihP
      · exact df.renameTm (CtxRen.weaken _ (Syntax.polyTy base P X))
      · exact .var (by simp)
    · apply Derivation.lam
      apply sumInr
      apply ihQ
      · exact df.renameTm (CtxRen.weaken _ (Syntax.polyTy base Q X))
      · exact .var (by simp)
  | prod P Q ihP ihQ =>
    apply prodElim dx
    apply Derivation.lam
    apply Derivation.lam
    apply prodPair
    · apply ihP
      · exact (df.renameTm (CtxRen.weaken _ (Syntax.polyTy base P X))).renameTm
          (CtxRen.weaken _ (Syntax.polyTy base Q X))
      · exact .var (by simp)
    · apply ihQ
      · exact (df.renameTm (CtxRen.weaken _ (Syntax.polyTy base P X))).renameTm
          (CtxRen.weaken _ (Syntax.polyTy base Q X))
      · exact .var (by simp)

end ProjectBeth.SystemF.Polynomial.Syntax.Typing
