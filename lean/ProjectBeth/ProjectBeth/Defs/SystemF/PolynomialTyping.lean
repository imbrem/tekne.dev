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
  congr 3
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

@[simp] theorem churchMu_instantiate (base : Const → Inductive.Ty)
    (P : STLC.Poly Const) (X : Inductive.Ty) :
    ((.arr (.arr (Syntax.polyTy (fun c => (base c).lift) P (.var 0)) (.var 0))
      (.var 0) : Inductive.Ty).instantiate X) =
      .arr (.arr (Syntax.polyTy base P X) X) X := by
  simp only [Inductive.Ty.instantiate, Inductive.Ty.subst]
  change (Inductive.Ty.arr (Inductive.Ty.arr
    ((Syntax.polyTy (fun c => (base c).lift) P (.var 0)).instantiate X) X) X) = _
  rw [polyTy_lift_instantiate]

def churchFold {base : Const → Inductive.Ty} {P : STLC.Poly Const}
    {m alg : Inductive.Tm} {X : Inductive.Ty}
    (dm : Derivation Δ Γ m (Syntax.churchMuTy base P))
    (da : Derivation Δ Γ alg (.arr (Syntax.polyTy base P X) X)) :
    Derivation Δ Γ (Syntax.churchFold m X alg) X := by
  have dm' : Derivation Δ Γ (.tyApp m X)
      (.arr (.arr (Syntax.polyTy base P X) X) X) :=
    (Derivation.tyApp (X := X) dm).castCtx rfl rfl
      (churchMu_instantiate base P X)
  exact .app dm' da

@[simp] theorem coChurch_instantiate (base : Const → Inductive.Ty)
    (P : STLC.Poly Const) (R : Inductive.Ty) :
    ((.arr
      (.all (.arr (.var 0)
        (.arr (.arr (.var 0)
          (Syntax.polyTy (fun c => ((base c).lift).lift) P (.var 0))) (.var 1))))
      (.var 0) : Inductive.Ty).instantiate R) =
      .arr
        (.all (.arr (.var 0)
          (.arr (.arr (.var 0)
            (Syntax.polyTy (fun c => (base c).lift) P (.var 0))) R.lift)))
        R := by
  simp [Inductive.Ty.instantiate, Inductive.Ty.subst, Inductive.upTySub,
    polyTy_subst, Inductive.Ty.lift]
  congr 2
  funext c
  rw [Inductive.Ty.subst_rename, Inductive.Ty.subst_rename]
  calc
    (base c).subst
        (((Inductive.upTySub fun x => match x with
          | 0 => R
          | n + 1 => .var n) ∘ Nat.succ) ∘ Nat.succ) =
      (base c).subst (Inductive.Ty.var ∘ Nat.succ) := by
        apply Inductive.Ty.subst_congr
        intro n
        rfl
    _ = (base c).rename Nat.succ := by
      rw [← Inductive.Ty.subst_rename Inductive.Ty.var]
      simp

def coElim {base : Const → Inductive.Ty} {P : STLC.Poly Const}
    {co handler : Inductive.Tm} {R : Inductive.Ty}
    (dc : Derivation Δ Γ co (Syntax.coChurchTy base P))
    (dh : Derivation Δ Γ handler
      (.all (.arr (.var 0)
        (.arr (.arr (.var 0)
          (Syntax.polyTy (fun c => (base c).lift) P (.var 0))) R.lift)))) :
    Derivation Δ Γ (Syntax.coElim co R handler) R := by
  have dc' : Derivation Δ Γ (.tyApp co R)
      (.arr
        (.all (.arr (.var 0)
          (.arr (.arr (.var 0)
            (Syntax.polyTy (fun c => (base c).lift) P (.var 0))) R.lift)))
        R) :=
    (Derivation.tyApp (X := R) dc).castCtx rfl rfl
      (coChurch_instantiate base P R)
  exact .app dc' dh

@[simp] theorem coHandler_instantiate (base : Const → Inductive.Ty)
    (P : STLC.Poly Const) (X : Inductive.Ty) :
    ((.arr (.var 0)
      (.arr (.arr (.var 0)
        (Syntax.polyTy (fun c => ((base c).lift).lift) P (.var 0))) (.var 1)) :
      Inductive.Ty).instantiate X.lift) =
      .arr X.lift
        (.arr (.arr X.lift
          (Syntax.polyTy (fun c => (base c).lift) P X.lift)) (.var 0)) := by
  simp only [Inductive.Ty.instantiate, Inductive.Ty.subst]
  exact congrArg (fun Z => Inductive.Ty.arr X.lift Z)
    (congrArg (fun Z => Inductive.Ty.arr Z (.var 0))
      (congrArg (fun Z => Inductive.Ty.arr X.lift Z)
        (polyTy_lift_instantiate (fun c => (base c).lift) P X.lift)))

def coPack {base : Const → Inductive.Ty} {P : STLC.Poly Const}
    {X : Inductive.Ty} {seed step : Inductive.Tm}
    (dseed : Derivation Δ Γ seed X)
    (dstep : Derivation Δ Γ step (.arr X (Syntax.polyTy base P X))) :
    Derivation Δ Γ (Syntax.coPack base P X seed step)
      (Syntax.coChurchTy base P) := by
  apply Derivation.tyLam
  let H : Inductive.Ty :=
    .all (.arr (.var 0)
      (.arr (.arr (.var 0)
        (Syntax.polyTy (fun c => ((base c).lift).lift) P (.var 0))) (.var 1)))
  apply Derivation.lam
  have dh : Derivation (Δ + 1) (H :: Γ.map Inductive.Ty.lift) (.var 0) H :=
    .var (by simp)
  have dh' : Derivation (Δ + 1) (H :: Γ.map Inductive.Ty.lift)
      (.tyApp (.var 0) X.lift)
      (.arr X.lift
        (.arr (.arr X.lift
          (Syntax.polyTy (fun c => (base c).lift) P X.lift)) (.var 0))) :=
    (Derivation.tyApp (X := X.lift) dh).castCtx rfl rfl
      (coHandler_instantiate base P X)
  apply Derivation.app
  · apply Derivation.app
    · exact dh'
    · exact (liftTy dseed).renameTm (CtxRen.weaken _ H)
  · have ds := (liftTy dstep).renameTm (CtxRen.weaken _ H)
    exact ds.castCtx rfl rfl (by
      simp only [Inductive.Ty.lift, Inductive.Ty.rename]
      congr 1
      exact polyTy_rename base P X Nat.succ)

def coiter {base : Const → Inductive.Ty} {P : STLC.Poly Const}
    {X : Inductive.Ty} {seed step : Inductive.Tm}
    (dseed : Derivation Δ Γ seed X)
    (dstep : Derivation Δ Γ step (.arr X (Syntax.polyTy base P X))) :
    Derivation Δ Γ (Syntax.coiter base P X step seed)
      (Syntax.coChurchTy base P) :=
  coPack dseed dstep

end ProjectBeth.SystemF.Polynomial.Syntax.Typing
