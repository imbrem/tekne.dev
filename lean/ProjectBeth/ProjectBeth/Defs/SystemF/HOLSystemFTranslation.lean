import ProjectBeth.Defs.SystemF.InductivePER
import ProjectBeth.Defs.SystemF.Untyped
import ProjectBeth.Defs.HOL.Syntax
import ProjectBeth.Defs.HOLOmega.Syntax

namespace ProjectBeth.SystemF.HOLTranslation

namespace Raw

abbrev Ty := ProjectBeth.SystemF.Inductive.Ty
abbrev Tm := ProjectBeth.SystemF.Inductive.Tm
abbrev HasType := ProjectBeth.SystemF.Inductive.HasType
open ProjectBeth.SystemF.Inductive

def boolTy : Ty := .all (.arr (.var 0) (.arr (.var 0) (.var 0)))

def natTy : Ty := .all (.arr (.arr (.var 0) (.var 0)) (.arr (.var 0) (.var 0)))

def churchTrue : Tm := .tyLam (.lam (.var 0) (.lam (.var 0) (.var 1)))

def churchFalse : Tm := .tyLam (.lam (.var 0) (.lam (.var 0) (.var 0)))

def churchIter : Nat → Tm
  | 0 => .var 0
  | n + 1 => .app (.var 1) (churchIter n)

def churchNat (n : Nat) : Tm :=
  .tyLam (.lam (.arr (.var 0) (.var 0)) (.lam (.var 0) (churchIter n)))

theorem churchTrue_typed : HasType Δ Γ churchTrue boolTy := by
  apply HasType.tyLam
  apply HasType.lam
  apply HasType.lam
  exact HasType.var (by rfl)

theorem churchFalse_typed : HasType Δ Γ churchFalse boolTy := by
  apply HasType.tyLam
  apply HasType.lam
  apply HasType.lam
  exact HasType.var (by rfl)

theorem churchIter_typed (n : Nat) :
    HasType Δ ([.var 0, .arr (.var 0) (.var 0)] ++ Γ) (churchIter n) (.var 0) := by
  induction n with
  | zero => exact HasType.var (by rfl)
  | succ n ih =>
    exact HasType.app (HasType.var (n := 1) (by rfl)) ih

theorem churchNat_typed (n : Nat) : HasType Δ Γ (churchNat n) natTy := by
  apply HasType.tyLam
  apply HasType.lam
  apply HasType.lam
  exact churchIter_typed n

@[simp] theorem churchIter_rename (n : Nat) (ρ : Nat → Nat) :
    (churchIter n).rename (upRen (upRen ρ)) = churchIter n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [churchIter, ProjectBeth.SystemF.Inductive.Tm.rename, upRen, ih]

@[simp] theorem churchBool_rename (b : Bool) (ρ : Nat → Nat) :
    (if b then churchTrue else churchFalse).rename ρ =
      (if b then churchTrue else churchFalse) := by
  cases b <;> rfl

@[simp] theorem churchNat_rename (n : Nat) (ρ : Nat → Nat) :
    (churchNat n).rename ρ = churchNat n := by
  simp only [churchNat, ProjectBeth.SystemF.Inductive.Tm.rename]
  congr 3
  change (churchIter n).rename (upRen (upRen ρ)) = churchIter n
  exact churchIter_rename n ρ

@[simp] theorem churchBool_subst (b : Bool) (σ : Nat → Tm) :
    (if b then churchTrue else churchFalse).subst σ =
      (if b then churchTrue else churchFalse) := by
  cases b <;> rfl

theorem churchIter_subst_of (n : Nat) (σ : Nat → Tm)
    (h0 : σ 0 = .var 0) (h1 : σ 1 = .var 1) :
    (churchIter n).subst σ = churchIter n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    simp only [churchIter, ProjectBeth.SystemF.Inductive.Tm.subst]
    rw [h1, ih]

@[simp] theorem churchNat_subst (n : Nat) (σ : Nat → Tm) :
    (churchNat n).subst σ = churchNat n := by
  simp only [churchNat, ProjectBeth.SystemF.Inductive.Tm.subst]
  congr 3
  apply churchIter_subst_of
  · rfl
  · rfl

end Raw

/-- The simply-typed HOL fragment representable without adding constants to
raw System F.  Subtypes deliberately remain outside this translation. -/
def holTy (base : B → Inductive.Ty) : ProjectBeth.HOL.Ty B → Option Inductive.Ty
  | .base A => some (base A)
  | .bool => some Raw.boolTy
  | .arr A B => return .arr (← holTy base A) (← holTy base B)
  | .sub _ _ => none

def holOmegaTy (base : B → Inductive.Ty) :
    ProjectBeth.HOLOmega.Ty B → Option Inductive.Ty
  | .base A => some (base A)
  | .var n => some (.var n)
  | .bool => some Raw.boolTy
  | .arr A B => return .arr (← holOmegaTy base A) (← holOmegaTy base B)
  | .lam _ A => return .all (← holOmegaTy base A)
  | .app _ _ => none
  | .sub _ _ => none

/-- An explicit boundary for constants absent from pure System F.  A client
may supply equality and classical choice only for translated types. -/
structure ClassicalInterface where
  eq : Inductive.Ty → Inductive.Tm
  epsilon : Inductive.Ty → Inductive.Tm
  eq_typed : ∀ Δ Γ A, Inductive.HasType Δ Γ (eq A)
    (.arr A (.arr A Raw.boolTy))
  epsilon_typed : ∀ Δ Γ A, Inductive.HasType Δ Γ (epsilon A)
    (.arr (.arr A Raw.boolTy) A)

def holCtx (base : B → Inductive.Ty) (Γ : ProjectBeth.HOL.Ctx B) :
    Option (List Inductive.Ty) := Γ.mapM (holTy base)

def holOmegaCtx (base : B → Inductive.Ty) (Γ : List (ProjectBeth.HOLOmega.Ty B)) :
    Option (List Inductive.Ty) := Γ.mapM (holOmegaTy base)

def holTm (I : ClassicalInterface) (base : B → Inductive.Ty) :
    ProjectBeth.HOL.Tm B → Option Inductive.Tm
  | .var n => some (.var n)
  | .app f x => return .app (← holTm I base f) (← holTm I base x)
  | .lam A t => return .lam (← holTy base A) (← holTm I base t)
  | .bool b => some (if b then Raw.churchTrue else Raw.churchFalse)
  | .eq A x y => return .app (.app (I.eq (← holTy base A))
      (← holTm I base x)) (← holTm I base y)
  | .epsilon A p => return .app (I.epsilon (← holTy base A)) (← holTm I base p)
  | .abs _ _ _ => none
  | .rep _ _ _ => none

def holOmegaTm (I : ClassicalInterface) (base : B → Inductive.Ty) :
    ProjectBeth.HOLOmega.Tm B → Option Inductive.Tm
  | .var n => some (.var n)
  | .app f x => return .app (← holOmegaTm I base f) (← holOmegaTm I base x)
  | .lam A t => return .lam (← holOmegaTy base A) (← holOmegaTm I base t)
  | .tyApp f A => return .tyApp (← holOmegaTm I base f) (← holOmegaTy base A)
  | .tyLam .star t => return .tyLam (← holOmegaTm I base t)
  | .tyLam (.arr _ _) _ => none
  | .bool b => some (if b then Raw.churchTrue else Raw.churchFalse)
  | .eq A x y => return .app (.app (I.eq (← holOmegaTy base A))
      (← holOmegaTm I base x)) (← holOmegaTm I base y)
  | .epsilon A p => do
      let A' ← holOmegaTy base A
      let p' ← holOmegaTm I base p
      pure (.app (I.epsilon A') p')
  | .abs _ _ _ => none
  | .rep _ _ _ => none

@[simp] theorem holTm_bool (I : ClassicalInterface) (base : B → Inductive.Ty)
    (b : Bool) : holTm I base (.bool b) =
      some (if b then Raw.churchTrue else Raw.churchFalse) := rfl

@[simp] theorem holOmegaTm_bool (I : ClassicalInterface)
    (base : B → Inductive.Ty) (b : Bool) : holOmegaTm I base (.bool b) =
      some (if b then Raw.churchTrue else Raw.churchFalse) := rfl

/-- Erasure is deliberately factored through the typed translation.  Thus
the square cannot silently erase a source construct rejected by `holTm`. -/
def holErase (S : ProjectBeth.Untyped.Signature) (I : ClassicalInterface)
    (base : B → Inductive.Ty) (t : ProjectBeth.HOL.Tm B) :=
  (holTm I base t).map (Inductive.Untyped.erase S)

def holOmegaErase (S : ProjectBeth.Untyped.Signature) (I : ClassicalInterface)
    (base : B → Inductive.Ty) (t : ProjectBeth.HOLOmega.Tm B) :=
  (holOmegaTm I base t).map (Inductive.Untyped.erase S)

theorem hol_erase_square (base : B → Inductive.Ty)
    (h : holTm I base t = some u) :
    holErase S I base t = some (Inductive.Untyped.erase S u) := by
  simp [holErase, h]

theorem holOmega_erase_square (base : B → Inductive.Ty)
    (h : holOmegaTm I base t = some u) :
    holOmegaErase S I base t = some (Inductive.Untyped.erase S u) := by
  simp [holOmegaErase, h]

/-- Semantic obligation for a realization of classical choice. `Sat A p x`
means that `x : A` satisfies the translated predicate `p : A → Bool`.
The law is conditional and therefore makes no representability or
definability claim about arbitrary semantic elements. -/
structure SelectionLaw (I : ClassicalInterface)
    (Sat : Inductive.Ty → Inductive.Tm → Inductive.Tm → Prop) : Prop where
  selected : ∀ {A p}, (∃ x, Sat A p x) → Sat A p (.app (I.epsilon A) p)

theorem epsilon_selection {Sat : Inductive.Ty → Inductive.Tm → Inductive.Tm → Prop}
    (law : SelectionLaw I Sat) (h : ∃ x, Sat A p x) :
    Sat A p (.app (I.epsilon A) p) := law.selected h

/-- A derivation-directed certificate for the HOL fragment accepted by the
compiler. Its indices retain the original HOL typing derivation. -/
inductive HOLCompile (I : ClassicalInterface) (base : B → Inductive.Ty) :
    ProjectBeth.HOL.Ctx B → ProjectBeth.HOL.Tm B → ProjectBeth.HOL.Ty B →
    (Γ' : List Inductive.Ty) → Inductive.Tm → Inductive.Ty → Prop
  | var (h : Γ[n]? = some A) (hΓ : Γ'[n]? = some A')
      (hA : holTy base A = some A') :
      HOLCompile I base Γ (.var n) A Γ' (.var n) A'
  | app (hf : HOLCompile I base Γ f (.arr A C) Γ' f' (.arr A' B'))
      (hx : HOLCompile I base Γ x A Γ' x' A') :
      HOLCompile I base Γ (.app f x) C Γ' (.app f' x') B'
  | lam (wf : ProjectBeth.HOL.Ty.Wf A)
      (hA : holTy base A = some A')
      (ht : HOLCompile I base (A :: Γ) t C (A' :: Γ') t' B') :
      HOLCompile I base Γ (.lam A t) (.arr A C) Γ' (.lam A' t') (.arr A' B')
  | bool (b : Bool) : HOLCompile I base Γ (.bool b) .bool Γ'
      (if b then Raw.churchTrue else Raw.churchFalse) Raw.boolTy
  | eq (wf : ProjectBeth.HOL.Ty.Wf A)
      (hA : holTy base A = some A')
      (hx : HOLCompile I base Γ x A Γ' x' A')
      (hy : HOLCompile I base Γ y A Γ' y' A') :
      HOLCompile I base Γ (.eq A x y) .bool Γ'
        (.app (.app (I.eq A') x') y') Raw.boolTy
  | epsilon (wf : ProjectBeth.HOL.Ty.Wf A)
      (hA : holTy base A = some A')
      (hp : HOLCompile I base Γ p (.arr A .bool) Γ' p' (.arr A' Raw.boolTy)) :
      HOLCompile I base Γ (.epsilon A p) A Γ'
        (.app (I.epsilon A') p') A'

def HOLCompile.typed (base : B → Inductive.Ty) :
    (d : HOLCompile I base Γ t A Γ' t' A') → Inductive.HasType 0 Γ' t' A'
  | .var _ hΓ _ => .var hΓ
  | .app hf hx => .app (typed base hf) (typed base hx)
  | .lam _ _ ht => .lam (typed base ht)
  | .bool true => Raw.churchTrue_typed
  | .bool false => Raw.churchFalse_typed
  | .eq _ _ hx hy =>
      .app (.app (I.eq_typed 0 Γ' _) (typed base hx)) (typed base hy)
  | .epsilon _ _ hp => .app (I.epsilon_typed 0 Γ' _) (typed base hp)

def HOLCompile.sourceTyped (base : B → Inductive.Ty) :
    HOLCompile I base Γ t A Γ' t' A' → ProjectBeth.HOL.HasType Γ t A
  | .var h _ _ => .var h
  | .app hf hx => .app (sourceTyped base hf) (sourceTyped base hx)
  | .lam wf _ ht => .lam wf (sourceTyped base ht)
  | .bool _ => .bool
  | .eq wf _ hx hy => .eq wf (sourceTyped base hx) (sourceTyped base hy)
  | .epsilon wf _ hp => .epsilon wf (sourceTyped base hp)

/-- The monomorphic portion of HOLω has the same derivation-directed
translation. Type abstraction/application are intentionally absent here;
their kind-indexed context translation is a separate compiler. -/
inductive HOLOmegaCompile (I : ClassicalInterface) (base : B → Inductive.Ty) :
    List ProjectBeth.HOLOmega.Kind → List (ProjectBeth.HOLOmega.Ty B) →
    ProjectBeth.HOLOmega.Tm B → ProjectBeth.HOLOmega.Ty B →
    (Γ' : List Inductive.Ty) → Inductive.Tm → Inductive.Ty → Prop
  | var (h : Γ[n]? = some A) (hΓ : Γ'[n]? = some A')
      (hA : holOmegaTy base A = some A') :
      HOLOmegaCompile I base Δ Γ (.var n) A Γ' (.var n) A'
  | app (hf : HOLOmegaCompile I base Δ Γ f (.arr A C) Γ' f' (.arr A' B'))
      (hx : HOLOmegaCompile I base Δ Γ x A Γ' x' A') :
      HOLOmegaCompile I base Δ Γ (.app f x) C Γ' (.app f' x') B'
  | lam (kA : ProjectBeth.HOLOmega.Kinded Δ A .star)
      (hA : holOmegaTy base A = some A')
      (ht : HOLOmegaCompile I base Δ (A :: Γ) t C (A' :: Γ') t' B') :
      HOLOmegaCompile I base Δ Γ (.lam A t) (.arr A C) Γ' (.lam A' t') (.arr A' B')
  | bool (b : Bool) : HOLOmegaCompile I base Δ Γ (.bool b) .bool Γ'
      (if b then Raw.churchTrue else Raw.churchFalse) Raw.boolTy
  | eq (kA : ProjectBeth.HOLOmega.Kinded Δ A .star)
      (hA : holOmegaTy base A = some A')
      (hx : HOLOmegaCompile I base Δ Γ x A Γ' x' A')
      (hy : HOLOmegaCompile I base Δ Γ y A Γ' y' A') :
      HOLOmegaCompile I base Δ Γ (.eq A x y) .bool Γ'
        (.app (.app (I.eq A') x') y') Raw.boolTy
  | epsilon (kA : ProjectBeth.HOLOmega.Kinded Δ A .star)
      (hA : holOmegaTy base A = some A')
      (hp : HOLOmegaCompile I base Δ Γ p (.arr A .bool) Γ' p' (.arr A' Raw.boolTy)) :
      HOLOmegaCompile I base Δ Γ (.epsilon A p) A Γ'
        (.app (I.epsilon A') p') A'

def HOLOmegaCompile.typed (base : B → Inductive.Ty) :
    (d : HOLOmegaCompile I base Δ Γ t A Γ' t' A') → Inductive.HasType 0 Γ' t' A'
  | .var _ hΓ _ => .var hΓ
  | .app hf hx => .app (typed base hf) (typed base hx)
  | .lam _ _ ht => .lam (typed base ht)
  | .bool true => Raw.churchTrue_typed
  | .bool false => Raw.churchFalse_typed
  | .eq _ _ hx hy =>
      .app (.app (I.eq_typed 0 Γ' _) (typed base hx)) (typed base hy)
  | .epsilon _ _ hp => .app (I.epsilon_typed 0 Γ' _) (typed base hp)

def HOLOmegaCompile.sourceTyped (base : B → Inductive.Ty) :
    HOLOmegaCompile I base Δ Γ t A Γ' t' A' →
      ProjectBeth.HOLOmega.HasType Δ Γ t A
  | .var h _ _ => .var h
  | .app hf hx => .app (sourceTyped base hf) (sourceTyped base hx)
  | .lam kA _ ht => .lam kA (sourceTyped base ht)
  | .bool _ => .bool
  | .eq kA _ hx hy => .eq kA (sourceTyped base hx) (sourceTyped base hy)
  | .epsilon kA _ hp => .epsilon kA (sourceTyped base hp)

universe v w

structure SemanticCompatibility (I : ClassicalInterface) (B : Type u)
    (E : Type v) (V : Type w) where
  holEval : ProjectBeth.HOL.Tm B → E → V
  omegaEval : ProjectBeth.HOLOmega.Tm B → E → V
  systemFEval : Inductive.Tm → E → V
  hol_var : ∀ n e, holEval (.var n) e = systemFEval (.var n) e
  hol_app : ∀ f x f' x' e, holEval f e = systemFEval f' e →
    holEval x e = systemFEval x' e →
    holEval (.app f x) e = systemFEval (.app f' x') e
  hol_lam : ∀ A t A' t' e, holEval t e = systemFEval t' e →
    holEval (.lam A t) e = systemFEval (.lam A' t') e
  hol_bool : ∀ b e, holEval (.bool b) e =
    systemFEval (if b then Raw.churchTrue else Raw.churchFalse) e
  hol_eq : ∀ A x y A' x' y' e, holEval x e = systemFEval x' e →
    holEval y e = systemFEval y' e →
    holEval (.eq A x y) e = systemFEval (.app (.app (I.eq A') x') y') e
  hol_epsilon : ∀ A p A' p' e, holEval p e = systemFEval p' e →
    holEval (.epsilon A p) e = systemFEval (.app (I.epsilon A') p') e
  omega_var : ∀ n e, omegaEval (.var n) e = systemFEval (.var n) e
  omega_app : ∀ f x f' x' e, omegaEval f e = systemFEval f' e →
    omegaEval x e = systemFEval x' e →
    omegaEval (.app f x) e = systemFEval (.app f' x') e
  omega_lam : ∀ A t A' t' e, omegaEval t e = systemFEval t' e →
    omegaEval (.lam A t) e = systemFEval (.lam A' t') e
  omega_bool : ∀ b e, omegaEval (.bool b) e =
    systemFEval (if b then Raw.churchTrue else Raw.churchFalse) e
  omega_eq : ∀ A x y A' x' y' e, omegaEval x e = systemFEval x' e →
    omegaEval y e = systemFEval y' e →
    omegaEval (.eq A x y) e = systemFEval (.app (.app (I.eq A') x') y') e
  omega_epsilon : ∀ A p A' p' e, omegaEval p e = systemFEval p' e →
    omegaEval (.epsilon A p) e = systemFEval (.app (I.epsilon A') p') e

def HOLCompile.semantic_square (base : B → Inductive.Ty)
    (C : SemanticCompatibility I B E V) :
    (d : HOLCompile I base Γ t A Γ' t' A') → ∀ e,
      C.holEval t e = C.systemFEval t' e
  | .var _ _ _, e => C.hol_var _ e
  | .app df dx, e => C.hol_app _ _ _ _ e
      (semantic_square base C df e) (semantic_square base C dx e)
  | .lam _ _ dt, e => C.hol_lam _ _ _ _ e (semantic_square base C dt e)
  | .bool b, e => C.hol_bool b e
  | .eq _ _ dx dy, e => C.hol_eq _ _ _ _ _ _ e
      (semantic_square base C dx e) (semantic_square base C dy e)
  | .epsilon _ _ dp, e => C.hol_epsilon _ _ _ _ e (semantic_square base C dp e)

def HOLOmegaCompile.semantic_square (base : B → Inductive.Ty)
    (C : SemanticCompatibility I B E V) :
    (d : HOLOmegaCompile I base Δ Γ t A Γ' t' A') → ∀ e,
      C.omegaEval t e = C.systemFEval t' e
  | .var _ _ _, e => C.omega_var _ e
  | .app df dx, e => C.omega_app _ _ _ _ e
      (semantic_square base C df e) (semantic_square base C dx e)
  | .lam _ _ dt, e => C.omega_lam _ _ _ _ e (semantic_square base C dt e)
  | .bool b, e => C.omega_bool b e
  | .eq _ _ dx dy, e => C.omega_eq _ _ _ _ _ _ e
      (semantic_square base C dx e) (semantic_square base C dy e)
  | .epsilon _ _ dp, e => C.omega_epsilon _ _ _ _ e
      (semantic_square base C dp e)


end ProjectBeth.SystemF.HOLTranslation
