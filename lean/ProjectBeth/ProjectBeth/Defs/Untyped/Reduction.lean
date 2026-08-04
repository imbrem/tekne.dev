import Mathlib.Logic.Relation

universe u v

namespace ProjectBeth.Untyped

/-- Untyped de Bruijn lambda terms with constants from `C`. -/
inductive Tm (C : Type u) : Type u
  | var : Nat → Tm C
  | const : C → Tm C
  | app : Tm C → Tm C → Tm C
  | lam : Tm C → Tm C
deriving DecidableEq

def Tm.rename (ρ : Nat → Nat) : Tm C → Tm C
  | .var i => .var (ρ i)
  | .const c => .const c
  | .app f x => .app (rename ρ f) (rename ρ x)
  | .lam t => .lam (rename (fun | 0 => 0 | i + 1 => ρ i + 1) t)

def Tm.subst (σ : Nat → Tm C) : Tm C → Tm C
  | .var i => σ i
  | .const c => .const c
  | .app f x => .app (subst σ f) (subst σ x)
  | .lam t => .lam (subst (fun | 0 => .var 0 | i + 1 => rename Nat.succ (σ i)) t)

def Tm.subst0 (body x : Tm C) : Tm C :=
  body.subst (fun | 0 => x | i + 1 => .var i)

structure Signature where
  Const : Type u
  apply : Const → Const → Option Const

structure Signature.Hom (S : Signature.{u}) (T : Signature.{v}) where
  onConst : S.Const → T.Const
  apply_natural : ∀ f x,
    T.apply (onConst f) (onConst x) = Option.map onConst (S.apply f x)

def Tm.mapConst {S : Signature.{u}} {T : Signature.{v}} (F : S.Hom T) :
    Tm S.Const → Tm T.Const
  | .var i => .var i
  | .const c => .const (F.onConst c)
  | .app f x => .app (mapConst F f) (mapConst F x)
  | .lam t => .lam (mapConst F t)

@[simp] theorem Tm.mapConst_rename {S : Signature.{u}} {T : Signature.{v}}
    (F : S.Hom T) (ρ) (t : Tm S.Const) :
    (t.rename ρ).mapConst F = (t.mapConst F).rename ρ := by
  induction t generalizing ρ <;> simp [Tm.rename, Tm.mapConst, *]

@[simp] theorem Tm.mapConst_subst {S : Signature.{u}} {T : Signature.{v}}
    (F : S.Hom T) (σ) (t : Tm S.Const) :
    (t.subst σ).mapConst F = (t.mapConst F).subst (fun i => (σ i).mapConst F) := by
  induction t generalizing σ with
  | var i => rfl
  | const c => rfl
  | app f x ihf ihx => simp [Tm.subst, Tm.mapConst, ihf, ihx]
  | lam t ih =>
    simp only [Tm.subst, Tm.mapConst, ih]
    congr 2
    funext i
    cases i <;> simp [Tm.mapConst, Tm.mapConst_rename]

@[simp] theorem Tm.mapConst_subst0 {S : Signature.{u}} {T : Signature.{v}}
    (F : S.Hom T) (body x : Tm S.Const) :
    (body.subst0 x).mapConst F = (body.mapConst F).subst0 (x.mapConst F) := by
  rw [Tm.subst0, Tm.mapConst_subst]
  unfold Tm.subst0
  congr 2
  funext i
  cases i <;> rfl

inductive Step (S : Signature) : Tm S.Const → Tm S.Const → Prop
  | beta (body x) : Step S (.app (.lam body) x) (body.subst0 x)
  | delta {f x r} : S.apply f x = some r →
      Step S (.app (.const f) (.const x)) (.const r)
  | appLeft {f f'} (x) : Step S f f' → Step S (.app f x) (.app f' x)
  | appRight (f) {x x'} : Step S x x' → Step S (.app f x) (.app f x')
  | lam {t t'} : Step S t t' → Step S (.lam t) (.lam t')

abbrev Steps (S : Signature) := Relation.ReflTransGen (Step S)

theorem Step.map {S : Signature.{u}} {T : Signature.{v}}
    (F : S.Hom T) {a b} (h : Step S a b) :
    Step T (a.mapConst F) (b.mapConst F) := by
  induction h with
  | beta body x => simpa [Tm.mapConst] using
      (Step.beta (S := T) (body.mapConst F) (x.mapConst F))
  | delta h =>
    apply Step.delta
    rw [F.apply_natural, h]
    rfl
  | appLeft x _ ih => exact Step.appLeft (x.mapConst F) ih
  | appRight f _ ih => exact Step.appRight (f.mapConst F) ih
  | lam _ ih => exact Step.lam ih

theorem Steps.map {S : Signature.{u}} {T : Signature.{v}}
    (F : S.Hom T) {a b} (h : Steps S a b) :
    Steps T (a.mapConst F) (b.mapConst F) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (hstep.map F)

/-- A deterministic, fuelled head evaluator. `none` means that fuel was
exhausted; one beta or constant step is performed when available. -/
def eval (S : Signature) : Nat → Tm S.Const → Option (Tm S.Const)
  | 0, _ => none
  | _ + 1, .app (.lam body) x => some (body.subst0 x)
  | _ + 1, .app (.const c) (.const d) =>
      match S.apply c d with
      | some r => some (.const r)
      | none => some (.app (.const c) (.const d))
  | _ + 1, t => some t

theorem eval_natural {S : Signature.{u}} {T : Signature.{v}}
    (F : S.Hom T) (fuel) (t : Tm S.Const) :
    eval T fuel (t.mapConst F) = Option.map (Tm.mapConst F) (eval S fuel t) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases t with
    | var i => rfl
    | const c => rfl
    | lam b => rfl
    | app f x =>
      cases f with
      | var i => rfl
      | app a b => rfl
      | lam body => simp [eval, Tm.mapConst]
      | const c =>
        cases x with
        | var i => rfl
        | app a b => rfl
        | lam b => rfl
        | const d =>
          change (match T.apply (F.onConst c) (F.onConst d) with
            | some r => some (Tm.const r)
            | none => some (Tm.app (Tm.const (F.onConst c)) (Tm.const (F.onConst d)))) = _
          rw [F.apply_natural]
          cases h : S.apply c d <;> rw [eval, h] <;> rfl

end ProjectBeth.Untyped
