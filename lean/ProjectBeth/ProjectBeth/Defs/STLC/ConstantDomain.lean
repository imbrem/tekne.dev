import ProjectBeth.Defs.STLC.Core
import Mathlib.Data.Fin.Basic

universe u v

namespace ProjectBeth.STLC.ConstantDomain

structure Signature where
  Const : Type u

inductive Tm (S : Signature) : Nat → Type u
  | var : Fin n → Tm S n
  | const : S.Const → Tm S n
  | app : Tm S n → Tm S n → Tm S n
  | lam : Tm S (n + 1) → Tm S n

def Tm.rename (ρ : Fin n → Fin m) : Tm S n → Tm S m
  | .var i => .var (ρ i)
  | .const c => .const c
  | .app f x => .app (f.rename ρ) (x.rename ρ)
  | .lam t => .lam (t.rename (Fin.cases 0 (fun i => Fin.succ (ρ i))))

def Tm.lift (t : Tm S n) : Tm S (n + 1) := t.rename Fin.succ

def Tm.subst (σ : Fin n → Tm S m) : Tm S n → Tm S m
  | .var i => σ i
  | .const c => .const c
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .lam t => .lam (t.subst (Fin.cases (.var 0) (fun i => (σ i).lift)))

def Tm.instantiate (t : Tm S (n + 1)) (x : Tm S n) : Tm S n :=
  t.subst (Fin.cases x .var)

inductive Reduces : Tm S n → Tm S n → Prop
  | beta : Reduces (.app (.lam t) x) (t.instantiate x)
  | app_left : Reduces f f' → Reduces (.app f x) (.app f' x)
  | app_right : Reduces x x' → Reduces (.app f x) (.app f x')
  | lam : Reduces t t' → Reduces (.lam t) (.lam t')

structure Model (S : Signature) (D : Type v) where
  const : S.Const → D
  app : D → D → D
  lam : (D → D) → D
  beta : ∀ f x, app (lam f) x = f x

abbrev Env (D : Type v) (n : Nat) := Fin n → D

def Tm.eval (M : Model S D) : Tm S n → Env D n → D
  | .var i, ρ => ρ i
  | .const c, _ => M.const c
  | .app f x, ρ => M.app (f.eval M ρ) (x.eval M ρ)
  | .lam t, ρ => M.lam (fun x => t.eval M (Fin.cases x ρ))

theorem Tm.eval_rename (M : Model S D) (t : Tm S n)
    (σ : Fin n → Fin m) (ρ : Env D m) :
    (t.rename σ).eval M ρ = t.eval M (ρ ∘ σ) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | app f x ihf ihx => simp [Tm.rename, Tm.eval, ihf, ihx]
  | lam t ih =>
    simp only [Tm.rename, Tm.eval]
    congr 1
    funext x
    rw [ih]
    apply congrArg (t.eval M)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl

theorem Tm.eval_subst (M : Model S D) (t : Tm S n)
    (σ : Fin n → Tm S m) (ρ : Env D m) :
    (t.subst σ).eval M ρ = t.eval M (fun i => (σ i).eval M ρ) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | app f x ihf ihx => simp [Tm.subst, Tm.eval, ihf, ihx]
  | lam t ih =>
    simp only [Tm.subst, Tm.eval]
    congr 1
    funext x
    rw [ih]
    apply congrArg (t.eval M)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change ((σ j).rename Fin.succ).eval M _ = _
      rw [Tm.eval_rename]
      apply congrArg ((σ j).eval M)
      funext k
      rfl

theorem Reduces.sound (M : Model S D) {n : Nat} {t u : Tm S n}
    (h : Reduces t u) (ρ : Env D n) :
    t.eval M ρ = u.eval M ρ := by
  induction h with
  | beta =>
    simp only [Tm.eval, Model.beta, Tm.instantiate, Tm.eval_subst]
    apply congrArg (_root_.id)
    apply congrArg (Tm.eval M _)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  | app_left h ih => simp [Tm.eval, ih]
  | app_right h ih => simp [Tm.eval, ih]
  | lam h ih =>
    simp only [Tm.eval]
    congr 1
    funext x
    exact ih _

structure TypedSignature (Ty : Type u) (arr : Ty → Ty → Ty) extends Signature where
  constTy : Const → Ty

inductive TypedTm (S : TypedSignature Ty arr) : List Ty → Ty → Type u
  | var : STLC.Var Γ A → TypedTm S Γ A
  | const : (c : S.Const) → TypedTm S Γ (S.constTy c)
  | app : TypedTm S Γ (arr A B) → TypedTm S Γ A → TypedTm S Γ B
  | lam : TypedTm S (A :: Γ) B → TypedTm S Γ (arr A B)

def eraseVar : STLC.Var Γ A → Fin Γ.length
  | .here => ⟨0, by simp⟩
  | .there v => ⟨eraseVar v + 1, by simpa using (eraseVar v).isLt⟩

def TypedTm.erase : TypedTm S Γ A → Tm S.toSignature Γ.length
  | .var v => .var (eraseVar v)
  | .const c => .const c
  | .app f x => .app f.erase x.erase
  | .lam t => .lam (by simpa using t.erase)

def ListEnv (D : Type v) : List Ty → Type v
  | [] => PUnit
  | _ :: Γ => D × ListEnv D Γ

def ListEnv.get : STLC.Var Γ A → ListEnv D Γ → D
  | .here, ρ => ρ.1
  | .there v, ρ => get v ρ.2

def ListEnv.toFin : (Γ : List Ty) → ListEnv D Γ → Fin Γ.length → D
  | [], _, i => Fin.elim0 i
  | _ :: Γ, ρ, i => Fin.cases ρ.1 (fun j => ListEnv.toFin Γ ρ.2 j) i

theorem ListEnv.toFin_var (v : STLC.Var Γ A) (ρ : ListEnv D Γ) :
    ListEnv.toFin Γ ρ (eraseVar v) = ListEnv.get v ρ := by
  induction v with
  | here => rfl
  | there v ih => exact ih ρ.2

def TypedTm.eval (M : Model S.toSignature D) : TypedTm S Γ A → ListEnv D Γ → D
  | .var v, ρ => ListEnv.get v ρ
  | .const c, _ => M.const c
  | .app f x, ρ => M.app (f.eval M ρ) (x.eval M ρ)
  | .lam t, ρ => M.lam (fun x => t.eval M (x, ρ))

theorem TypedTm.erase_eval (M : Model S.toSignature D) (t : TypedTm S Γ A)
    (ρ : ListEnv D Γ) :
    t.erase.eval M (ListEnv.toFin Γ ρ) = t.eval M ρ := by
  induction t with
  | var v => exact ListEnv.toFin_var v ρ
  | const c => rfl
  | app f x ihf ihx =>
    change M.app (f.erase.eval M _) (x.erase.eval M _) =
      M.app (f.eval M ρ) (x.eval M ρ)
    rw [ihf, ihx]
  | lam t ih =>
    change M.lam (fun x => t.erase.eval M _) = M.lam (fun x => t.eval M (x, ρ))
    congr 1
    funext x
    exact ih (x, ρ)

end ProjectBeth.STLC.ConstantDomain
