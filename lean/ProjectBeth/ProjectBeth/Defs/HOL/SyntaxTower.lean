import ProjectBeth.Defs.HOL.Kernel

namespace ProjectBeth.HOL.SyntaxTower

open ProjectBeth.HOL.Kernel

noncomputable section
attribute [local instance] Classical.propDecidable

universe u

namespace Minimal

inductive Tm : Kernel.Ctx.{u} → Kernel.Ty.{u} → Type (u + 1)
  | var : Var Γ A → Tm Γ A
  | app : Tm Γ (A.arr B) → Tm Γ A → Tm Γ B
  | lam : Tm (A :: Γ) B → Tm Γ (A.arr B)
  | bool : Bool → Tm Γ .bool
  | conj : Tm Γ .bool → Tm Γ .bool → Tm Γ .bool
  | eq : Tm Γ A → Tm Γ A → Tm Γ .bool

noncomputable def Tm.eval : Tm Γ A → Env Γ → A.El
  | .var v, ρ => ρ v
  | .app f x, ρ => f.eval ρ (x.eval ρ)
  | .lam t, ρ => fun x => t.eval (ρ.cons x)
  | .bool b, _ => ⟨b⟩
  | .conj p q, ρ => ⟨(p.eval ρ).down && (q.eval ρ).down⟩
  | .eq x y, ρ => if x.eval ρ = y.eval ρ then ⟨true⟩ else ⟨false⟩

noncomputable def Tm.rename (σ : Ren Γ Δ) : Tm Γ A → Tm Δ A
  | .var v => .var (σ v)
  | .app f x => .app (f.rename σ) (x.rename σ)
  | .lam t => .lam (t.rename σ.lift)
  | .bool b => .bool b
  | .conj p q => .conj (p.rename σ) (q.rename σ)
  | .eq x y => .eq (x.rename σ) (y.rename σ)

abbrev Sub (G D : Kernel.Ctx.{u}) := ∀ {A}, Var G A → Tm D A

noncomputable def Sub.lift (σ : Sub G D) : Sub (A :: G) (A :: D)
  | _, .here => .var .here
  | _, .there v => (σ v).rename (fun v => .there v)

noncomputable def Tm.subst (σ : Sub Γ Δ) : Tm Γ A → Tm Δ A
  | .var v => σ v
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .lam t => .lam (t.subst σ.lift)
  | .bool b => .bool b
  | .conj p q => .conj (p.subst σ) (q.subst σ)
  | .eq x y => .eq (x.subst σ) (y.subst σ)

theorem Tm.subst_congr (t : Tm Γ A) {σ τ : Sub Γ Δ}
    (h : ∀ {B} (v : Var Γ B), σ v = τ v) : t.subst σ = t.subst τ := by
  induction t generalizing Δ with
  | var v => exact h v
  | app f x ihf ihx => simp only [Tm.subst]; rw [ihf h, ihx h]
  | lam t ih =>
    apply congrArg Tm.lam
    apply ih
    intro B v
    cases v with
    | here => rfl
    | there v => simp only [Sub.lift]; rw [h v]
  | bool => rfl
  | conj p q ihp ihq => simp only [Tm.subst]; rw [ihp h, ihq h]
  | eq x y ihx ihy => simp only [Tm.subst]; rw [ihx h, ihy h]

noncomputable def Tm.toKernel : Tm Γ A → Kernel.Tm Γ A
  | .var v => .var v
  | .app f x => .app f.toKernel x.toKernel
  | .lam t => .lam t.toKernel
  | .bool b => .bool b
  | .conj p q => .conj p.toKernel q.toKernel
  | .eq x y => .eq x.toKernel y.toKernel

@[simp] theorem eval_toKernel (t : Tm Γ A) (ρ : Env Γ) :
    t.toKernel.eval ρ = t.eval ρ := by
  induction t with
  | var => rfl
  | app f x ihf ihx => simp [Tm.toKernel, Tm.eval, Kernel.Tm.eval, ihf, ihx]
  | lam t ih => funext x; exact ih _
  | bool => rfl
  | conj p q ihp ihq => simp [Tm.toKernel, Tm.eval, Kernel.Tm.eval, ihp, ihq]
  | eq x y ihx ihy => simp [Tm.toKernel, Tm.eval, Kernel.Tm.eval, ihx, ihy]

end Minimal

namespace Choice

inductive Tm : Kernel.Ctx.{u} → Kernel.Ty.{u} → Type (u + 1)
  | var : Var Γ A → Tm Γ A
  | app : Tm Γ (A.arr B) → Tm Γ A → Tm Γ B
  | lam : Tm (A :: Γ) B → Tm Γ (A.arr B)
  | bool : Bool → Tm Γ .bool
  | conj : Tm Γ .bool → Tm Γ .bool → Tm Γ .bool
  | eq : Tm Γ A → Tm Γ A → Tm Γ .bool
  | epsilon : Tm Γ (A.arr .bool) → Tm Γ A

def ofMinimal : Minimal.Tm Γ A → Tm Γ A
  | .var v => .var v
  | .app f x => .app (ofMinimal f) (ofMinimal x)
  | .lam t => .lam (ofMinimal t)
  | .bool b => .bool b
  | .conj p q => .conj (ofMinimal p) (ofMinimal q)
  | .eq x y => .eq (ofMinimal x) (ofMinimal y)

inductive Obstruction where | epsilon
  deriving DecidableEq

def project : Tm Γ A → Except Obstruction (Minimal.Tm Γ A)
  | .var v => pure (.var v)
  | .app f x => return .app (← project f) (← project x)
  | .lam t => return .lam (← project t)
  | .bool b => pure (.bool b)
  | .conj p q => return .conj (← project p) (← project q)
  | .eq x y => return .eq (← project x) (← project y)
  | .epsilon _ => .error .epsilon

@[simp] theorem project_ofMinimal (t : Minimal.Tm Γ A) : project (ofMinimal t) = .ok t := by
  induction t <;> simp_all only [ofMinimal, project] <;> rfl

theorem ofMinimal_injective : Function.Injective (@ofMinimal Γ A) := by
  intro x y h
  have := congrArg project h
  simpa using this

noncomputable def Tm.toKernel : Tm Γ A → Kernel.Tm Γ A
  | .var v => .var v
  | .app f x => .app f.toKernel x.toKernel
  | .lam t => .lam t.toKernel
  | .bool b => .bool b
  | .conj p q => .conj p.toKernel q.toKernel
  | .eq x y => .eq x.toKernel y.toKernel
  | .epsilon p => .epsilon p.toKernel

noncomputable def Tm.eval (t : Tm Γ A) (ρ : Env Γ) : A.El := t.toKernel.eval ρ

noncomputable def Tm.rename (σ : Ren Γ Δ) : Tm Γ A → Tm Δ A
  | .var v => .var (σ v)
  | .app f x => .app (f.rename σ) (x.rename σ)
  | .lam t => .lam (t.rename σ.lift)
  | .bool b => .bool b
  | .conj p q => .conj (p.rename σ) (q.rename σ)
  | .eq x y => .eq (x.rename σ) (y.rename σ)
  | .epsilon p => .epsilon (p.rename σ)

abbrev Sub (G D : Kernel.Ctx.{u}) := ∀ {A}, Var G A → Tm D A

noncomputable def Sub.lift (σ : Sub G D) : Sub (A :: G) (A :: D)
  | _, .here => .var .here
  | _, .there v => (σ v).rename (fun v => .there v)

noncomputable def Tm.subst (σ : Sub Γ Δ) : Tm Γ A → Tm Δ A
  | .var v => σ v
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .lam t => .lam (t.subst σ.lift)
  | .bool b => .bool b
  | .conj p q => .conj (p.subst σ) (q.subst σ)
  | .eq x y => .eq (x.subst σ) (y.subst σ)
  | .epsilon p => .epsilon (p.subst σ)

theorem Tm.subst_congr (t : Tm Γ A) {σ τ : Sub Γ Δ}
    (h : ∀ {B} (v : Var Γ B), σ v = τ v) : t.subst σ = t.subst τ := by
  induction t generalizing Δ with
  | var v => exact h v
  | app f x ihf ihx => simp only [Tm.subst]; rw [ihf h, ihx h]
  | lam t ih =>
    apply congrArg Tm.lam
    apply ih
    intro B v
    cases v with
    | here => rfl
    | there v => simp only [Sub.lift]; rw [h v]
  | bool => rfl
  | conj p q ihp ihq => simp only [Tm.subst]; rw [ihp h, ihq h]
  | eq x y ihx ihy => simp only [Tm.subst]; rw [ihx h, ihy h]
  | epsilon p ih => exact congrArg Tm.epsilon (ih h)

@[simp] theorem toKernel_ofMinimal (t : Minimal.Tm Γ A) :
    (ofMinimal t).toKernel = t.toKernel := by induction t <;> simp [ofMinimal, Tm.toKernel, Minimal.Tm.toKernel, *]

@[simp] theorem eval_ofMinimal (t : Minimal.Tm Γ A) (ρ : Env Γ) :
    (ofMinimal t).eval ρ = t.eval ρ := by
  rw [Tm.eval, toKernel_ofMinimal, Minimal.eval_toKernel]

@[simp] theorem rename_ofMinimal (t : Minimal.Tm Γ A) (σ : Ren Γ Δ) :
    (ofMinimal t).rename σ = ofMinimal (t.rename σ) := by
  induction t generalizing Δ <;> simp [ofMinimal, Tm.rename, Minimal.Tm.rename, *]

def ofMinimalSub (σ : Minimal.Sub G D) : Sub G D :=
  fun {_} v => ofMinimal (σ v)

@[simp] theorem subst_ofMinimal (t : Minimal.Tm Γ A) (σ : Minimal.Sub Γ Δ) :
    (ofMinimal t).subst (ofMinimalSub σ) = ofMinimal (t.subst σ) := by
  induction t generalizing Δ with
  | var => rfl
  | app f x ihf ihx => simp [ofMinimal, Tm.subst, Minimal.Tm.subst, ihf, ihx]
  | lam t ih =>
    apply congrArg Tm.lam
    calc
      (ofMinimal t).subst (Sub.lift (ofMinimalSub σ)) =
          (ofMinimal t).subst (ofMinimalSub (Minimal.Sub.lift σ)) :=
        Tm.subst_congr _ (by
          intro B v
          cases v <;> simp [ofMinimalSub, Sub.lift, Minimal.Sub.lift, rename_ofMinimal, ofMinimal])
      _ = ofMinimal (t.subst (Minimal.Sub.lift σ)) := ih _
  | bool => rfl
  | conj p q ihp ihq => simp [ofMinimal, Tm.subst, Minimal.Tm.subst, ihp, ihq]
  | eq x y ihx ihy => simp [ofMinimal, Tm.subst, Minimal.Tm.subst, ihx, ihy]

/-- An interpretation of choice syntax in the minimal language.  Its law says
exactly when this non-structural lowering preserves the standard semantics. -/
structure Lowering where
  epsilon : ∀ {Γ : Kernel.Ctx.{u}} {A : Kernel.Ty.{u}},
    Minimal.Tm Γ (A.arr .bool) → Minimal.Tm Γ A
  epsilon_eval : ∀ {Γ : Kernel.Ctx.{u}} {A : Kernel.Ty.{u}}
      (p : Minimal.Tm Γ (A.arr .bool)) (ρ : Env Γ),
    (epsilon p).eval ρ = (Kernel.Tm.epsilon p.toKernel).eval ρ

def lower (L : Lowering) : Tm Γ A → Minimal.Tm Γ A
  | .var v => .var v
  | .app f x => .app (lower L f) (lower L x)
  | .lam t => .lam (lower L t)
  | .bool b => .bool b
  | .conj p q => .conj (lower L p) (lower L q)
  | .eq x y => .eq (lower L x) (lower L y)
  | .epsilon p => L.epsilon (lower L p)

@[simp] theorem lower_ofMinimal (L : Lowering) (t : Minimal.Tm Γ A) :
    lower L (ofMinimal t) = t := by induction t <;> simp [lower, ofMinimal, *]

theorem eval_lower (L : Lowering) (t : Tm Γ A) (ρ : Env Γ) :
    (lower L t).eval ρ = t.eval ρ := by
  induction t with
  | var => rfl
  | app f x ihf ihx => simp [lower, Tm.eval, Tm.toKernel, Minimal.Tm.eval, Kernel.Tm.eval, ihf, ihx]
  | lam t ih => funext x; exact ih _
  | bool => rfl
  | conj p q ihp ihq => simp [lower, Tm.eval, Tm.toKernel, Minimal.Tm.eval, Kernel.Tm.eval, ihp, ihq]
  | eq x y ihx ihy => simp [lower, Tm.eval, Tm.toKernel, Minimal.Tm.eval, Kernel.Tm.eval, ihx, ihy]
  | epsilon p ih =>
    rw [lower, L.epsilon_eval]
    change (Kernel.Tm.epsilon (lower L p).toKernel).eval ρ =
      (Kernel.Tm.epsilon p.toKernel).eval ρ
    have hp := ih ρ
    simp only [Choice.Tm.eval] at hp
    change (if h : ∃ x, ((lower L p).toKernel.eval ρ x).down = true then
      Classical.choose h else _) =
      if h : ∃ x, (p.toKernel.eval ρ x).down = true then Classical.choose h else _
    have hp' : (lower L p).toKernel.eval ρ = p.toKernel.eval ρ := by
      exact (Minimal.eval_toKernel (lower L p) ρ).trans (by
        simpa only [Choice.Tm.eval] using hp)
    exact congrArg (fun f => if h : ∃ x, (f x).down = true then
      Classical.choose h else _) hp'

end Choice

namespace Typedef

inductive Tm : Kernel.Ctx.{u} → Kernel.Ty.{u} → Type (u + 1)
  | var : Var Γ A → Tm Γ A
  | app : Tm Γ (A.arr B) → Tm Γ A → Tm Γ B
  | lam : Tm (A :: Γ) B → Tm Γ (A.arr B)
  | bool : Bool → Tm Γ .bool
  | conj : Tm Γ .bool → Tm Γ .bool → Tm Γ .bool
  | eq : Tm Γ A → Tm Γ A → Tm Γ .bool
  | epsilon : Tm Γ (A.arr .bool) → Tm Γ A
  | abs (P : A.El → Prop) : Tm Γ A → Tm Γ (A.sub P)
  | rep (P : A.El → Prop) : Tm Γ (A.sub P) → Tm Γ A

def ofChoice : Choice.Tm Γ A → Tm Γ A
  | .var v => .var v
  | .app f x => .app (ofChoice f) (ofChoice x)
  | .lam t => .lam (ofChoice t)
  | .bool b => .bool b
  | .conj p q => .conj (ofChoice p) (ofChoice q)
  | .eq x y => .eq (ofChoice x) (ofChoice y)
  | .epsilon p => .epsilon (ofChoice p)

inductive Obstruction where | abs | rep
  deriving DecidableEq

def project : Tm Γ A → Except Obstruction (Choice.Tm Γ A)
  | .var v => pure (.var v)
  | .app f x => return .app (← project f) (← project x)
  | .lam t => return .lam (← project t)
  | .bool b => pure (.bool b)
  | .conj p q => return .conj (← project p) (← project q)
  | .eq x y => return .eq (← project x) (← project y)
  | .epsilon p => return .epsilon (← project p)
  | .abs _ _ => .error .abs
  | .rep _ _ => .error .rep

@[simp] theorem project_ofChoice (t : Choice.Tm Γ A) : project (ofChoice t) = .ok t := by
  induction t <;> simp_all only [ofChoice, project] <;> rfl

theorem ofChoice_injective : Function.Injective (@ofChoice Γ A) := by
  intro x y h
  have := congrArg project h
  simpa using this

noncomputable def toKernel : Tm Γ A → Kernel.Tm Γ A
  | .var v => .var v
  | .app f x => .app (toKernel f) (toKernel x)
  | .lam t => .lam (toKernel t)
  | .bool b => .bool b
  | .conj p q => .conj (toKernel p) (toKernel q)
  | .eq x y => .eq (toKernel x) (toKernel y)
  | .epsilon p => .epsilon (toKernel p)
  | .abs P x => .abs P (toKernel x)
  | .rep P x => .rep P (toKernel x)

noncomputable def Tm.eval (t : Tm Γ A) (ρ : Env Γ) : A.El := (toKernel t).eval ρ

noncomputable def Tm.rename (σ : Ren Γ Δ) : Tm Γ A → Tm Δ A
  | .var v => .var (σ v)
  | .app f x => .app (f.rename σ) (x.rename σ)
  | .lam t => .lam (t.rename σ.lift)
  | .bool b => .bool b
  | .conj p q => .conj (p.rename σ) (q.rename σ)
  | .eq x y => .eq (x.rename σ) (y.rename σ)
  | .epsilon p => .epsilon (p.rename σ)
  | .abs P x => .abs P (x.rename σ)
  | .rep P x => .rep P (x.rename σ)

abbrev Sub (G D : Kernel.Ctx.{u}) := ∀ {A}, Var G A → Tm D A

noncomputable def Sub.lift (σ : Sub G D) : Sub (A :: G) (A :: D)
  | _, .here => .var .here
  | _, .there v => (σ v).rename (fun v => .there v)

noncomputable def Tm.subst (σ : Sub Γ Δ) : Tm Γ A → Tm Δ A
  | .var v => σ v
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .lam t => .lam (t.subst σ.lift)
  | .bool b => .bool b
  | .conj p q => .conj (p.subst σ) (q.subst σ)
  | .eq x y => .eq (x.subst σ) (y.subst σ)
  | .epsilon p => .epsilon (p.subst σ)
  | .abs P x => .abs P (x.subst σ)
  | .rep P x => .rep P (x.subst σ)

theorem Tm.subst_congr (t : Tm Γ A) {σ τ : Sub Γ Δ}
    (h : ∀ {B} (v : Var Γ B), σ v = τ v) : t.subst σ = t.subst τ := by
  induction t generalizing Δ with
  | var v => exact h v
  | app f x ihf ihx => simp only [Tm.subst]; rw [ihf h, ihx h]
  | lam t ih =>
    apply congrArg Tm.lam
    apply ih
    intro B v
    cases v with
    | here => rfl
    | there v => simp only [Sub.lift]; rw [h v]
  | bool => rfl
  | conj p q ihp ihq => simp only [Tm.subst]; rw [ihp h, ihq h]
  | eq x y ihx ihy => simp only [Tm.subst]; rw [ihx h, ihy h]
  | epsilon p ih => exact congrArg Tm.epsilon (ih h)
  | abs P x ih => exact congrArg (Tm.abs P) (ih h)
  | rep P x ih => exact congrArg (Tm.rep P) (ih h)

noncomputable def ofKernel : Kernel.Tm Γ A → Tm Γ A
  | .var v => .var v
  | .app f x => .app (ofKernel f) (ofKernel x)
  | .lam t => .lam (ofKernel t)
  | .bool b => .bool b
  | .conj p q => .conj (ofKernel p) (ofKernel q)
  | .eq x y => .eq (ofKernel x) (ofKernel y)
  | .epsilon p => .epsilon (ofKernel p)
  | .abs P x => .abs P (ofKernel x)
  | .rep P x => .rep P (ofKernel x)

@[simp] theorem toKernel_ofKernel (t : Kernel.Tm Γ A) : toKernel (ofKernel t) = t := by
  induction t <;> simp [toKernel, ofKernel, *]

@[simp] theorem ofKernel_toKernel (t : Tm Γ A) : ofKernel (toKernel t) = t := by
  induction t <;> simp [toKernel, ofKernel, *]

structure KernelEquivalence (Γ : Kernel.Ctx.{u}) (A : Kernel.Ty.{u}) where
  toKernel : Tm Γ A → Kernel.Tm Γ A
  ofKernel : Kernel.Tm Γ A → Tm Γ A
  left_inv : Function.LeftInverse ofKernel toKernel
  right_inv : Function.RightInverse ofKernel toKernel

noncomputable def kernelEquivalence : KernelEquivalence Γ A where
  toKernel := toKernel
  ofKernel := ofKernel
  left_inv := ofKernel_toKernel
  right_inv := toKernel_ofKernel

@[simp] theorem toKernel_ofChoice (t : Choice.Tm Γ A) :
    toKernel (ofChoice t) = t.toKernel := by induction t <;> simp [ofChoice, toKernel, Choice.Tm.toKernel, *]

@[simp] theorem eval_ofChoice (t : Choice.Tm Γ A) (ρ : Env Γ) :
    (ofChoice t).eval ρ = t.eval ρ := by rw [Tm.eval, Choice.Tm.eval, toKernel_ofChoice]

@[simp] theorem rename_ofChoice (t : Choice.Tm Γ A) (σ : Ren Γ Δ) :
    (ofChoice t).rename σ = ofChoice (t.rename σ) := by
  induction t generalizing Δ <;> simp [ofChoice, Tm.rename, Choice.Tm.rename, *]

def ofChoiceSub (σ : Choice.Sub G D) : Sub G D :=
  fun {_} v => ofChoice (σ v)

@[simp] theorem subst_ofChoice (t : Choice.Tm Γ A) (σ : Choice.Sub Γ Δ) :
    (ofChoice t).subst (ofChoiceSub σ) = ofChoice (t.subst σ) := by
  induction t generalizing Δ with
  | var => rfl
  | app f x ihf ihx => simp [ofChoice, Tm.subst, Choice.Tm.subst, ihf, ihx]
  | lam t ih =>
    apply congrArg Tm.lam
    calc
      (ofChoice t).subst (Sub.lift (ofChoiceSub σ)) =
          (ofChoice t).subst (ofChoiceSub (Choice.Sub.lift σ)) :=
        Tm.subst_congr _ (by
          intro B v
          cases v <;> simp [ofChoiceSub, Sub.lift, Choice.Sub.lift, rename_ofChoice, ofChoice])
      _ = ofChoice (t.subst (Choice.Sub.lift σ)) := ih _
  | bool => rfl
  | conj p q ihp ihq => simp [ofChoice, Tm.subst, Choice.Tm.subst, ihp, ihq]
  | eq x y ihx ihy => simp [ofChoice, Tm.subst, Choice.Tm.subst, ihx, ihy]
  | epsilon p ih => simp [ofChoice, Tm.subst, Choice.Tm.subst, ih]

structure Lowering where
  abs : ∀ {Γ : Kernel.Ctx.{u}} {A : Kernel.Ty.{u}}
    (P : A.El → Prop), Choice.Tm Γ A → Choice.Tm Γ (A.sub P)
  rep : ∀ {Γ : Kernel.Ctx.{u}} {A : Kernel.Ty.{u}}
    (P : A.El → Prop), Choice.Tm Γ (A.sub P) → Choice.Tm Γ A
  abs_eval : ∀ {Γ : Kernel.Ctx.{u}} {A : Kernel.Ty.{u}}
      (P : A.El → Prop) (x : Choice.Tm Γ A) (ρ : Env Γ),
    (abs P x).eval ρ = (Kernel.Tm.abs P x.toKernel).eval ρ
  rep_eval : ∀ {Γ : Kernel.Ctx.{u}} {A : Kernel.Ty.{u}}
      (P : A.El → Prop) (x : Choice.Tm Γ (A.sub P)) (ρ : Env Γ),
    (rep P x).eval ρ = (Kernel.Tm.rep P x.toKernel).eval ρ

def lower (L : Lowering) : Tm Γ A → Choice.Tm Γ A
  | .var v => .var v
  | .app f x => .app (lower L f) (lower L x)
  | .lam t => .lam (lower L t)
  | .bool b => .bool b
  | .conj p q => .conj (lower L p) (lower L q)
  | .eq x y => .eq (lower L x) (lower L y)
  | .epsilon p => .epsilon (lower L p)
  | .abs P x => L.abs P (lower L x)
  | .rep P x => L.rep P (lower L x)

@[simp] theorem lower_ofChoice (L : Lowering) (t : Choice.Tm Γ A) :
    lower L (ofChoice t) = t := by induction t <;> simp [lower, ofChoice, *]

theorem eval_lower (L : Lowering) (t : Tm Γ A) (ρ : Env Γ) :
    (lower L t).eval ρ = t.eval ρ := by
  induction t with
  | var => rfl
  | app f x ihf ihx =>
    change (lower L f).toKernel.eval ρ ((lower L x).toKernel.eval ρ) =
      (toKernel f).eval ρ ((toKernel x).eval ρ)
    have hf := ihf ρ
    have hx := ihx ρ
    simp only [Choice.Tm.eval, Typedef.Tm.eval] at hf hx
    rw [hf, hx]
  | lam t ih => funext x; exact ih _
  | bool => rfl
  | conj p q ihp ihq =>
    change ULift.up (((lower L p).toKernel.eval ρ).down && ((lower L q).toKernel.eval ρ).down) =
      ULift.up (((toKernel p).eval ρ).down && ((toKernel q).eval ρ).down)
    have hp := ihp ρ
    have hq := ihq ρ
    simp only [Choice.Tm.eval, Typedef.Tm.eval] at hp hq
    rw [hp, hq]
  | eq x y ihx ihy =>
    change (if (lower L x).toKernel.eval ρ = (lower L y).toKernel.eval ρ then _ else _) =
      if (toKernel x).eval ρ = (toKernel y).eval ρ then _ else _
    have hx := ihx ρ
    have hy := ihy ρ
    simp only [Choice.Tm.eval, Typedef.Tm.eval] at hx hy
    rw [hx, hy]
  | epsilon p ih =>
    change (Kernel.Tm.epsilon (lower L p).toKernel).eval ρ =
      (Kernel.Tm.epsilon (toKernel p)).eval ρ
    have hp := ih ρ
    simp only [Choice.Tm.eval, Typedef.Tm.eval] at hp
    simp only [Kernel.Tm.eval]
    rw [hp]
  | abs P x ih =>
    rw [lower, L.abs_eval]
    change (Kernel.Tm.abs P (lower L x).toKernel).eval ρ =
      (Kernel.Tm.abs P (toKernel x)).eval ρ
    have hx := ih ρ
    simp only [Choice.Tm.eval, Typedef.Tm.eval] at hx
    simp only [Kernel.Tm.eval]
    rw [hx]
  | rep P x ih =>
    rw [lower, L.rep_eval]
    change (Kernel.Tm.rep P (lower L x).toKernel).eval ρ =
      (Kernel.Tm.rep P (toKernel x)).eval ρ
    have hx := ih ρ
    simp only [Choice.Tm.eval, Typedef.Tm.eval] at hx
    simp only [Kernel.Tm.eval]
    rw [hx]

/-- The obstruction reported when lowering the full language directly to the
minimal fragment.  The first unsupported constructor in structural traversal
is retained rather than collapsed to a bare failure. -/
inductive MinimalObstruction where
  | epsilon | abs | rep
  deriving DecidableEq

def projectMinimal (t : Tm Γ A) : Except MinimalObstruction (Minimal.Tm Γ A) :=
  match project t with
  | .error .abs => .error .abs
  | .error .rep => .error .rep
  | .ok c => match Choice.project c with
    | .error .epsilon => .error .epsilon
    | .ok m => .ok m

def ofMinimal (t : Minimal.Tm Γ A) : Tm Γ A := ofChoice (Choice.ofMinimal t)

@[simp] theorem projectMinimal_ofMinimal (t : Minimal.Tm Γ A) :
    projectMinimal (ofMinimal t) = .ok t := by
  rw [projectMinimal, ofMinimal, project_ofChoice]
  change (match Choice.project (Choice.ofMinimal t) with
    | Except.error Choice.Obstruction.epsilon =>
        Except.error MinimalObstruction.epsilon
    | Except.ok m => Except.ok m) = Except.ok t
  rw [Choice.project_ofMinimal]

theorem ofMinimal_injective : Function.Injective (@ofMinimal Γ A) := by
  intro x y h
  have := congrArg projectMinimal h
  simpa using this

@[simp] theorem rename_ofMinimal (t : Minimal.Tm Γ A) (σ : Ren Γ Δ) :
    (ofMinimal t).rename σ = ofMinimal (t.rename σ) := by
  simp [ofMinimal, rename_ofChoice, Choice.rename_ofMinimal]

def ofMinimalSub (σ : Minimal.Sub G D) : Sub G D :=
  ofChoiceSub (Choice.ofMinimalSub σ)

@[simp] theorem subst_ofMinimal (t : Minimal.Tm Γ A) (σ : Minimal.Sub Γ Δ) :
    (ofMinimal t).subst (ofMinimalSub σ) = ofMinimal (t.subst σ) := by
  simp [ofMinimal, ofMinimalSub, subst_ofChoice, Choice.subst_ofMinimal]

@[simp] theorem eval_ofMinimal (t : Minimal.Tm Γ A) (ρ : Env Γ) :
    (ofMinimal t).eval ρ = t.eval ρ := by
  rw [ofMinimal, eval_ofChoice, Choice.eval_ofMinimal]

end Typedef

end

end ProjectBeth.HOL.SyntaxTower
