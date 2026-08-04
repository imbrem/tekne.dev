import ProjectBeth.Defs.HOL.Syntax

namespace ProjectBeth.HOL.Kernel

noncomputable section
attribute [local instance] Classical.propDecidable

structure Ty where
  El : Type 1
  default : El

abbrev Ty.bool : Ty := ⟨ULift Bool, ⟨false⟩⟩
def Ty.arr (A B : Ty) : Ty := ⟨A.El → B.El, fun _ => B.default⟩
noncomputable def Ty.sub (A : Ty) (P : A.El → Prop) : Ty :=
  ⟨TotalSubtype A.El P, @TotalSubtype.abs _ ⟨A.default⟩ P A.default⟩

abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type 2
  | here : Var (A :: Γ) A
  | there : Var Γ A → Var (B :: Γ) A

abbrev Env (Γ : Ctx) := ∀ {A}, Var Γ A → A.El

def Env.cons (x : A.El) (ρ : Env Γ) : Env (A :: Γ)
  | _, .here => x
  | _, .there v => ρ v

inductive Tm : Ctx → Ty → Type 2
  | var : Var Γ A → Tm Γ A
  | app : Tm Γ (A.arr B) → Tm Γ A → Tm Γ B
  | lam : Tm (A :: Γ) B → Tm Γ (A.arr B)
  | bool : Bool → Tm Γ .bool
  | conj : Tm Γ .bool → Tm Γ .bool → Tm Γ .bool
  | eq : Tm Γ A → Tm Γ A → Tm Γ .bool
  | epsilon : Tm Γ (A.arr .bool) → Tm Γ A
  | abs (P : A.El → Prop) : Tm Γ A → Tm Γ (A.sub P)
  | rep (P : A.El → Prop) : Tm Γ (A.sub P) → Tm Γ A

noncomputable def Tm.eval : Tm Γ A → Env Γ → A.El
  | .var v, ρ => ρ v
  | .app f x, ρ => f.eval ρ (x.eval ρ)
  | .lam t, ρ => fun x => t.eval (ρ.cons x)
  | .bool b, _ => ⟨b⟩
  | .conj p q, ρ => ⟨(p.eval ρ).down && (q.eval ρ).down⟩
  | .eq x y, ρ => if x.eval ρ = y.eval ρ then ⟨true⟩ else ⟨false⟩
  | @epsilon _ A p, ρ =>
      if h : ∃ x, (p.eval ρ x).down = true then Classical.choose h else A.default
  | @abs _ A P x, ρ => @TotalSubtype.abs _ ⟨A.default⟩ P (x.eval ρ)
  | .rep _ x, ρ => TotalSubtype.rep (x.eval ρ)

abbrev Ren (Γ Δ : Ctx) := ∀ {A}, Var Γ A → Var Δ A

def Ren.lift (σ : Ren Γ Δ) : Ren (A :: Γ) (A :: Δ)
  | _, .here => .here
  | _, .there v => .there (σ v)

def Ren.env (σ : Ren Γ Δ) (ρ : Env Δ) : Env Γ := fun v => ρ (σ v)

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

theorem Tm.eval_rename (t : Tm Γ A) (σ : Ren Γ Δ) (ρ : Env Δ) :
    (t.rename σ).eval ρ = t.eval (σ.env ρ) := by
  induction t generalizing Δ with
  | var => rfl
  | app f x ihf ihx => simp [rename, eval, ihf, ihx]
  | lam t ih =>
    funext x
    change (t.rename σ.lift).eval (Env.cons x ρ) = t.eval (Env.cons x (σ.env ρ))
    rw [ih]
    apply congrArg t.eval
    funext B v
    cases v <;> rfl
  | bool => rfl
  | conj p q ihp ihq => simp [rename, eval, ihp, ihq]
  | eq x y ihx ihy => simp [rename, eval, ihx, ihy]
  | epsilon p ih => simp [rename, eval, ih]
  | abs P x ih => simp [rename, eval, ih]; rfl
  | rep P x ih => simp [rename, eval, ih]

abbrev Sub (Γ Δ : Ctx) := ∀ {A}, Var Γ A → Tm Δ A

noncomputable def Sub.lift (σ : Sub Γ Δ) : Sub (A :: Γ) (A :: Δ)
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

noncomputable def Sub.env (σ : Sub Γ Δ) (ρ : Env Δ) : Env Γ := fun v => (σ v).eval ρ

theorem Sub.env_lift {A : Ty} (σ : Sub Γ Δ) (ρ : Env Δ) (x : A.El) :
    (Sub.env σ.lift (Env.cons x ρ) : Env (A :: Γ)) =
      (Env.cons x (Sub.env σ ρ) : Env (A :: Γ)) := by
  funext B v
  cases v with
  | here => rfl
  | there v => exact Tm.eval_rename (σ v) (fun v => .there v) (Env.cons x ρ)

theorem Tm.eval_subst (t : Tm Γ A) (σ : Sub Γ Δ) (ρ : Env Δ) :
    (t.subst σ).eval ρ = t.eval (Sub.env σ ρ) := by
  induction t generalizing Δ with
  | var => rfl
  | app f x ihf ihx => simp [subst, eval, ihf, ihx]
  | lam t ih =>
    funext x
    change (t.subst σ.lift).eval (Env.cons x ρ) = t.eval (Env.cons x (Sub.env σ ρ))
    rw [ih, Sub.env_lift]
  | bool => rfl
  | conj p q ihp ihq => simp [subst, eval, ihp, ihq]
  | eq x y ihx ihy => simp [subst, eval, ihx, ihy]
  | epsilon p ih => simp [subst, eval, ih]
  | abs P x ih => simp [subst, eval, ih]; rfl
  | rep P x ih => simp [subst, eval, ih]

noncomputable def Sub.single (x : Tm Γ A) : Sub (A :: Γ) Γ
  | _, .here => x
  | _, .there v => .var v

noncomputable def Tm.subst0 (t : Tm (A :: Γ) B) (x : Tm Γ A) : Tm Γ B :=
  t.subst (Sub.single x)

inductive Eqv : Tm Γ A → Tm Γ A → Type 2
  | refl (t) : Eqv t t
  | symm : Eqv s t → Eqv t s
  | trans : Eqv r s → Eqv s t → Eqv r t
  | app : Eqv f g → Eqv x y → Eqv (.app f x) (.app g y)
  | lam : Eqv s t → Eqv (.lam s) (.lam t)
  | beta (t : Tm (A :: Γ) B) (x : Tm Γ A) : Eqv (.app (.lam t) x) (t.subst0 x)
  | boolExt {p q : Tm Γ Ty.bool} :
      (∀ ρ, (p.eval ρ).down = (q.eval ρ).down) → Eqv p q
  | abs_rep {A : Ty} (P : A.El → Prop) (x : Tm Γ (A.sub P)) :
      Eqv (.abs P (.rep P x)) x
  | rep_abs {A : Ty} (P : A.El → Prop) (x : Tm Γ A) :
      (∀ ρ, P (x.eval ρ)) → Eqv (.rep P (.abs P x)) x

theorem uliftBool_ext {x y : ULift Bool} (h : x.down = y.down) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem Eqv.valid {s t : Tm Γ A} (h : Eqv s t) (ρ : Env Γ) : s.eval ρ = t.eval ρ := by
  induction h with
  | refl => rfl
  | symm _ ih => exact (ih ρ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ ρ).trans (ih₂ ρ)
  | app _ _ ihf ihx => simp [Tm.eval, ihf ρ, ihx ρ]
  | lam _ ih => funext x; exact ih (Env.cons x ρ)
  | beta t x =>
      have he : (Sub.env (Sub.single x) ρ : Env (_ :: _)) =
          (Env.cons (x.eval ρ) ρ : Env (_ :: _)) := by
        funext B v
        cases v <;> rfl
      rw [Tm.eval, Tm.subst0, Tm.eval_subst, he]
      rfl
  | boolExt h => exact uliftBool_ext (h ρ)
  | @abs_rep _ A P x => exact @TotalSubtype.abs_rep _ ⟨A.default⟩ P _
  | @rep_abs _ A P x hP => exact @TotalSubtype.rep_abs_of _ ⟨A.default⟩ P _ (hP ρ)

end

end ProjectBeth.HOL.Kernel
