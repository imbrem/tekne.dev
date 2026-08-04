import ProjectBeth.Defs.Syntax.Representations
import Mathlib.Logic.Equiv.Defs

universe u v

namespace ProjectBeth.Syntax

namespace LocallyNameless

/-- A generic locally-nameless transformer for syntax signatures parameterized by
their variable type. -/
abbrev Transform (Syntax : Type u → Type v) (Name : Type u) : Type v :=
  Syntax (Var Name)

def shiftVar : Var Name → Var Name
  | .bound i => .bound (i + 1)
  | .free x => .free x

/-- Interpret a bounded de Bruijn term using an arbitrary locally-nameless variable
environment.  Extending the environment beneath a binder is the generic
locally-nameless operation. -/
def ofBoundedWith (ρ : Fin n → Var Name) : Bounded.Tm n → Tm Name
  | .var i => .var (ρ i)
  | .app f a => .app (ofBoundedWith ρ f) (ofBoundedWith ρ a)
  | .lam b => .lam (ofBoundedWith (Fin.cases (.bound 0) (fun i => shiftVar (ρ i))) b)

def ofBounded (t : Bounded.Tm n) : Tm (Fin n) :=
  ofBoundedWith Var.free t

end LocallyNameless

namespace Named

variable {Name : Type u} [DecidableEq Name]

/-- Raw named terms are alpha-equivalent exactly when erasing binder spellings to
locally nameless syntax gives the same tree. -/
def Alpha (t u : Tm Name) : Prop :=
  LocallyNameless.ofNamed [] t = LocallyNameless.ofNamed [] u

instance alphaDecidable (t u : Tm Name) : Decidable (Alpha t u) :=
  inferInstanceAs (Decidable (LocallyNameless.ofNamed [] t = LocallyNameless.ofNamed [] u))

/-- HOL Light-style computable alpha-conversion test. -/
def aconv (t u : Tm Name) : Bool := decide (Alpha t u)

theorem aconv_correct {t u : Tm Name} : aconv t u = true ↔ Alpha t u := by
  simp [aconv]

theorem aconv_false {t u : Tm Name} : aconv t u = false ↔ ¬Alpha t u := by
  simp [aconv]

@[refl] theorem Alpha.refl (t : Tm Name) : Alpha t t := rfl

@[symm] theorem Alpha.symm {t u : Tm Name} : Alpha t u → Alpha u t := Eq.symm

theorem Alpha.trans {t u v : Tm Name} : Alpha t u → Alpha u v → Alpha t v :=
  Eq.trans

instance alphaSetoid : Setoid (Tm Name) where
  r := Alpha
  iseqv := ⟨Alpha.refl, Alpha.symm, Alpha.trans⟩

theorem alpha_lam_rename {x y : Name} {b c : Tm Name}
    (h : LocallyNameless.ofNamed [x] b = LocallyNameless.ofNamed [y] c) :
    Alpha (.lam x b) (.lam y c) := by
  exact congrArg LocallyNameless.Tm.lam h

/-- A direct, syntactic named/de-Bruijn correspondence mediated by the generic
locally-nameless transformer.  It does not quotient or replace raw named terms. -/
def Represents (t : Tm (Fin n)) (d : Bounded.Tm n) : Prop :=
  LocallyNameless.ofNamed [] t = LocallyNameless.ofBounded d

theorem represents_alpha {t u : Tm (Fin n)} {d : Bounded.Tm n}
    (ht : Represents t d) (hu : Represents u d) : Alpha t u := by
  exact ht.trans hu.symm

theorem aconv_of_represents {t u : Tm (Fin n)} {d : Bounded.Tm n}
    (ht : Represents t d) (hu : Represents u d) : aconv t u = true :=
  aconv_correct.mpr (represents_alpha ht hu)

namespace AlphaQuotient

/-- Raw named syntax modulo alpha-equivalence. -/
abbrev Q (Name : Type u) [DecidableEq Name] := Quotient (alphaSetoid (Name := Name))

/-- Fully nameless trees which arise from raw named syntax.  Binders are de Bruijn
indices and free variables retain their names. -/
abbrev ScopedNameless (Name : Type u) [DecidableEq Name] :=
  {x : LocallyNameless.Tm Name // ∃ t : Tm Name, LocallyNameless.ofNamed [] t = x}

def toScoped : Q Name → ScopedNameless Name :=
  Quotient.lift (fun t : Tm Name => ⟨LocallyNameless.ofNamed [] t, ⟨t, rfl⟩⟩)
    (fun _ _ h => Subtype.ext h)

noncomputable def ofScoped : ScopedNameless Name → Q Name :=
  fun t => Quotient.mk _ (Classical.choose t.property)

noncomputable def equivScoped : Equiv (Q Name) (ScopedNameless Name) where
  toFun := toScoped
  invFun := ofScoped
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ t =>
      apply Quotient.sound
      exact (Classical.choose_spec
        (show ∃ a, LocallyNameless.ofNamed [] a = LocallyNameless.ofNamed [] t from
          (toScoped (Quotient.mk _ t)).property)).trans rfl
  right_inv t := by
    apply Subtype.ext
    exact Classical.choose_spec t.property

/-- Any semantics defined on the nameless representation lifts canonically to the
alpha quotient. -/
def eval (sem : LocallyNameless.Tm Name → S) : Q Name → S :=
  fun q => sem (toScoped q).1

@[simp] theorem eval_mk (sem : LocallyNameless.Tm Name → S) (t : Tm Name) :
    eval sem (Quotient.mk _ t) = sem (LocallyNameless.ofNamed [] t) := rfl

theorem eval_eq_of_aconv (sem : LocallyNameless.Tm Name → S) {t u : Tm Name}
    (h : aconv t u = true) :
    eval sem (Quotient.mk _ t) = eval sem (Quotient.mk _ u) := by
  change sem (LocallyNameless.ofNamed [] t) = sem (LocallyNameless.ofNamed [] u)
  exact congrArg sem (aconv_correct.mp h)

end AlphaQuotient

end Named

end ProjectBeth.Syntax
