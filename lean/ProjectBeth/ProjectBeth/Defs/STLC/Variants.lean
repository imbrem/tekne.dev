import ProjectBeth.Defs.STLC.Core

universe u v

namespace ProjectBeth.STLC

namespace Arrow

inductive Ty (Base : Type u) : Type u
  | base : Base → Ty Base
  | arr : Ty Base → Ty Base → Ty Base

abbrev Tm {Base : Type u} := ArrowTm (@Ty.arr Base)

def Ty.denote {Base : Type u} (El : Base → Type v) : Ty Base → Type v
  | .base A => El A
  | .arr A B => Ty.denote El A → Ty.denote El B

def Tm.denote {Base : Type u} (El : Base → Type v) :
    {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Env (Ty.denote El) Γ → Ty.denote El A
  | _, _, .var x, env => x.lookup env
  | _, _, .app f x, env => denote El f env (denote El x env)
  | _, _, .lam t, env => fun x => denote El t (x, env)

end Arrow

namespace ArrowProd

inductive Ty (Base : Type u) : Type u
  | base : Base → Ty Base
  | arr : Ty Base → Ty Base → Ty Base
  | prod : Ty Base → Ty Base → Ty Base

inductive Tm {Base : Type u} : List (Ty Base) → Ty Base → Type u
  | var : Var Γ A → Tm Γ A
  | app : Tm Γ (.arr A B) → Tm Γ A → Tm Γ B
  | lam : Tm (A :: Γ) B → Tm Γ (.arr A B)
  | pair : Tm Γ A → Tm Γ B → Tm Γ (.prod A B)
  | fst : Tm Γ (.prod A B) → Tm Γ A
  | snd : Tm Γ (.prod A B) → Tm Γ B

def Ty.denote {Base : Type u} (El : Base → Type v) : Ty Base → Type v
  | .base A => El A
  | .arr A B => Ty.denote El A → Ty.denote El B
  | .prod A B => Ty.denote El A × Ty.denote El B

def Tm.denote {Base : Type u} (El : Base → Type v) :
    {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Env (Ty.denote El) Γ → Ty.denote El A
  | _, _, .var x, env => x.lookup env
  | _, _, .app f x, env => denote El f env (denote El x env)
  | _, _, .lam t, env => fun x => denote El t (x, env)
  | _, _, .pair a b, env => (denote El a env, denote El b env)
  | _, _, .fst p, env => (denote El p env).1
  | _, _, .snd p, env => (denote El p env).2

end ArrowProd

namespace ArrowProdSum

inductive Ty (Base : Type u) : Type u
  | base : Base → Ty Base
  | arr : Ty Base → Ty Base → Ty Base
  | prod : Ty Base → Ty Base → Ty Base
  | sum : Ty Base → Ty Base → Ty Base

inductive Tm {Base : Type u} : List (Ty Base) → Ty Base → Type u
  | var : Var Γ A → Tm Γ A
  | app : Tm Γ (.arr A B) → Tm Γ A → Tm Γ B
  | lam : Tm (A :: Γ) B → Tm Γ (.arr A B)
  | pair : Tm Γ A → Tm Γ B → Tm Γ (.prod A B)
  | fst : Tm Γ (.prod A B) → Tm Γ A
  | snd : Tm Γ (.prod A B) → Tm Γ B
  | inl : Tm Γ A → Tm Γ (.sum A B)
  | inr : Tm Γ B → Tm Γ (.sum A B)
  | case : Tm Γ (.sum A B) → Tm (A :: Γ) C → Tm (B :: Γ) C → Tm Γ C

def Ty.denote {Base : Type u} (El : Base → Type v) : Ty Base → Type v
  | .base A => El A
  | .arr A B => Ty.denote El A → Ty.denote El B
  | .prod A B => Ty.denote El A × Ty.denote El B
  | .sum A B => Ty.denote El A ⊕ Ty.denote El B

def Tm.denote {Base : Type u} (El : Base → Type v) :
    {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Env (Ty.denote El) Γ → Ty.denote El A
  | _, _, .var x, env => x.lookup env
  | _, _, .app f x, env => denote El f env (denote El x env)
  | _, _, .lam t, env => fun x => denote El t (x, env)
  | _, _, .pair a b, env => (denote El a env, denote El b env)
  | _, _, .fst p, env => (denote El p env).1
  | _, _, .snd p, env => (denote El p env).2
  | _, _, .inl x, env => Sum.inl (denote El x env)
  | _, _, .inr x, env => Sum.inr (denote El x env)
  | _, _, .case s l r, env =>
      Sum.elim (fun x => denote El l (x, env)) (fun x => denote El r (x, env))
        (denote El s env)

end ArrowProdSum

namespace Full

inductive Ty (Base : Type u) : Type u
  | base : Base → Ty Base
  | arr : Ty Base → Ty Base → Ty Base
  | prod : Ty Base → Ty Base → Ty Base
  | sum : Ty Base → Ty Base → Ty Base
  | bool : Ty Base
  | nat : Ty Base

inductive Tm {Base : Type u} : List (Ty Base) → Ty Base → Type u
  | var : Var Γ A → Tm Γ A
  | app : Tm Γ (.arr A B) → Tm Γ A → Tm Γ B
  | lam : Tm (A :: Γ) B → Tm Γ (.arr A B)
  | pair : Tm Γ A → Tm Γ B → Tm Γ (.prod A B)
  | fst : Tm Γ (.prod A B) → Tm Γ A
  | snd : Tm Γ (.prod A B) → Tm Γ B
  | inl : Tm Γ A → Tm Γ (.sum A B)
  | inr : Tm Γ B → Tm Γ (.sum A B)
  | case : Tm Γ (.sum A B) → Tm (A :: Γ) C → Tm (B :: Γ) C → Tm Γ C
  | bool : Bool → Tm Γ .bool
  | ite : Tm Γ .bool → Tm Γ A → Tm Γ A → Tm Γ A
  | nat : Nat → Tm Γ .nat

def Ty.denote {Base : Type u} (El : Base → Type v) : Ty Base → Type v
  | .base A => El A
  | .arr A B => Ty.denote El A → Ty.denote El B
  | .prod A B => Ty.denote El A × Ty.denote El B
  | .sum A B => Ty.denote El A ⊕ Ty.denote El B
  | .bool => ULift.{v} Bool
  | .nat => ULift.{v} Nat

def Tm.denote {Base : Type u} (El : Base → Type v) :
    {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Env (Ty.denote El) Γ → Ty.denote El A
  | _, _, .var x, env => x.lookup env
  | _, _, .app f x, env => denote El f env (denote El x env)
  | _, _, .lam t, env => fun x => denote El t (x, env)
  | _, _, .pair a b, env => (denote El a env, denote El b env)
  | _, _, .fst p, env => (denote El p env).1
  | _, _, .snd p, env => (denote El p env).2
  | _, _, .inl x, env => Sum.inl (denote El x env)
  | _, _, .inr x, env => Sum.inr (denote El x env)
  | _, _, .case s l r, env =>
      Sum.elim (fun x => denote El l (x, env)) (fun x => denote El r (x, env))
        (denote El s env)
  | _, _, .bool b, _ => ULift.up b
  | _, _, .ite c t e, env =>
      if (denote El c env).down then denote El t env else denote El e env
  | _, _, .nat n, _ => ULift.up n

end Full

end ProjectBeth.STLC
