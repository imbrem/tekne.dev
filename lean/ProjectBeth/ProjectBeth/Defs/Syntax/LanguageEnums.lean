import ProjectBeth.Defs.Syntax.Representations

namespace ProjectBeth.Syntax.Language

inductive Fragment
  | stlc | let | cases | letCases | inductive | coinductive
  deriving DecidableEq

inductive HasLet : Fragment → Prop | let : HasLet .let | letCases : HasLet .letCases
inductive HasCases : Fragment → Prop | cases : HasCases .cases | letCases : HasCases .letCases
inductive HasInductive : Fragment → Prop | intro : HasInductive .inductive
inductive HasCoinductive : Fragment → Prop | intro : HasCoinductive .coinductive

/-- The six requested ordinary, untyped syntax enums, indexed by their feature set. -/
inductive Raw (F : Fragment) : Type
  | var : Nat → Raw F
  | app : Raw F → Raw F → Raw F
  | lam : Raw F → Raw F
  | letE : HasLet F → Raw F → Raw F → Raw F
  | pair : HasCases F → Raw F → Raw F → Raw F
  | fst : HasCases F → Raw F → Raw F
  | snd : HasCases F → Raw F → Raw F
  | inl : HasCases F → Raw F → Raw F
  | inr : HasCases F → Raw F → Raw F
  | case : HasCases F → Raw F → Raw F → Raw F → Raw F
  | roll : HasInductive F → Nat → Raw F → Raw F
  | fold : HasInductive F → Nat → Raw F → Raw F → Raw F
  | observe : HasCoinductive F → Nat → Raw F → Raw F
  | corec : HasCoinductive F → Nat → Raw F → Raw F → Raw F

abbrev STLC := Raw .stlc
abbrev STLCWithLet := Raw .let
abbrev STLCWithCases := Raw .cases
abbrev STLCWithLetCases := Raw .letCases
abbrev InductiveCalculus := Raw .inductive
abbrev CoinductiveCalculus := Raw .coinductive

def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

def rename (ρ : Nat → Nat) : Raw F → Raw F
  | .var i => .var (ρ i)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .lam b => .lam (rename (upRen ρ) b)
  | .letE h x b => .letE h (rename ρ x) (rename (upRen ρ) b)
  | .pair h x y => .pair h (rename ρ x) (rename ρ y)
  | .fst h x => .fst h (rename ρ x)
  | .snd h x => .snd h (rename ρ x)
  | .inl h x => .inl h (rename ρ x)
  | .inr h x => .inr h (rename ρ x)
  | .case h x l r => .case h (rename ρ x) (rename (upRen ρ) l) (rename (upRen ρ) r)
  | .roll h p x => .roll h p (rename ρ x)
  | .fold h p x a => .fold h p (rename ρ x) (rename (upRen ρ) a)
  | .observe h p x => .observe h p (rename ρ x)
  | .corec h p x a => .corec h p (rename ρ x) (rename (upRen ρ) a)

def lift (t : Raw F) : Raw F := rename Nat.succ t

def upSub (σ : Nat → Raw F) : Nat → Raw F
  | 0 => .var 0
  | i + 1 => lift (σ i)

def subst (σ : Nat → Raw F) : Raw F → Raw F
  | .var i => σ i
  | .app f a => .app (subst σ f) (subst σ a)
  | .lam b => .lam (subst (upSub σ) b)
  | .letE h x b => .letE h (subst σ x) (subst (upSub σ) b)
  | .pair h x y => .pair h (subst σ x) (subst σ y)
  | .fst h x => .fst h (subst σ x)
  | .snd h x => .snd h (subst σ x)
  | .inl h x => .inl h (subst σ x)
  | .inr h x => .inr h (subst σ x)
  | .case h x l r => .case h (subst σ x) (subst (upSub σ) l) (subst (upSub σ) r)
  | .roll h p x => .roll h p (subst σ x)
  | .fold h p x a => .fold h p (subst σ x) (subst (upSub σ) a)
  | .observe h p x => .observe h p (subst σ x)
  | .corec h p x a => .corec h p (subst σ x) (subst (upSub σ) a)

/-- The same six enums, intrinsically bounded by the number of available variables. -/
inductive Bounded (F : Fragment) : Nat → Type
  | var : Fin n → Bounded F n
  | app : Bounded F n → Bounded F n → Bounded F n
  | lam : Bounded F (n + 1) → Bounded F n
  | letE : HasLet F → Bounded F n → Bounded F (n + 1) → Bounded F n
  | pair : HasCases F → Bounded F n → Bounded F n → Bounded F n
  | fst : HasCases F → Bounded F n → Bounded F n
  | snd : HasCases F → Bounded F n → Bounded F n
  | inl : HasCases F → Bounded F n → Bounded F n
  | inr : HasCases F → Bounded F n → Bounded F n
  | case : HasCases F → Bounded F n → Bounded F (n + 1) → Bounded F (n + 1) → Bounded F n
  | roll : HasInductive F → Nat → Bounded F n → Bounded F n
  | fold : HasInductive F → Nat → Bounded F n → Bounded F (n + 1) → Bounded F n
  | observe : HasCoinductive F → Nat → Bounded F n → Bounded F n
  | corec : HasCoinductive F → Nat → Bounded F n → Bounded F (n + 1) → Bounded F n

abbrev BoundedSTLC := Bounded .stlc
abbrev BoundedSTLCWithLet := Bounded .let
abbrev BoundedSTLCWithCases := Bounded .cases
abbrev BoundedSTLCWithLetCases := Bounded .letCases
abbrev BoundedInductiveCalculus := Bounded .inductive
abbrev BoundedCoinductiveCalculus := Bounded .coinductive

def Bounded.rename (ρ : Fin n → Fin m) : Bounded F n → Bounded F m
  | .var i => .var (ρ i)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .lam b => .lam (rename (Fin.cases 0 (fun i => Fin.succ (ρ i))) b)
  | .letE h x b => .letE h (rename ρ x) (rename (Fin.cases 0 (fun i => Fin.succ (ρ i))) b)
  | .pair h x y => .pair h (rename ρ x) (rename ρ y)
  | .fst h x => .fst h (rename ρ x)
  | .snd h x => .snd h (rename ρ x)
  | .inl h x => .inl h (rename ρ x)
  | .inr h x => .inr h (rename ρ x)
  | .case h x l r => .case h (rename ρ x)
      (rename (Fin.cases 0 (fun i => Fin.succ (ρ i))) l)
      (rename (Fin.cases 0 (fun i => Fin.succ (ρ i))) r)
  | .roll h p x => .roll h p (rename ρ x)
  | .fold h p x a => .fold h p (rename ρ x) (rename (Fin.cases 0 (fun i => Fin.succ (ρ i))) a)
  | .observe h p x => .observe h p (rename ρ x)
  | .corec h p x a => .corec h p (rename ρ x) (rename (Fin.cases 0 (fun i => Fin.succ (ρ i))) a)

def Bounded.upSub (σ : Fin n → Bounded F m) : Fin (n + 1) → Bounded F (m + 1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

def Bounded.subst (σ : Fin n → Bounded F m) : Bounded F n → Bounded F m
  | .var i => σ i
  | .app f a => .app (subst σ f) (subst σ a)
  | .lam b => .lam (subst (upSub σ) b)
  | .letE h x b => .letE h (subst σ x) (subst (upSub σ) b)
  | .pair h x y => .pair h (subst σ x) (subst σ y)
  | .fst h x => .fst h (subst σ x)
  | .snd h x => .snd h (subst σ x)
  | .inl h x => .inl h (subst σ x)
  | .inr h x => .inr h (subst σ x)
  | .case h x l r => .case h (subst σ x) (subst (upSub σ) l) (subst (upSub σ) r)
  | .roll h p x => .roll h p (subst σ x)
  | .fold h p x a => .fold h p (subst σ x) (subst (upSub σ) a)
  | .observe h p x => .observe h p (subst σ x)
  | .corec h p x a => .corec h p (subst σ x) (subst (upSub σ) a)

def Bounded.erase : Bounded F n → Raw F
  | .var i => .var i
  | .app f a => .app (erase f) (erase a)
  | .lam b => .lam (erase b)
  | .letE h x b => .letE h (erase x) (erase b)
  | .pair h x y => .pair h (erase x) (erase y)
  | .fst h x => .fst h (erase x)
  | .snd h x => .snd h (erase x)
  | .inl h x => .inl h (erase x)
  | .inr h x => .inr h (erase x)
  | .case h x l r => .case h (erase x) (erase l) (erase r)
  | .roll h p x => .roll h p (erase x)
  | .fold h p x a => .fold h p (erase x) (erase a)
  | .observe h p x => .observe h p (erase x)
  | .corec h p x a => .corec h p (erase x) (erase a)

/-- The graph of the evident bounded-to-unbounded translation. -/
inductive Erases : Bounded F n → Raw F → Prop
  | intro (t : Bounded F n) : Erases t t.erase

theorem erases_functional {t : Bounded F n} : Erases t r → r = t.erase := by
  intro h
  cases h
  rfl

end ProjectBeth.Syntax.Language
