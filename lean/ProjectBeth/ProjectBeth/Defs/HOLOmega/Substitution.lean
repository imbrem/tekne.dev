import ProjectBeth.Defs.HOLOmega.Syntax

universe u

namespace ProjectBeth.HOLOmega

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

mutual
  def Ty.rename {Base : Type u} (ρ : Nat → Nat) : Ty Base → Ty Base
    | .base A => .base A
    | .var n => .var (ρ n)
    | .lam K A => .lam K (A.rename (liftRen ρ))
    | .app F A => .app (F.rename ρ) (A.rename ρ)
    | .bool => .bool
    | .arr A B => .arr (A.rename ρ) (B.rename ρ)
    | .sub A p => .sub (A.rename ρ) (p.renameTy ρ)

  def Tm.renameTy {Base : Type u} (ρ : Nat → Nat) : Tm Base → Tm Base
    | .var n => .var n
    | .app f x => .app (f.renameTy ρ) (x.renameTy ρ)
    | .lam A t => .lam (A.rename ρ) (t.renameTy ρ)
    | .tyApp f A => .tyApp (f.renameTy ρ) (A.rename ρ)
    | .tyLam K t => .tyLam K (t.renameTy (liftRen ρ))
    | .bool b => .bool b
    | .eq A x y => .eq (A.rename ρ) (x.renameTy ρ) (y.renameTy ρ)
    | .epsilon A p => .epsilon (A.rename ρ) (p.renameTy ρ)
    | .abs A p x => .abs (A.rename ρ) (p.renameTy ρ) (x.renameTy ρ)
    | .rep A p x => .rep (A.rename ρ) (p.renameTy ρ) (x.renameTy ρ)
end

def liftSub {Base : Type u} (σ : Nat → Ty Base) : Nat → Ty Base
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

mutual
  def Ty.subst {Base : Type u} (σ : Nat → Ty Base) : Ty Base → Ty Base
    | .base A => .base A
    | .var n => σ n
    | .lam K A => .lam K (A.subst (liftSub σ))
    | .app F A => .app (F.subst σ) (A.subst σ)
    | .bool => .bool
    | .arr A B => .arr (A.subst σ) (B.subst σ)
    | .sub A p => .sub (A.subst σ) (p.substTy σ)

  def Tm.substTy {Base : Type u} (σ : Nat → Ty Base) : Tm Base → Tm Base
    | .var n => .var n
    | .app f x => .app (f.substTy σ) (x.substTy σ)
    | .lam A t => .lam (A.subst σ) (t.substTy σ)
    | .tyApp f A => .tyApp (f.substTy σ) (A.subst σ)
    | .tyLam K t => .tyLam K (t.substTy (liftSub σ))
    | .bool b => .bool b
    | .eq A x y => .eq (A.subst σ) (x.substTy σ) (y.substTy σ)
    | .epsilon A p => .epsilon (A.subst σ) (p.substTy σ)
    | .abs A p x => .abs (A.subst σ) (p.substTy σ) (x.substTy σ)
    | .rep A p x => .rep (A.subst σ) (p.substTy σ) (x.substTy σ)
end

def liftTmRen (ρ : Nat → Nat) : Nat → Nat := liftRen ρ

def Tm.rename {Base : Type u} (ρ : Nat → Nat) : Tm Base → Tm Base
  | .var n => .var (ρ n)
  | .app f x => .app (f.rename ρ) (x.rename ρ)
  | .lam A t => .lam A (t.rename (liftTmRen ρ))
  | .tyApp f A => .tyApp (f.rename ρ) A
  | .tyLam K t => .tyLam K (t.rename ρ)
  | .bool b => .bool b
  | .eq A x y => .eq A (x.rename ρ) (y.rename ρ)
  | .epsilon A p => .epsilon A (p.rename ρ)
  | .abs A p x => .abs A p (x.rename ρ)
  | .rep A p x => .rep A p (x.rename ρ)

def liftTmSub {Base : Type u} (σ : Nat → Tm Base) : Nat → Tm Base
  | 0 => .var 0
  | n + 1 => (σ n).rename Nat.succ

def Tm.subst {Base : Type u} (σ : Nat → Tm Base) : Tm Base → Tm Base
  | .var n => σ n
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .lam A t => .lam A (t.subst (liftTmSub σ))
  | .tyApp f A => .tyApp (f.subst σ) A
  | .tyLam K t => .tyLam K (t.subst σ)
  | .bool b => .bool b
  | .eq A x y => .eq A (x.subst σ) (y.subst σ)
  | .epsilon A p => .epsilon A (p.subst σ)
  | .abs A p x => .abs A p (x.subst σ)
  | .rep A p x => .rep A p (x.subst σ)

@[simp] theorem Ty.rename_var {Base : Type u} (ρ : Nat → Nat) (n : Nat) :
    (Ty.var n : Ty Base).rename ρ = .var (ρ n) := rfl

@[simp] theorem Ty.subst_var {Base : Type u} (σ : Nat → Ty Base) (n : Nat) :
    (Ty.var n : Ty Base).subst σ = σ n := rfl

@[simp] theorem Tm.rename_var {Base : Type u} (ρ : Nat → Nat) (n : Nat) :
    (Tm.var n : Tm Base).rename ρ = .var (ρ n) := rfl

@[simp] theorem Tm.subst_var {Base : Type u} (σ : Nat → Tm Base) (n : Nat) :
    (Tm.var n : Tm Base).subst σ = σ n := rfl

def Ty.instantiate {Base : Type u} (A X : Ty Base) : Ty Base :=
  A.subst (fun | 0 => X | n + 1 => .var n)

def Tm.instantiateTy {Base : Type u} (t : Tm Base) (X : Ty Base) : Tm Base :=
  t.substTy (fun | 0 => X | n + 1 => .var n)

def Tm.instantiate {Base : Type u} (t x : Tm Base) : Tm Base :=
  t.subst (fun | 0 => x | n + 1 => .var n)

end ProjectBeth.HOLOmega
