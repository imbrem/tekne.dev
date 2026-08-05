import ProjectBeth.Defs.STLC.Syntax.SimpleType
import ProjectBeth.Defs.SystemF.Inductive

namespace ProjectBeth.SystemF.Syntax

namespace Generic

inductive Op
  | var (n : Nat) | bool | nat | arr | all
  deriving DecidableEq

abbrev arity : Op → Nat
  | .var _ | .bool | .nat => 0
  | .all => 1
  | .arr => 2

abbrev signature : STLC.Syntax.Signature := ⟨Op, arity⟩
abbrev Ty := STLC.Syntax.TypeExpr signature PEmpty

end Generic

abbrev Ty := Inductive.Ty

private def one (A : Generic.Ty) : Fin 1 → Generic.Ty := fun _ => A
private def two (A B : Generic.Ty) : Fin 2 → Generic.Ty :=
  Fin.cases A (Fin.cases B Fin.elim0)

@[simp] private theorem two_zero (A B : Generic.Ty) : two A B 0 = A := rfl
@[simp] private theorem two_one (A B : Generic.Ty) : two A B 1 = B := rfl
private theorem two_eta (xs : Fin 2 → Generic.Ty) : two (xs 0) (xs 1) = xs := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

def toGeneric : Ty → Generic.Ty
  | .var n => .op (.var n) Fin.elim0
  | .bool => .op .bool Fin.elim0
  | .nat => .op .nat Fin.elim0
  | .arr A B => .op .arr (two (toGeneric A) (toGeneric B))
  | .all A => .op .all (one (toGeneric A))

def fromGeneric : Generic.Ty → Ty
  | .base x => nomatch x
  | .op (.var n) _ => .var n
  | .op .bool _ => .bool
  | .op .nat _ => .nat
  | .op .arr xs => .arr (fromGeneric (xs 0)) (fromGeneric (xs 1))
  | .op .all xs => .all (fromGeneric (xs 0))

@[simp] theorem fromGeneric_toGeneric (A : Ty) : fromGeneric (toGeneric A) = A := by
  induction A <;> simp [toGeneric, fromGeneric, one, two_zero, two_one, *]

@[simp] theorem toGeneric_fromGeneric (A : Generic.Ty) :
    toGeneric (fromGeneric A) = A := by
  induction A with
  | base x => exact PEmpty.elim x
  | op f xs ih =>
    cases f <;> simp only [fromGeneric, toGeneric] <;> congr
    · funext i; exact Fin.elim0 i
    · funext i; exact Fin.elim0 i
    · funext i; exact Fin.elim0 i
    · rw [ih 0, ih 1]; exact two_eta xs
    · funext i; fin_cases i; exact ih 0

def genericEquiv : Ty ≃ Generic.Ty where
  toFun := toGeneric
  invFun := fromGeneric
  left_inv := fromGeneric_toGeneric
  right_inv := toGeneric_fromGeneric

namespace Generic

def rename (ρ : Nat → Nat) (A : Ty) : Ty :=
  toGeneric (Inductive.Ty.rename ρ (fromGeneric A))

def subst (σ : Nat → Inductive.Ty) (A : Ty) : Ty :=
  toGeneric (Inductive.Ty.subst σ (fromGeneric A))

def fold (var : Nat → X) (bool nat : X) (arr : X → X → X) (all : X → X)
    : Ty → X
  | .base x => nomatch x
  | .op (.var n) _ => var n
  | .op .bool _ => bool
  | .op .nat _ => nat
  | .op .arr xs => arr (fold var bool nat arr all (xs 0))
      (fold var bool nat arr all (xs 1))
  | .op .all xs => all (fold var bool nat arr all (xs 0))

end Generic

@[simp] theorem toGeneric_rename (ρ : Nat → Nat) (A : Ty) :
    toGeneric (A.rename ρ) = Generic.rename ρ (toGeneric A) := by
  simp [Generic.rename]

@[simp] theorem toGeneric_subst (σ : Nat → Ty) (A : Ty) :
    toGeneric (A.subst σ) = Generic.subst σ (toGeneric A) := by
  simp [Generic.subst]

def concreteFold (var : Nat → X) (bool nat : X) (arr : X → X → X) (all : X → X) :
    Ty → X
  | .var n => var n
  | .bool => bool
  | .nat => nat
  | .arr A B => arr (concreteFold var bool nat arr all A) (concreteFold var bool nat arr all B)
  | .all A => all (concreteFold var bool nat arr all A)

@[simp] theorem generic_fold_square (var : Nat → X) (bool nat : X)
    (arr : X → X → X) (all : X → X) (A : Ty) :
    Generic.fold var bool nat arr all (toGeneric A) = concreteFold var bool nat arr all A := by
  induction A with
  | var => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB =>
    change arr (Generic.fold var bool nat arr all (toGeneric A))
      (Generic.fold var bool nat arr all (toGeneric B)) = _
    rw [ihA, ihB]
    rfl
  | all A ih =>
    change all (Generic.fold var bool nat arr all (toGeneric A)) = _
    rw [ih]
    rfl

end ProjectBeth.SystemF.Syntax
