universe u v

namespace ProjectBeth.STLC

inductive Var {Ty : Type u} : List Ty → Ty → Type u
  | here : Var (A :: Γ) A
  | there : Var Γ A → Var (B :: Γ) A

def Env {Ty : Type u} (El : Ty → Type v) : List Ty → Type (max u v)
  | [] => PUnit
  | A :: Γ => El A × Env El Γ

def Var.lookup {Ty : Type u} {El : Ty → Type v} {Γ : List Ty} {A : Ty} :
    Var Γ A → Env El Γ → El A
  | .here, env => env.1
  | .there v, env => v.lookup env.2

inductive ArrowTm {Ty : Type u} (arr : Ty → Ty → Ty) : List Ty → Ty → Type u
  | var : Var Γ A → ArrowTm arr Γ A
  | app : ArrowTm arr Γ (arr A B) → ArrowTm arr Γ A → ArrowTm arr Γ B
  | lam : ArrowTm arr (A :: Γ) B → ArrowTm arr Γ (arr A B)

end ProjectBeth.STLC
