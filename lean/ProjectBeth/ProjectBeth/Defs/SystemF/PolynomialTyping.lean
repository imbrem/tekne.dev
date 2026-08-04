import ProjectBeth.Defs.SystemF.Polynomial
import ProjectBeth.Defs.SystemF.ContextMorphisms

namespace ProjectBeth.SystemF.Polynomial.Syntax.Typing

open ProjectBeth.SystemF.Inductive
open ProjectBeth.SystemF.Inductive.Semantics

def liftTy (d : Derivation Δ Γ t A) :
    Derivation (Δ + 1) (Γ.map Ty.lift) (t.renameTy Nat.succ) A.lift :=
  ((d.renameTy Nat.succ).changeDepth (Δ' := Δ + 1)).castCtx
    (by simp [Ty.lift]) rfl (by rfl)

def sumInl (d : Derivation Δ Γ a A) :
    Derivation Δ Γ (Syntax.sumInl A B a) (Syntax.sumTy A B) := by
  apply Derivation.tyLam
  apply Derivation.lam
  apply Derivation.lam
  apply Derivation.app
  · exact Derivation.var (n := 1) (A := .arr A.lift (.var 0)) (by simp)
  · exact (((liftTy d).renameTm
      (CtxRen.weaken _ (.arr A.lift (.var 0)))).renameTm
        (CtxRen.weaken _ (.arr B.lift (.var 0))))

def sumInr (d : Derivation Δ Γ b B) :
    Derivation Δ Γ (Syntax.sumInr A B b) (Syntax.sumTy A B) := by
  apply Derivation.tyLam
  apply Derivation.lam
  apply Derivation.lam
  apply Derivation.app
  · exact Derivation.var (n := 0) (A := .arr B.lift (.var 0)) (by simp)
  · exact (((liftTy d).renameTm
      (CtxRen.weaken _ (.arr A.lift (.var 0)))).renameTm
        (CtxRen.weaken _ (.arr B.lift (.var 0))))

def prodPair (da : Derivation Δ Γ a A) (db : Derivation Δ Γ b B) :
    Derivation Δ Γ (Syntax.prodPair A B a b) (Syntax.prodTy A B) := by
  apply Derivation.tyLam
  apply Derivation.lam
  apply Derivation.app
  · apply Derivation.app
    · exact Derivation.var (n := 0)
        (A := .arr A.lift (.arr B.lift (.var 0))) (by simp)
    · exact (liftTy da).renameTm (CtxRen.weaken _ _)
  · exact (liftTy db).renameTm (CtxRen.weaken _ _)

end ProjectBeth.SystemF.Polynomial.Syntax.Typing
