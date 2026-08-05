import ProjectBeth.Defs.STLC.Variants
import ProjectBeth.Defs.Untyped.Reduction

universe u

namespace ProjectBeth.STLC.UntypedCompilation

open ProjectBeth.Untyped

/-- A constant reduction algebra whose table is consistent with its simple
types. -/
structure TypedSignature (Ty : Type u) (arr : Ty → Ty → Ty)
    extends Signature where
  constTy : Const → Ty
  apply_typed : ∀ {f x r}, apply f x = some r →
    ∃ A B, constTy f = arr A B ∧ constTy x = A ∧ constTy r = B

inductive At {Ty : Type u} : List Ty → Nat → Ty → Prop
  | here : At (A :: Γ) 0 A
  | there : At Γ i A → At (B :: Γ) (i + 1) A

inductive HasType {Ty : Type u} (arr : Ty → Ty → Ty)
    (S : TypedSignature Ty arr) : List Ty → Tm S.Const → Ty → Prop
  | var : At Γ i A → HasType arr S Γ (.var i) A
  | const : HasType arr S Γ (.const c) (S.constTy c)
  | app : HasType arr S Γ f (arr A B) → HasType arr S Γ x A →
      HasType arr S Γ (.app f x) B
  | lam (body) : HasType arr S (A :: Γ) body B →
      HasType arr S Γ (.lam body) (arr A B)

theorem delta_typed {Ty : Type u} {arr : Ty → Ty → Ty}
    (S : TypedSignature Ty arr) {Γ : List Ty} {f x r} (h : S.apply f x = some r) :
    ∃ A B, HasType arr S Γ (.const f) (arr A B) ∧
      HasType arr S Γ (.const x) A ∧ HasType arr S Γ (.const r) B := by
  rcases S.apply_typed h with ⟨A, B, hf, hx, hr⟩
  refine ⟨A, B, ?_, ?_, ?_⟩
  · simpa [hf] using (HasType.const (arr := arr) (S := S) (Γ := Γ) (c := f))
  · simpa [hx] using (HasType.const (arr := arr) (S := S) (Γ := Γ) (c := x))
  · simpa [hr] using (HasType.const (arr := arr) (S := S) (Γ := Γ) (c := r))

def varIndex : ProjectBeth.STLC.Var Γ A → Nat
  | .here => 0
  | .there x => varIndex x + 1

theorem varIndex_get? (x : ProjectBeth.STLC.Var Γ A) :
    At Γ (varIndex x) A := by
  induction x with
  | here => exact .here
  | there x ih => exact .there ih

/-- Erasure/compilation of intrinsically typed arrow-only STLC into the
untyped constant calculus.  The target signature is irrelevant because this
fragment introduces no constants. -/
def compile {Ty : Type u} {arr : Ty → Ty → Ty} {S : Signature}
    {Γ : List Ty} {A : Ty} : ProjectBeth.STLC.ArrowTm arr Γ A → Tm S.Const
  | .var x => .var (varIndex x)
  | .app f x => .app (compile f) (compile x)
  | .lam body => .lam (compile body)

theorem compile_typed {Ty : Type u} {arr : Ty → Ty → Ty}
    (S : TypedSignature Ty arr) {Γ : List Ty} {A : Ty}
    (t : ProjectBeth.STLC.ArrowTm arr Γ A) :
    HasType arr S Γ (compile (S := S.toSignature) t) A := by
  induction t with
  | var x => exact .var (varIndex_get? x)
  | app f x ihf ihx => exact .app ihf ihx
  | lam body ih => exact .lam _ ih

namespace Church

def pair (a b : Tm C) : Tm C :=
  .lam (.app (.app (.var 0) (a.rename Nat.succ)) (b.rename Nat.succ))
def fst (p : Tm C) : Tm C := .app p (.lam (.lam (.var 1)))
def snd (p : Tm C) : Tm C := .app p (.lam (.lam (.var 0)))
def inl (x : Tm C) : Tm C := .lam (.lam (.app (.var 1) (x.rename (fun i => i + 2))))
def inr (x : Tm C) : Tm C := .lam (.lam (.app (.var 0) (x.rename (fun i => i + 2))))
def case (s l r : Tm C) : Tm C := .app (.app s l) r

end Church

def compileProd {Base : Type u} {S : Signature} {Γ} {A} :
    STLC.ArrowProd.Tm (Base := Base) Γ A → Tm S.Const
  | .var x => .var (varIndex x)
  | .app f x => .app (compileProd f) (compileProd x)
  | .lam body => .lam (compileProd body)
  | .pair a b => Church.pair (compileProd a) (compileProd b)
  | .fst p => Church.fst (compileProd p)
  | .snd p => Church.snd (compileProd p)

def compileSum {Base : Type u} {S : Signature} {Γ} {A} :
    STLC.ArrowProdSum.Tm (Base := Base) Γ A → Tm S.Const
  | .var x => .var (varIndex x)
  | .app f x => .app (compileSum f) (compileSum x)
  | .lam body => .lam (compileSum body)
  | .pair a b => Church.pair (compileSum a) (compileSum b)
  | .fst p => Church.fst (compileSum p)
  | .snd p => Church.snd (compileSum p)
  | .inl x => Church.inl (compileSum x)
  | .inr x => Church.inr (compileSum x)
  | .case s l r => Church.case (compileSum s) (.lam (compileSum l)) (.lam (compileSum r))

end ProjectBeth.STLC.UntypedCompilation
