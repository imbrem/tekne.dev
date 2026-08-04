universe u v w

namespace ProjectBeth.STLC.Ext

abbrev Lang (Ctx : Type u) (Ty : Type v) := Ctx → Ty → Type w

variable {Ctx : Type u} {Ty : Type v}
variable {push : Ty → Ctx → Ctx} {arr : Ty → Ty → Ty}
variable {U V W : Lang Ctx Ty}

structure Hom {Ctx : Type u} {Ty : Type v}
    (V W : Lang Ctx Ty) where
  app : ∀ {Γ A}, V Γ A → W Γ A

def Hom.id (V : Lang Ctx Ty) : Hom V V where
  app x := x

def Hom.comp {U V W : Lang Ctx Ty} (g : Hom V W) (f : Hom U V) : Hom U W where
  app x := g.app (f.app x)

inductive Lam {Ctx : Type u} {Ty : Type v}
    (push : Ty → Ctx → Ctx) (arr : Ty → Ty → Ty)
    (V : Lang Ctx Ty) : Lang Ctx Ty
  | inj : V Γ A → Lam push arr V Γ A
  | app : Lam push arr V Γ (arr A B) → Lam push arr V Γ A → Lam push arr V Γ B
  | lam : Lam push arr V (push A Γ) B → Lam push arr V Γ (arr A B)

namespace Lam

def map (f : Hom V W) : Hom (Lam push arr V) (Lam push arr W) where
  app := go
  where
    go : ∀ {Γ A}, Lam push arr V Γ A → Lam push arr W Γ A
      | _, _, .inj x => .inj (f.app x)
      | _, _, .app g x => .app (go g) (go x)
      | _, _, .lam t => .lam (go t)

structure Algebra (V : Lang Ctx Ty) (W : Lang Ctx Ty) where
  inj : Hom V W
  app : ∀ {Γ A B}, W Γ (arr A B) → W Γ A → W Γ B
  lam : ∀ {Γ A B}, W (push A Γ) B → W Γ (arr A B)

def fold (alg : Algebra (push := push) (arr := arr) V W) : Hom (Lam push arr V) W where
  app := go
  where
    go : ∀ {Γ A}, Lam push arr V Γ A → W Γ A
      | _, _, .inj x => alg.inj.app x
      | _, _, .app g x => alg.app (go g) (go x)
      | _, _, .lam t => alg.lam (go t)

def flatten : Hom (Lam push arr (Lam push arr V)) (Lam push arr V) :=
  fold
    { inj := Hom.id _
      app := .app
      lam := .lam }

end Lam

inductive Let {Ctx : Type u} {Ty : Type v}
    (push : Ty → Ctx → Ctx) (V : Lang Ctx Ty) : Lang Ctx Ty
  | inj : V Γ A → Let push V Γ A
  | letE : Let push V Γ A → Let push V (push A Γ) B → Let push V Γ B

namespace Let

def map (f : Hom V W) : Hom (Let push V) (Let push W) where
  app := go
  where
    go : ∀ {Γ A}, Let push V Γ A → Let push W Γ A
      | _, _, .inj x => .inj (f.app x)
      | _, _, .letE x t => .letE (go x) (go t)

structure Algebra (V : Lang Ctx Ty) (W : Lang Ctx Ty) where
  inj : Hom V W
  letE : ∀ {Γ A B}, W Γ A → W (push A Γ) B → W Γ B

def fold (alg : Algebra (push := push) V W) : Hom (Let push V) W where
  app := go
  where
    go : ∀ {Γ A}, Let push V Γ A → W Γ A
      | _, _, .inj x => alg.inj.app x
      | _, _, .letE x t => alg.letE (go x) (go t)

def flatten : Hom (Let push (Let push V)) (Let push V) :=
  fold
    { inj := Hom.id _
      letE := .letE }

def intoLam : Hom (Let push (Lam push arr V)) (Lam push arr V) :=
  fold
    { inj := Hom.id _
      letE := fun x t => .app (.lam t) x }

end Let

inductive Cases {Ctx : Type u} {Ty : Type v}
    (push : Ty → Ctx → Ctx) (sum : Ty → Ty → Ty)
    (V : Lang Ctx Ty) : Lang Ctx Ty
  | inj : V Γ A → Cases push sum V Γ A
  | inl : Cases push sum V Γ A → Cases push sum V Γ (sum A B)
  | inr : Cases push sum V Γ B → Cases push sum V Γ (sum A B)
  | case : Cases push sum V Γ (sum A B) →
      Cases push sum V (push A Γ) C → Cases push sum V (push B Γ) C →
      Cases push sum V Γ C

inductive FreeVar {Ctx : Type u} {Ty : Type v}
    (Free : Ty → Type w) (V : Lang Ctx Ty) : Lang Ctx Ty
  | inj : V Γ A → FreeVar Free V Γ A
  | free : Free A → FreeVar Free V Γ A

inductive LetLam {Ctx : Type u} {Ty : Type v}
    (push : Ty → Ctx → Ctx) (arr : Ty → Ty → Ty)
    (V : Lang Ctx Ty) : Lang Ctx Ty
  | inj : V Γ A → LetLam push arr V Γ A
  | app : LetLam push arr V Γ (arr A B) → LetLam push arr V Γ A →
      LetLam push arr V Γ B
  | lam : LetLam push arr V (push A Γ) B → LetLam push arr V Γ (arr A B)
  | letE : LetLam push arr V Γ A → LetLam push arr V (push A Γ) B →
      LetLam push arr V Γ B

namespace LetLam

def fromLam : Hom (Lam push arr V) (LetLam push arr V) :=
  Lam.fold
    { inj := { app := .inj }
      app := .app
      lam := .lam }

def fromLet : Hom (Let push V) (LetLam push arr V) :=
  Let.fold
    { inj := { app := .inj }
      letE := .letE }

def fromLamLet : Hom (Lam push arr (Let push V)) (LetLam push arr V) :=
  Lam.fold
    { inj := fromLet
      app := .app
      lam := .lam }

def fromLetLam : Hom (Let push (Lam push arr V)) (LetLam push arr V) :=
  Let.fold
    { inj := fromLam
      letE := .letE }

end LetLam

structure Semantics {Ctx : Type u} {Ty : Type v}
    (V : Lang Ctx Ty) (El : Ctx → Ty → Type w) where
  denote : ∀ {Γ A}, V Γ A → El Γ A

structure SemEquiv {Ctx : Type u} {Ty : Type v}
    {V W : Lang Ctx Ty} (f : Hom V W)
    {El : Ctx → Ty → Type w}
    (VSem : Semantics V El) (WSem : Semantics W El) : Prop where
  commutes : ∀ {Γ A} (x : V Γ A), WSem.denote (f.app x) = VSem.denote x

end ProjectBeth.STLC.Ext
