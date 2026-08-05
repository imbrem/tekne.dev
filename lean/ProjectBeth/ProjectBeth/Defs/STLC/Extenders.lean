/-! Composable syntax extenders and their folds. -/

universe u v w

namespace ProjectBeth.STLC.Ext

abbrev Lang (Ctx : Type u) (Ty : Type v) := Ctx → Ty → Type w

variable {Ctx : Type u} {Ty : Type v}
variable {push : Ty → Ctx → Ctx} {arr : Ty → Ty → Ty}
variable {sum : Ty → Ty → Ty} {Free : Ty → Type w}
variable {U V W : Lang Ctx Ty}

structure Hom {Ctx : Type u} {Ty : Type v}
    (V W : Lang Ctx Ty) where
  app : ∀ {Γ A}, V Γ A → W Γ A

@[ext]
theorem Hom.ext {V W : Lang Ctx Ty} {f g : Hom V W}
    (h : ∀ {Γ A} (x : V Γ A), f.app x = g.app x) : f = g := by
  cases f
  cases g
  congr
  funext Γ A x
  exact h x

def Hom.id (V : Lang Ctx Ty) : Hom V V where
  app x := x

def Hom.comp {U V W : Lang Ctx Ty} (g : Hom V W) (f : Hom U V) : Hom U W where
  app x := g.app (f.app x)

@[simp] theorem Hom.id_comp (f : Hom V W) : Hom.comp (Hom.id W) f = f := by
  ext
  rfl

@[simp] theorem Hom.comp_id (f : Hom V W) : Hom.comp f (Hom.id V) = f := by
  ext
  rfl

theorem Hom.comp_assoc {X : Lang Ctx Ty} (h : Hom W X) (g : Hom V W) (f : Hom U V) :
    Hom.comp (Hom.comp h g) f = Hom.comp h (Hom.comp g f) := by
  ext
  rfl

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

namespace Cases

def map (f : Hom V W) : Hom (Cases push sum V) (Cases push sum W) where
  app := go
  where
    go : ∀ {Γ A}, Cases push sum V Γ A → Cases push sum W Γ A
      | _, _, .inj x => .inj (f.app x)
      | _, _, .inl x => .inl (go x)
      | _, _, .inr x => .inr (go x)
      | _, _, .case x l r => .case (go x) (go l) (go r)

structure Algebra (V : Lang Ctx Ty) (W : Lang Ctx Ty) where
  inj : Hom V W
  inl : ∀ {Γ A B}, W Γ A → W Γ (sum A B)
  inr : ∀ {Γ A B}, W Γ B → W Γ (sum A B)
  case : ∀ {Γ A B C}, W Γ (sum A B) →
    W (push A Γ) C → W (push B Γ) C → W Γ C

def fold (alg : Algebra (push := push) (sum := sum) V W) :
    Hom (Cases push sum V) W where
  app := go
  where
    go : ∀ {Γ A}, Cases push sum V Γ A → W Γ A
      | _, _, .inj x => alg.inj.app x
      | _, _, .inl x => alg.inl (go x)
      | _, _, .inr x => alg.inr (go x)
      | _, _, .case x l r => alg.case (go x) (go l) (go r)

def flatten : Hom (Cases push sum (Cases push sum V)) (Cases push sum V) :=
  fold
    { inj := Hom.id _
      inl := .inl
      inr := .inr
      case := .case }

end Cases

inductive FreeVar {Ctx : Type u} {Ty : Type v}
    (Free : Ty → Type w) (V : Lang Ctx Ty) : Lang Ctx Ty
  | inj : V Γ A → FreeVar Free V Γ A
  | free : Free A → FreeVar Free V Γ A

namespace FreeVar

def map (f : Hom V W) : Hom (FreeVar Free V) (FreeVar Free W) where
  app
    | .inj x => .inj (f.app x)
    | .free x => .free x

structure Algebra (Free : Ty → Type w) (V : Lang Ctx Ty) (W : Lang Ctx Ty) where
  inj : Hom V W
  free : ∀ {Γ A}, Free A → W Γ A

def fold (alg : Algebra Free V W) : Hom (FreeVar Free V) W where
  app
    | .inj x => alg.inj.app x
    | .free x => alg.free x

def flatten : Hom (FreeVar Free (FreeVar Free V)) (FreeVar Free V) :=
  fold
    { inj := Hom.id _
      free := .free }

end FreeVar

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

theorem SemEquiv.refl {V : Lang Ctx Ty} {El : Ctx → Ty → Type w}
    (sem : Semantics V El) : SemEquiv (Hom.id V) sem sem :=
  ⟨fun _ => rfl⟩

theorem SemEquiv.comp {X : Lang Ctx Ty} {f : Hom U V} {g : Hom V X}
    {El : Ctx → Ty → Type w} {USem : Semantics U El}
    {VSem : Semantics V El} {XSem : Semantics X El}
    (hg : SemEquiv g VSem XSem) (hf : SemEquiv f USem VSem) :
    SemEquiv (Hom.comp g f) USem XSem :=
  ⟨fun x => (hg.commutes (f.app x)).trans (hf.commutes x)⟩

end ProjectBeth.STLC.Ext
