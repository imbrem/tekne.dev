import ProjectBeth.Defs.SystemF.Inductive
import ProjectBeth.Defs.SystemF.PER

universe u v

namespace ProjectBeth.SystemF.Inductive.Semantics

open ProjectBeth.SystemF

variable (U : Universe)

def extend (X : U.Code) (ρ : Nat → U.Code) : Nat → U.Code
  | 0 => X
  | n + 1 => ρ n

def Ty.code (ρ : Nat → U.Code) : Inductive.Ty → U.Code
  | .var i => ρ i
  | .bool => U.bool
  | .nat => U.nat
  | .arr A B => U.arr (Ty.code ρ A) (Ty.code ρ B)
  | .all A => U.all (fun X => Ty.code (extend U X ρ) A)

theorem Ty.code_rename (ρ : Nat → Nat) (η : Nat → U.Code) (A : Inductive.Ty) :
    Ty.code U η (A.rename ρ) = Ty.code U (η ∘ ρ) A := by
  induction A generalizing ρ η with
  | var i => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.code, Inductive.Ty.rename, ihA, ihB]
  | all A ih =>
    simp only [Inductive.Ty.rename, Ty.code, ih]
    congr 2
    funext X
    apply congrArg (fun e => Ty.code U e A)
    funext i
    cases i <;> rfl

theorem Ty.code_lift (ρ : Nat → U.Code) (X : U.Code) (A : Inductive.Ty) :
    Ty.code U (extend U X ρ) A.lift = Ty.code U ρ A := by
  rw [Inductive.Ty.lift, Ty.code_rename]
  rfl

theorem Ty.code_subst (σ : Nat → Inductive.Ty) (η : Nat → U.Code)
    (A : Inductive.Ty) :
    Ty.code U η (A.subst σ) = Ty.code U (fun i => Ty.code U η (σ i)) A := by
  induction A generalizing σ η with
  | var i => rfl
  | bool => rfl
  | nat => rfl
  | arr A B ihA ihB => simp [Ty.code, Inductive.Ty.subst, ihA, ihB]
  | all A ih =>
    simp only [Inductive.Ty.subst, Ty.code, ih]
    congr 2
    funext X
    apply congrArg (fun e => Ty.code U e A)
    funext i
    cases i with
    | zero => rfl
    | succ i => exact Ty.code_lift U η X (σ i)

theorem Ty.code_instantiate (η : Nat → U.Code) (A X : Inductive.Ty) :
    Ty.code U η (A.instantiate X) =
      Ty.code U (extend U (Ty.code U η X) η) A := by
  rw [Inductive.Ty.instantiate, Ty.code_subst]
  congr 1
  funext i
  cases i <;> rfl

def Env (ρ : Nat → U.Code) : List Inductive.Ty → Type u
  | [] => PUnit
  | A :: Γ => U.El (Ty.code U ρ A) × Env ρ Γ

def Env.mapLift (ρ : Nat → U.Code) (X : U.Code) :
    (Γ : List Inductive.Ty) → Env U ρ Γ →
      Env U (extend U X ρ) (Γ.map Inductive.Ty.lift)
  | [], _ => PUnit.unit
  | A :: Γ, γ =>
      (cast (congrArg U.El (Ty.code_lift U ρ X A).symm) γ.1,
        Env.mapLift ρ X Γ γ.2)

def lookup {Γ : List Inductive.Ty} {n : Nat} {A : Inductive.Ty} (h : Γ[n]? = some A)
    (ρ : Nat → U.Code) : Env U ρ Γ → U.El (Ty.code U ρ A) := by
  induction Γ generalizing n A with
  | nil => simp at h
  | cons B Γ ih =>
    cases n with
    | zero =>
      simp at h
      subst A
      exact fun γ => γ.1
    | succ n =>
      simp at h
      exact fun γ => ih h γ.2

inductive Derivation : Nat → List Inductive.Ty → Inductive.Tm → Inductive.Ty → Type
  | var (h : Γ[n]? = some A) : Derivation Δ Γ (.var n) A
  | app : Derivation Δ Γ f (.arr A B) → Derivation Δ Γ x A →
      Derivation Δ Γ (.app f x) B
  | lam : Derivation Δ (A :: Γ) t B → Derivation Δ Γ (.lam A t) (.arr A B)
  | tyApp : Derivation Δ Γ f (.all A) →
      Derivation Δ Γ (.tyApp f X) (A.instantiate X)
  | tyLam : Derivation (Δ + 1) (Γ.map Inductive.Ty.lift) t A →
      Derivation Δ Γ (.tyLam t) (.all A)
  | bool (b : Bool) : Derivation Δ Γ (.bool b) .bool
  | nat (n : Nat) : Derivation Δ Γ (.nat n) .nat

def Derivation.toHasType : Derivation Δ Γ t A → Inductive.HasType Δ Γ t A
  | .var h => .var h
  | .app f x => .app f.toHasType x.toHasType
  | .lam t => .lam t.toHasType
  | .tyApp f => .tyApp f.toHasType
  | .tyLam t => .tyLam t.toHasType
  | .bool b => .bool
  | .nat n => .nat

structure SemanticTyped (Δ : Nat) (Γ : List Inductive.Ty) (A : Inductive.Ty) where
  term : Inductive.Tm
  derivation : Derivation Δ Γ term A

def denote : Derivation Δ Γ t A →
    (ρ : Nat → U.Code) → Env U ρ Γ → U.El (Ty.code U ρ A)
  | .var h, ρ, γ => lookup U h ρ γ
  | .app hf hx, ρ, γ => U.arrEquiv _ _ (denote hf ρ γ) (denote hx ρ γ)
  | .lam h, ρ, γ => (U.arrEquiv _ _).symm (fun x => denote h ρ (x, γ))
  | .tyApp hf, ρ, γ =>
      cast (congrArg U.El (Ty.code_instantiate U ρ _ _).symm)
        (U.allEquiv _ (denote hf ρ γ) (Ty.code U ρ _))
  | .tyLam h, ρ, γ => (U.allEquiv _).symm
      (fun X => denote h (extend U X ρ) (Env.mapLift U ρ X _ γ))
  | .bool b, _, _ => U.boolEquiv.symm b
  | .nat n, _, _ => U.natEquiv.symm n

@[simp] theorem denote_beta (body : Derivation Δ (A :: Γ) t B)
    (x : Derivation Δ Γ s A) (ρ γ) :
    denote U (.app (.lam body) x) ρ γ =
      denote U body ρ (denote U x ρ γ, γ) := by
  simp [denote]

@[simp] theorem denote_tyBeta
    (body : Derivation (Δ + 1) (Γ.map Inductive.Ty.lift) t A)
    (X : Inductive.Ty) (ρ γ) :
    denote U (.tyApp (X := X) (.tyLam body)) ρ γ =
      cast (congrArg U.El (Ty.code_instantiate U ρ A X).symm)
        (denote U body (extend U (Ty.code U ρ X) ρ)
          (Env.mapLift U ρ (Ty.code U ρ X) Γ γ)) := by
  simp [denote]

structure LogicalPERModel (D : Type v) extends ProjectBeth.SystemF.PERModel U D where
  quote_cast : ∀ {A B : U.Code} (h : A = B) (x : U.El A),
    quote B (cast (congrArg U.El h) x) = quote A x
  app_rel : ∀ A B (f g : U.El (U.arr A B)) (x y : U.El A),
    (interp (U.arr A B)).Rel (quote _ f) (quote _ g) →
    (interp A).Rel (quote _ x) (quote _ y) →
    (interp B).Rel (quote _ (U.arrEquiv A B f x))
      (quote _ (U.arrEquiv A B g y))
  lam_rel : ∀ A B (f g : U.El A → U.El B),
    (∀ x y, (interp A).Rel (quote _ x) (quote _ y) →
      (interp B).Rel (quote _ (f x)) (quote _ (g y))) →
    (interp (U.arr A B)).Rel (quote _ ((U.arrEquiv A B).symm f))
      (quote _ ((U.arrEquiv A B).symm g))
  all_elim : ∀ F (f g : U.El (U.all F)) X,
    (interp (U.all F)).Rel (quote _ f) (quote _ g) →
    (interp (F X)).Rel (quote _ (U.allEquiv F f X))
      (quote _ (U.allEquiv F g X))
  all_rel : ∀ F (f g : (X : U.Code) → U.El (F X)),
    (∀ X, (interp (F X)).Rel (quote _ (f X)) (quote _ (g X))) →
    (interp (U.all F)).Rel (quote _ ((U.allEquiv F).symm f))
      (quote _ ((U.allEquiv F).symm g))

def EnvRel (M : LogicalPERModel U D) (ρ : Nat → U.Code) :
    (Γ : List Inductive.Ty) → Env U ρ Γ → Env U ρ Γ → Prop
  | [], _, _ => True
  | A :: Γ, γ, δ =>
      (M.interp (Ty.code U ρ A)).Rel (M.quote _ γ.1) (M.quote _ δ.1) ∧
      EnvRel M ρ Γ γ.2 δ.2

theorem EnvRel.lookup (M : LogicalPERModel U D) (h : Γ[n]? = some A)
    {γ δ : Env U ρ Γ} (hγδ : EnvRel U M ρ Γ γ δ) :
    (M.interp (Ty.code U ρ A)).Rel
      (M.quote _ (lookup U h ρ γ)) (M.quote _ (lookup U h ρ δ)) := by
  induction Γ generalizing n A with
  | nil => simp at h
  | cons B Γ ih =>
    cases n with
    | zero => simp at h; subst A; exact hγδ.1
    | succ n => simp at h; exact ih h hγδ.2

theorem EnvRel.mapLift (M : LogicalPERModel U D) {γ δ : Env U ρ Γ}
    (h : EnvRel U M ρ Γ γ δ) (X : U.Code) :
    EnvRel U M (extend U X ρ) (Γ.map Inductive.Ty.lift)
      (Env.mapLift U ρ X Γ γ) (Env.mapLift U ρ X Γ δ) := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih =>
    constructor
    · simp only [Env.mapLift, EnvRel]
      rw [M.quote_cast, M.quote_cast, Ty.code_lift]
      exact h.1
      all_goals exact (Ty.code_lift U ρ X A).symm
    · exact ih h.2

theorem fundamental (M : LogicalPERModel U D) (d : Derivation Δ Γ t A) :
    ∀ ρ γ δ, EnvRel U M ρ Γ γ δ →
      (M.interp (Ty.code U ρ A)).Rel
        (M.quote _ (denote U d ρ γ)) (M.quote _ (denote U d ρ δ)) := by
  induction d with
  | var h => intro ρ γ δ hγδ; exact hγδ.lookup U M h
  | app f x ihf ihx =>
    intro ρ γ δ hγδ
    exact M.app_rel _ _ _ _ _ _ (ihf ρ γ δ hγδ) (ihx ρ γ δ hγδ)
  | lam body ih =>
    intro ρ γ δ hγδ
    apply M.lam_rel
    intro x y hxy
    exact ih ρ (x, γ) (y, δ) ⟨hxy, hγδ⟩
  | tyApp f ih =>
    intro ρ γ δ hγδ
    simp only [denote]
    rw [M.quote_cast, M.quote_cast, Ty.code_instantiate]
    exact M.all_elim _ _ _ (Ty.code U ρ _) (ih ρ γ δ hγδ)
    all_goals exact (Ty.code_instantiate U ρ _ _).symm
  | tyLam body ih =>
    intro ρ γ δ hγδ
    apply M.all_rel
    intro X
    exact ih (extend U X ρ) _ _ (hγδ.mapLift U M X)
  | bool b => intro ρ γ δ hγδ; exact M.quote_rel _ _
  | nat n => intro ρ γ δ hγδ; exact M.quote_rel _ _

theorem fundamental_quote (M : ProjectBeth.SystemF.PERModel U D)
    (d : Derivation Δ Γ t A) (ρ γ) :
    (M.interp (Ty.code U ρ A)).Rel
      (M.quote _ (denote U d ρ γ)) (M.quote _ (denote U d ρ γ)) :=
  M.quote_rel _ _

end ProjectBeth.SystemF.Inductive.Semantics
