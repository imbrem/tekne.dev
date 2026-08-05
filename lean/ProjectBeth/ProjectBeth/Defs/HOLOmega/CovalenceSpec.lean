import ProjectBeth.Defs.HOLOmega.Kernel
import ProjectBeth.Defs.HOLOmega.Soundness

/-!
# A small tree specification of HOLω

This module is the executable kernel-facing specification intended for
Covalence.  `Kind`, `Ty`, and `Tm` are the content-addressed raw trees.  A
`Certificate` is another tree: each constructor checks only its immediate
children and the indicated context lookup.  There is consequently no global
well-formedness pass hidden in this interface.

The raw formation and typing rules erase exactly to the established HOLω
judgements, whose soundness is inherited for every `SoundModel`.  The logical
rules are exposed separately because they require the stronger standard
Tarskian universe used by the HOLω kernel; their single soundness theorem
covers every equality, choice, and subtype rule.
-/

universe u v

namespace ProjectBeth.HOLOmega.CovalenceSpec

variable {Base : Type u} {Ω : Type v}

abbrev Kind := HOLOmega.Kind
abbrev Ty (Base : Type u) := HOLOmega.Ty Base
abbrev Tm (Base : Type u) := HOLOmega.Tm Base

abbrev KindCtx := List Kind
abbrev TermCtx (Base : Type u) := List (Ty Base)
abbrev Assumptions (Base : Type u) := List (Tm Base)

/-- The two forms of locally checkable goal. -/
abbrev Goal (Base : Type u) := HOLOmega.JudgementIndex Base

/-- A content-addressable derivation tree.  Its constructors are the complete
formation and typing rules for the raw language. -/
abbrev Certificate {Base : Type u} := @HOLOmega.Judgement Base

namespace Rules

-- Kinds are the freely generated simple kinds `*` and `K ⇒ L`.
abbrev star : Kind := .star
abbrev kindArrow (K L : Kind) : Kind := .arr K L

-- Type formation.
theorem base {Base : Type u} (A : Base) :
    Certificate (.kinded Δ (.base A) .star) := .kBase

theorem tyVar (h : Δ[n]? = some K) :
    Certificate (Base := Base) (.kinded Δ (.var n) K) := .kVar h

theorem tyLam (body : Certificate (Base := Base) (.kinded (K :: Δ) A L)) :
    Certificate (.kinded Δ (.lam K A) (.arr K L)) := .kLam body

theorem tyApp (fn : Certificate (Base := Base) (.kinded Δ F (.arr K L)))
    (arg : Certificate (.kinded Δ A K)) :
    Certificate (.kinded Δ (.app F A) L) := .kApp fn arg

theorem boolTy : Certificate (Base := Base) (.kinded Δ .bool .star) := .kBool

theorem arrowTy (left : Certificate (Base := Base) (.kinded Δ A .star))
    (right : Certificate (.kinded Δ B .star)) :
    Certificate (.kinded Δ (.arr A B) .star) := .kArr left right

theorem subtype (carrier : Certificate (Base := Base) (.kinded Δ A .star))
    (predicate : Certificate (.hasType Δ [A] p .bool)) :
    Certificate (.kinded Δ (.sub A p) .star) := .kSub carrier predicate

-- Term typing.
theorem var (h : Γ[n]? = some A) :
    Certificate (Base := Base) (.hasType Δ Γ (.var n) A) := .var h

theorem app (fn : Certificate (Base := Base) (.hasType Δ Γ f (.arr A B)))
    (arg : Certificate (.hasType Δ Γ x A)) :
    Certificate (.hasType Δ Γ (.app f x) B) := .app fn arg

theorem lam (domain : Certificate (Base := Base) (.kinded Δ A .star))
    (body : Certificate (.hasType Δ (A :: Γ) t B)) :
    Certificate (.hasType Δ Γ (.lam A t) (.arr A B)) := .lam domain body

theorem typeApp (fn : Certificate (Base := Base) (.hasType Δ Γ f (.app F X)))
    (arg : Certificate (.kinded Δ A K)) :
    Certificate (.hasType Δ Γ (.tyApp f A) (.app F A)) := .tyApp fn arg

theorem typeLam (body : Certificate (Base := Base) (.hasType (K :: Δ) Γ t A)) :
    Certificate (.hasType Δ Γ (.tyLam K t) (.lam K A)) := .tyLam body

theorem bool (b : Bool) :
    Certificate (Base := Base) (.hasType Δ Γ (.bool b) .bool) := .bool

theorem equal (type : Certificate (Base := Base) (.kinded Δ A .star))
    (left : Certificate (.hasType Δ Γ x A))
    (right : Certificate (.hasType Δ Γ y A)) :
    Certificate (.hasType Δ Γ (.eq A x y) .bool) := .eq type left right

theorem choice (type : Certificate (Base := Base) (.kinded Δ A .star))
    (predicate : Certificate (.hasType Δ Γ p (.arr A .bool))) :
    Certificate (.hasType Δ Γ (.epsilon A p) A) := .epsilon type predicate

theorem abs (type : Certificate (Base := Base) (.kinded Δ A .star))
    (predicate : Certificate (.hasType Δ [A] p .bool))
    (value : Certificate (.hasType Δ Γ x A)) :
    Certificate (.hasType Δ Γ (.abs A p x) (.sub A p)) :=
  .abs type predicate value

theorem rep (type : Certificate (Base := Base) (.kinded Δ A .star))
    (predicate : Certificate (.hasType Δ [A] p .bool))
    (value : Certificate (.hasType Δ Γ x (.sub A p))) :
    Certificate (.hasType Δ Γ (.rep A p x) A) :=
  .rep type predicate value

end Rules

/-- A term context bundled with the local kinding certificates for its entries.
Checking extension therefore checks just the new head. -/
structure Context (Base : Type u) (Δ : KindCtx) where
  types : TermCtx Base
  valid : ∀ A, A ∈ types → Certificate (.kinded Δ A .star)

namespace Context

def empty (Base : Type u) (Δ : KindCtx) : Context Base Δ :=
  ⟨[], by simp⟩

def cons (A : Ty Base) (hA : Certificate (.kinded Δ A .star))
    (Γ : Context Base Δ) : Context Base Δ where
  types := A :: Γ.types
  valid B h := by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact hA
    · exact Γ.valid B h

@[simp] theorem empty_types : (empty Base Δ).types = [] := rfl

@[simp] theorem cons_types {A : Ty Base}
    {hA : Certificate (.kinded Δ A .star)} (Γ : Context Base Δ) :
    (cons A hA Γ).types = A :: Γ.types := rfl

end Context

/-- Soundness of every type-formation rule in one statement. -/
theorem kindSound (M : HOLOmega.SoundModel Base Ω)
    (d : Certificate (.kinded Δ A K)) (ρ : HOLOmega.KindEnv Ω Δ) :
    ∃ a, HOLOmega.TyDenotes M ρ A K a :=
  d.toKinded.sound M ρ

/-- Soundness of every term-typing rule in one statement. -/
theorem termSound (M : HOLOmega.SoundModel Base Ω)
    (d : Certificate (.hasType Δ Γ t A))
    (ρ : HOLOmega.KindEnv Ω Δ)
    (γ : STLC.Env (fun _ => Ω) Γ) (hγ : HOLOmega.CtxValid M Γ γ) :
    ∃ x, HOLOmega.TmDenotes M ρ γ t x ∧ x ∈ M.carrier A :=
  d.toHasType.sound M ρ γ hγ

namespace Logic

/-! The logical layer uses the standard Tarskian model.  Types and terms are
intrinsic here, so every rule constructor is impossible to form at the wrong
kind or type.  `Proof` remains an ordinary inductive tree. -/

abbrev Universe := HOLOmega.Kernel.Universe
abbrev SemanticTy (U : Universe) (Δ : List Kind) (K : Kind) :=
  HOLOmega.Kernel.Ty U Δ K
abbrev SemanticTm (U : Universe) {Δ : List Kind}
    (Γ : HOLOmega.Kernel.Ctx U Δ) (A : HOLOmega.Kernel.Ty U Δ .star) :=
  HOLOmega.Kernel.Tm U Γ A
abbrev Equality (U : Universe) {Δ : List Kind}
    (Γ : HOLOmega.Kernel.Ctx U Δ) {A : HOLOmega.Kernel.Ty U Δ .star}
    (x y : HOLOmega.Kernel.Tm U Γ A) := HOLOmega.Kernel.EqTm U Γ x y
abbrev Proof (U : Universe) {Δ : List Kind} {Γ : HOLOmega.Kernel.Ctx U Δ}
    (H : List (HOLOmega.Kernel.Tm U Γ (HOLOmega.Kernel.Ty.boolCode U)))
    (p : HOLOmega.Kernel.Tm U Γ (HOLOmega.Kernel.Ty.boolCode U)) :=
  HOLOmega.Kernel.Derives U H p
abbrev Entails (U : Universe) {Δ : List Kind} {Γ : HOLOmega.Kernel.Ctx U Δ}
    (H : List (HOLOmega.Kernel.Tm U Γ (HOLOmega.Kernel.Ty.boolCode U)))
    (p : HOLOmega.Kernel.Tm U Γ (HOLOmega.Kernel.Ty.boolCode U)) :=
  HOLOmega.Kernel.Entails U H p

/-- `Equality` has exactly these constructors: reflexivity, symmetry,
transitivity, application and abstraction congruence at both term and type
levels, and term/type beta and eta. -/
abbrev EqualityRules (U : Universe) := @HOLOmega.Kernel.EqTm U

/-- `Proof` has exactly these constructors: assumption, truth, equality
reflexivity and substitution, choice, conversion, equality introduction,
Boolean antisymmetry, and both directions of the subtype isomorphism. -/
abbrev ProofRules (U : Universe) := @HOLOmega.Kernel.Derives U

/-- Every equality rule denotes actual equality in the standard model. -/
theorem equalitySound {U : Universe} {Δ : List Kind}
    {Γ : HOLOmega.Kernel.Ctx U Δ} {A : HOLOmega.Kernel.Ty U Δ .star}
    {x y : HOLOmega.Kernel.Tm U Γ A}
    (d : HOLOmega.Kernel.EqTm U Γ x y) : x = y :=
  d.sound U

/-- Every HOLω logical rule preserves truth in the standard model. -/
theorem proofSound {U : Universe} {Δ : List Kind}
    {Γ : HOLOmega.Kernel.Ctx U Δ}
    {H : List (HOLOmega.Kernel.Tm U Γ (HOLOmega.Kernel.Ty.boolCode U))}
    {p : HOLOmega.Kernel.Tm U Γ (HOLOmega.Kernel.Ty.boolCode U)}
    (d : HOLOmega.Kernel.Derives U H p) : HOLOmega.Kernel.Entails U H p :=
  d.sound U

end Logic

end ProjectBeth.HOLOmega.CovalenceSpec
