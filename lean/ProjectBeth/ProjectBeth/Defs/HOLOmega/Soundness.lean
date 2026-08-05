import ProjectBeth.Defs.HOLOmega.Semantics

universe u v

namespace ProjectBeth.HOLOmega

def KindEnv.lookup {Ω : Type v} {Δ : List Kind} {n : Nat} {K : Kind}
    (h : Δ[n]? = some K) (ρ : KindEnv Ω Δ) : Kind.denote Ω K := by
  induction Δ generalizing n K with
  | nil => simp at h
  | cons L Δ ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst K
      exact ρ.1
    | succ n =>
      exact ih (by simpa using h) ρ.2

def envLookupNat {Ty : Type u} {El : Ty → Type v} {Γ : List Ty}
    {n : Nat} {A : Ty} (h : Γ[n]? = some A) (γ : STLC.Env El Γ) : El A := by
  induction Γ generalizing n A with
  | nil => simp at h
  | cons B Γ ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst A
      exact γ.1
    | succ n =>
      exact ih (by simpa using h) γ.2

/-- Operations on a common carrier, together with exactly the closure laws used by
the pure-tree HOLω rules.  The carrier interpretation is deliberately defined on
raw types: this also gives a semantics to open contexts before a separate
well-kinded-context judgment is imposed. -/
structure SoundModel (Base : Type u) (Ω : Type v) where
  carrier : Ty Base → Set Ω
  app : Ω → Ω → Ω
  lam : (Ω → Ω) → Ω
  tyApp : Ω → (K : Kind) → Kind.denote Ω K → Ω
  tyLam : (K : Kind) → (Kind.denote Ω K → Ω) → Ω
  bool : Bool → Ω
  equal : Ω → Ω → Ω
  epsilon : (Ω → Ω) → Ω
  abs : Tm Base → (Ω → Ω) → Ω → Ω
  rep : Tm Base → (Ω → Ω) → Ω → Ω
  app_mem : ∀ {A B f x}, f ∈ carrier (.arr A B) → x ∈ carrier A →
    app f x ∈ carrier B
  lam_mem : ∀ {A B} (f : Ω → Ω),
    (∀ x, x ∈ carrier A → f x ∈ carrier B) → lam f ∈ carrier (.arr A B)
  tyApp_mem : ∀ {F X A K} (a : Kind.denote Ω K) {f},
    f ∈ carrier (.app F X) → tyApp f K a ∈ carrier (.app F A)
  tyLam_mem : ∀ {K A} (f : Kind.denote Ω K → Ω),
    (∀ X, f X ∈ carrier A) → tyLam K f ∈ carrier (.lam K A)
  bool_mem : ∀ b, bool b ∈ carrier .bool
  equal_mem : ∀ {A x y}, x ∈ carrier A → y ∈ carrier A →
    equal x y ∈ carrier .bool
  epsilon_mem : ∀ {A} (p : Ω → Ω),
    (∀ x, x ∈ carrier A → p x ∈ carrier .bool) → epsilon p ∈ carrier A
  abs_mem : ∀ {A P} (p : Ω → Ω) {x},
    (∀ y, y ∈ carrier A → p y ∈ carrier .bool) → x ∈ carrier A →
    abs P p x ∈ carrier (.sub A P)
  rep_mem : ∀ {A P} (p : Ω → Ω) {x},
    (∀ y, y ∈ carrier A → p y ∈ carrier .bool) →
    x ∈ carrier (.sub A P) → rep P p x ∈ carrier A

/-- Relational interpretation avoids choosing computational content from a
proof-irrelevant kinding derivation. -/
inductive TyDenotes {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω) :
    {Δ : List Kind} → KindEnv Ω Δ → Ty Base → (K : Kind) → Kind.denote Ω K → Prop
  | base {Δ ρ A} : TyDenotes M (Δ := Δ) ρ (.base A) .star (M.carrier (.base A))
  | var {Δ ρ n K} (h : Δ[n]? = some K) :
      TyDenotes M ρ (.var n) K (ρ.lookup h)
  | lam {Δ ρ A K L} {f : Kind.denote Ω K → Kind.denote Ω L} :
      (∀ X, TyDenotes M (Δ := K :: Δ) (X, ρ) A L (f X)) →
      TyDenotes M ρ (.lam K A) (.arr K L) f
  | app {Δ ρ F X K L} {f : Kind.denote Ω K → Kind.denote Ω L}
      {x : Kind.denote Ω K} :
      TyDenotes M (Δ := Δ) ρ F (.arr K L) f → TyDenotes M ρ X K x →
      TyDenotes M ρ (.app F X) L (f x)
  | bool {Δ ρ} : TyDenotes M (Δ := Δ) ρ .bool .star (M.carrier .bool)
  | arr {Δ ρ A B} :
      TyDenotes M (Δ := Δ) ρ (.arr A B) .star (M.carrier (.arr A B))
  | sub {Δ ρ A p} :
      TyDenotes M (Δ := Δ) ρ (.sub A p) .star (M.carrier (.sub A p))

def CtxValid {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω) :
    (Γ : List (Ty Base)) → STLC.Env (fun _ => Ω) Γ → Prop
  | [], _ => True
  | A :: Γ, γ => γ.1 ∈ M.carrier A ∧ CtxValid M Γ γ.2

inductive TmDenotes {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω) :
    {Δ : List Kind} → KindEnv Ω Δ → {Γ : List (Ty Base)} →
      STLC.Env (fun _ => Ω) Γ → Tm Base → Ω → Prop
  | var {Δ ρ} {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ} {n A}
      (h : Γ[n]? = some A) :
      TmDenotes M (Δ := Δ) ρ γ (.var n) (envLookupNat h γ)
  | app {Δ ρ} {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ} {f x fv xv} :
      TmDenotes M (Δ := Δ) ρ γ f fv → TmDenotes M ρ γ x xv →
      TmDenotes M ρ γ (.app f x) (M.app fv xv)
  | lam {Δ ρ} {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ} {A t}
      {f : Ω → Ω} :
      (∀ x, x ∈ M.carrier A →
        TmDenotes M (Δ := Δ) ρ (Γ := A :: Γ) (x, γ) t (f x)) →
      TmDenotes M ρ γ (.lam A t) (M.lam f)
  | tyApp {Δ ρ} {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ}
      {f A K fv a} :
      TmDenotes M (Δ := Δ) ρ γ f fv → TyDenotes M ρ A K a →
      TmDenotes M ρ γ (.tyApp f A) (M.tyApp fv K a)
  | tyLam {Δ ρ} {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ} {K t}
      {f : Kind.denote Ω K → Ω} :
      (∀ X, TmDenotes M (Δ := K :: Δ) (X, ρ) γ t (f X)) →
      TmDenotes M ρ γ (.tyLam K t) (M.tyLam K f)
  | bool {Δ ρ} {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ} {b} :
      TmDenotes M (Δ := Δ) ρ (Γ := Γ) γ (.bool b) (M.bool b)
  | eq {Δ ρ} {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ} {A x y xv yv} :
      TmDenotes M (Δ := Δ) ρ γ x xv → TmDenotes M ρ γ y yv →
      TmDenotes M ρ γ (.eq A x y) (M.equal xv yv)
  | epsilon {Δ ρ} {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ} {A p pv} :
      TmDenotes M (Δ := Δ) ρ γ p pv →
      TmDenotes M ρ γ (.epsilon A p) (M.epsilon (fun x => M.app pv x))
  | abs {Δ ρ} {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ} {A P x xv}
      {p : Ω → Ω} :
      (∀ y, y ∈ M.carrier A →
        TmDenotes M (Δ := Δ) ρ (Γ := [A]) (y, PUnit.unit) P (p y)) →
      TmDenotes M ρ γ x xv →
      TmDenotes M ρ γ (.abs A P x) (M.abs P p xv)
  | rep {Δ ρ} {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ} {A P x xv}
      {p : Ω → Ω} :
      (∀ y, y ∈ M.carrier A →
        TmDenotes M (Δ := Δ) ρ (Γ := [A]) (y, PUnit.unit) P (p y)) →
      TmDenotes M ρ γ x xv →
      TmDenotes M ρ γ (.rep A P x) (M.rep P p xv)

private def KindSound {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω)
    {Δ : List Kind} {A : Ty Base} {K : Kind} (_ : Kinded Δ A K) : Prop :=
  ∀ ρ : KindEnv Ω Δ, ∃ a, TyDenotes M (Δ := Δ) ρ A K a

private def TermSound {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω)
    {Δ : List Kind} {Γ : List (Ty Base)} {t : Tm Base} {A : Ty Base}
    (_ : HasType Δ Γ t A) : Prop :=
  ∀ (ρ : KindEnv Ω Δ) (γ : STLC.Env (fun _ => Ω) Γ), CtxValid M Γ γ →
    ∃ x, TmDenotes M (Δ := Δ) ρ γ t x ∧ x ∈ M.carrier A

theorem CtxValid.lookup {Base : Type u} {Ω : Type v} {M : SoundModel Base Ω}
    {Γ : List (Ty Base)} {γ : STLC.Env (fun _ => Ω) Γ} (hγ : CtxValid M Γ γ)
    {n : Nat} {A : Ty Base} (h : Γ[n]? = some A) : envLookupNat h γ ∈ M.carrier A := by
  induction Γ generalizing n A with
  | nil => simp at h
  | cons B Γ ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst A
      exact hγ.1
    | succ n =>
      exact ih hγ.2 (by simpa using h)

theorem Kinded.sound {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω)
    {Δ : List Kind} {A : Ty Base} {K : Kind} (h : Kinded Δ A K) :
    ∀ ρ : KindEnv Ω Δ, ∃ a, TyDenotes M (Δ := Δ) ρ A K a := by
  apply Kinded.rec (motive_1 := fun Δ A K h => KindSound M h)
    (motive_2 := fun _ _ _ _ _ => True)
    (t := h)
  · intro Δ A ρ
    exact ⟨_, .base⟩
  · intro Δ n K hn ρ
    exact ⟨_, .var hn⟩
  · intro K Δ A L h ih ρ
    classical
    choose f hf using fun X => ih (X, ρ)
    exact ⟨f, .lam hf⟩
  · intro Δ F K L X hf hx ihf ihx ρ
    obtain ⟨f, hfd⟩ := ihf ρ
    obtain ⟨x, hxd⟩ := ihx ρ
    exact ⟨f x, .app hfd hxd⟩
  · intro Δ ρ
    exact ⟨_, .bool⟩
  · intro Δ A B hA hB ihA ihB ρ
    exact ⟨_, .arr⟩
  · intro Δ A p hA hp ihA ihp ρ
    exact ⟨_, .sub⟩
  all_goals intros <;> trivial

theorem HasType.sound {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω)
    {Δ : List Kind} {Γ : List (Ty Base)} {t : Tm Base} {A : Ty Base}
    (h : HasType Δ Γ t A) : TermSound M h := by
  apply HasType.rec (motive_1 := fun Δ A K h => KindSound M h)
    (motive_2 := fun Δ Γ t A h => TermSound M h) (t := h)
  · intro Δ A ρ
    exact ⟨_, .base⟩
  · intro Δ n K hn ρ
    exact ⟨_, .var hn⟩
  · intro K Δ A L h ih ρ
    classical
    choose f hf using fun X => ih (X, ρ)
    exact ⟨f, .lam hf⟩
  · intro Δ F K L X hf hx ihf ihx ρ
    obtain ⟨f, hfd⟩ := ihf ρ
    obtain ⟨x, hxd⟩ := ihx ρ
    exact ⟨f x, .app hfd hxd⟩
  · intro Δ ρ
    exact ⟨_, .bool⟩
  · intro Δ A B hA hB ihA ihB ρ
    exact ⟨_, .arr⟩
  · intro Δ A p hA hp ihA ihp ρ
    exact ⟨_, .sub⟩
  · intro Γ n A Δ hn ρ γ hγ
    exact ⟨envLookupNat hn γ, .var hn, hγ.lookup hn⟩
  · intro Δ Γ f A B x hf hx ihf ihx ρ γ hγ
    obtain ⟨fv, hfd, hfm⟩ := ihf ρ γ hγ
    obtain ⟨xv, hxd, hxm⟩ := ihx ρ γ hγ
    exact ⟨M.app fv xv, .app hfd hxd, M.app_mem hfm hxm⟩
  · intro Δ A Γ t B hA ht ihA iht ρ γ hγ
    classical
    let f : Ω → Ω := fun x =>
      if hx : x ∈ M.carrier A then Classical.choose (iht ρ (x, γ) ⟨hx, hγ⟩)
      else M.bool false
    have hf : ∀ x, x ∈ M.carrier A →
        TmDenotes M ρ (Γ := A :: Γ) (x, γ) t (f x) ∧ f x ∈ M.carrier B := by
      intro x hx
      simp only [f, dif_pos hx]
      exact (Classical.choose_spec (iht ρ (x, γ) ⟨hx, hγ⟩))
    exact ⟨M.lam f, .lam (fun x hx => (hf x hx).1),
      M.lam_mem f (fun x hx => (hf x hx).2)⟩
  · intro Δ Γ f F X A K hf hA ihf ihA ρ γ hγ
    obtain ⟨fv, hfd, hfm⟩ := ihf ρ γ hγ
    obtain ⟨a, ha⟩ := ihA ρ
    exact ⟨M.tyApp fv K a, .tyApp hfd ha, M.tyApp_mem a hfm⟩
  · intro K Δ Γ t A ht iht ρ γ hγ
    classical
    choose f hf using fun X => iht (X, ρ) γ hγ
    exact ⟨M.tyLam K f, .tyLam (fun X => (hf X).1),
      M.tyLam_mem f (fun X => (hf X).2)⟩
  · intro Δ Γ b ρ γ hγ
    exact ⟨M.bool b, .bool, M.bool_mem b⟩
  · intro Δ A Γ x y hA hx hy ihA ihx ihy ρ γ hγ
    obtain ⟨xv, hxd, hxm⟩ := ihx ρ γ hγ
    obtain ⟨yv, hyd, hym⟩ := ihy ρ γ hγ
    exact ⟨M.equal xv yv, .eq hxd hyd, M.equal_mem hxm hym⟩
  · intro Δ A Γ p hA hp ihA ihp ρ γ hγ
    obtain ⟨pv, hpd, hpm⟩ := ihp ρ γ hγ
    exact ⟨M.epsilon (fun x => M.app pv x), .epsilon hpd,
      M.epsilon_mem _ (fun x hx => M.app_mem hpm hx)⟩
  · intro Δ A P Γ x hA hp hx ihA ihp ihx ρ γ hγ
    classical
    let p : Ω → Ω := fun y =>
      if hy : y ∈ M.carrier A then
        Classical.choose (ihp ρ (y, PUnit.unit) ⟨hy, trivial⟩)
      else M.bool false
    have hpd : ∀ y, y ∈ M.carrier A →
        TmDenotes M ρ (Γ := [A]) (y, PUnit.unit) P (p y) ∧
          p y ∈ M.carrier .bool := by
      intro y hy
      simp only [p, dif_pos hy]
      exact Classical.choose_spec (ihp ρ (y, PUnit.unit) ⟨hy, trivial⟩)
    obtain ⟨xv, hxd, hxm⟩ := ihx ρ γ hγ
    exact ⟨M.abs P p xv, .abs (fun y hy => (hpd y hy).1) hxd,
      M.abs_mem p (fun y hy => (hpd y hy).2) hxm⟩
  · intro Δ A P Γ x hA hp hx ihA ihp ihx ρ γ hγ
    classical
    let p : Ω → Ω := fun y =>
      if hy : y ∈ M.carrier A then
        Classical.choose (ihp ρ (y, PUnit.unit) ⟨hy, trivial⟩)
      else M.bool false
    have hpd : ∀ y, y ∈ M.carrier A →
        TmDenotes M ρ (Γ := [A]) (y, PUnit.unit) P (p y) ∧
          p y ∈ M.carrier .bool := by
      intro y hy
      simp only [p, dif_pos hy]
      exact Classical.choose_spec (ihp ρ (y, PUnit.unit) ⟨hy, trivial⟩)
    obtain ⟨xv, hxd, hxm⟩ := ihx ρ γ hγ
    exact ⟨M.rep P p xv, .rep (fun y hy => (hpd y hy).1) hxd,
      M.rep_mem p (fun y hy => (hpd y hy).2) hxm⟩

end ProjectBeth.HOLOmega
