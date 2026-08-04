import ProjectBeth.Defs.Syntax.Alpha

universe u v w

namespace ProjectBeth.Syntax.LocallyNameless

variable {Name : Type u} {Name' : Type v} {Name'' : Type w}

def renameFree (f : Name → Name') : Tm Name → Tm Name'
  | .var (.bound i) => .var (.bound i)
  | .var (.free x) => .var (.free (f x))
  | .app p q => .app (renameFree f p) (renameFree f q)
  | .lam b => .lam (renameFree f b)

def substFree (σ : Name → Tm Name') : Tm Name → Tm Name'
  | .var (.bound i) => .var (.bound i)
  | .var (.free x) => σ x
  | .app p q => .app (substFree σ p) (substFree σ q)
  | .lam b => .lam (substFree σ b)

/-- Open a bound index with an arbitrary locally nameless term. -/
def openAtTerm (u : Tm Name) : Nat → Tm Name → Tm Name
  | k, .var (.bound i) => if i = k then u else .var (.bound i)
  | _, .var (.free y) => .var (.free y)
  | k, .app p q => .app (openAtTerm u k p) (openAtTerm u k q)
  | k, .lam b => .lam (openAtTerm u (k + 1) b)

@[simp] theorem renameFree_id (t : Tm Name) : renameFree id t = t := by
  induction t with
  | var v => cases v <;> rfl
  | app p q ihp ihq => simp [renameFree, ihp, ihq]
  | lam b ih => simp [renameFree, ih]

theorem renameFree_comp (f : Name → Name') (g : Name' → Name'') (t : Tm Name) :
    renameFree g (renameFree f t) = renameFree (g ∘ f) t := by
  induction t with
  | var v => cases v <;> rfl
  | app p q ihp ihq => simp [renameFree, ihp, ihq]
  | lam b ih => simp [renameFree, ih]

@[simp] theorem substFree_var (t : Tm Name) :
    substFree (fun x => .var (.free x)) t = t := by
  induction t with
  | var v => cases v <;> rfl
  | app p q ihp ihq => simp [substFree, ihp, ihq]
  | lam b ih => simp [substFree, ih]

theorem substFree_comp (σ : Name → Tm Name') (τ : Name' → Tm Name'')
    (t : Tm Name) :
    substFree τ (substFree σ t) = substFree (fun x => substFree τ (σ x)) t := by
  induction t with
  | var v => cases v <;> rfl
  | app p q ihp ihq => simp [substFree, ihp, ihq]
  | lam b ih => simp [substFree, ih]

theorem renameFree_substFree (f : Name' → Name'') (σ : Name → Tm Name')
    (t : Tm Name) :
    renameFree f (substFree σ t) = substFree (fun x => renameFree f (σ x)) t := by
  induction t with
  | var v => cases v <;> rfl
  | app p q ihp ihq => simp [renameFree, substFree, ihp, ihq]
  | lam b ih => simp [renameFree, substFree, ih]

theorem substFree_renameFree (σ : Name' → Tm Name'') (f : Name → Name')
    (t : Tm Name) :
    substFree σ (renameFree f t) = substFree (σ ∘ f) t := by
  induction t with
  | var v => cases v <;> rfl
  | app p q ihp ihq => simp [renameFree, substFree, ihp, ihq]
  | lam b ih => simp [renameFree, substFree, ih]

theorem renameFree_openAt (f : Name → Name') (x : Name) (k : Nat) (t : Tm Name) :
    renameFree f (openAt x k t) = openAt (f x) k (renameFree f t) := by
  induction t generalizing k with
  | var v =>
    cases v with
    | free => rfl
    | bound i => by_cases h : i = k <;> simp [openAt, renameFree, h]
  | app p q ihp ihq => simp [openAt, renameFree, ihp, ihq]
  | lam b ih => simp [openAt, renameFree, ih]

end ProjectBeth.Syntax.LocallyNameless
