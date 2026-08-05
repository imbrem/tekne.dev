import ProjectBeth.Defs.HOL.Syntax

universe u

namespace ProjectBeth.HOL.TheoryVariants

variable {Content : Type u}

/-- The two conservative declaration forms used by definitional HOL extensions. -/
inductive DeclKind
  | typedef | constdef
  deriving DecidableEq

/-- A pure content-addressable declaration.  Dependencies are embedded by content,
so cycles are unrepresentable. -/
inductive Tree (Content : Type u) : Type u
  | decl (kind : DeclKind) (content : Content) (dependencies : List (Tree Content))

namespace Tree

def dependencies : Tree Content → List (Tree Content)
  | .decl _ _ ds => ds

def content : Tree Content → Content
  | .decl _ c _ => c

def kind : Tree Content → DeclKind
  | .decl k _ _ => k

/-- Structural equality is the content address in the pure presentation. -/
def Address (Content : Type u) := Tree Content

def address (t : Tree Content) : Address Content := t

/-- Compatibility predicate for clients that state well-formedness uniformly
across tree and sequential presentations.  It is automatic for `Tree`: finite
acyclic dependency structure is enforced by the inductive datatype itself. -/
def Wf (_ : Tree Content) : Prop := True

theorem wf (t : Tree Content) : t.Wf := trivial

/-- Postorder flattening: every dependency is emitted before its user. -/
def flatten : Tree Content → List (Tree Content)
  | t@(.decl _ _ ds) => ds.flatMap flatten ++ [t]

theorem mem_flatten_self (t : Tree Content) : t ∈ t.flatten := by
  cases t
  simp [flatten]

theorem dependency_mem_flatten {t d : Tree Content} (h : d ∈ t.dependencies) :
    d ∈ t.flatten := by
  cases t with
  | decl k c ds =>
    simp only [dependencies] at h
    simp only [flatten, List.mem_append, List.mem_flatMap, List.mem_singleton]
    exact Or.inl ⟨d, h, mem_flatten_self d⟩

end Tree

/-- A sequential typedef/constdef theory. References are content addresses; `Wf`
requires every dependency to occur strictly earlier. -/
abbrev Sequential (Content : Type u) := List (Tree Content)

namespace Sequential

def Earlier (d t : Tree Content) (xs : Sequential Content) : Prop :=
  ∃ pre post, xs = pre ++ t :: post ∧ d ∈ pre

def Wf (xs : Sequential Content) : Prop :=
  ∀ t ∈ xs, ∀ d ∈ t.dependencies, Earlier d t xs

/-- The inverse presentation forgets sharing and regards maximal declarations as
roots.  It is always meaningful, although `flatten (toTrees xs)` may duplicate
shared dependencies. -/
def toTrees (xs : Sequential Content) : List (Tree Content) := xs

def flattenTrees (roots : List (Tree Content)) : Sequential Content :=
  roots.flatMap Tree.flatten

end Sequential

/-- Acyclic trees flatten to lists in dependency order.  This local formulation is
often more useful than a global no-duplicate condition. -/
theorem flatten_dependency_before (t d : Tree Content) (hd : d ∈ t.dependencies) :
    ∃ pre post, t.flatten = pre ++ t :: post ∧ d ∈ pre := by
  cases t with
  | decl k c ds =>
    simp only [Tree.dependencies] at hd
    refine ⟨ds.flatMap Tree.flatten, [], ?_, ?_⟩
    · simp [Tree.flatten]
    · exact List.mem_flatMap.mpr ⟨d, hd, Tree.mem_flatten_self d⟩

namespace Semantics

/-- A declaration predicate abstracts the usual obligations: typedef predicates
are inhabited and constdefs denote the declared term. -/
def Sequential.Valid (valid : DeclKind → Content → Prop) (xs : Sequential Content) : Prop :=
  ∀ t ∈ xs, valid t.kind t.content

/-- Direct validity of a content tree: every declaration reachable in its finite
dependency closure meets its declaration-specific obligation. -/
def Tree.Valid (valid : DeclKind → Content → Prop) (t : Tree Content) : Prop :=
  Sequential.Valid valid t.flatten

theorem treeValid_iff_flattenValid (valid : DeclKind → Content → Prop)
    (t : Tree Content) :
    Tree.Valid valid t ↔ Sequential.Valid valid t.flatten := by
  rfl

theorem forestValid_iff_flattenValid (valid : DeclKind → Content → Prop)
    (roots : List (Tree Content)) :
    (∀ t ∈ roots, Tree.Valid valid t) ↔
      Sequential.Valid valid (Sequential.flattenTrees roots) := by
  constructor
  · intro h x hx
    obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx
    exact (treeValid_iff_flattenValid valid t).mp (h t ht) x hxt
  · intro h t ht
    apply (treeValid_iff_flattenValid valid t).mpr
    intro x hx
    exact h x (List.mem_flatMap.mpr ⟨t, ht, hx⟩)

end Semantics

end ProjectBeth.HOL.TheoryVariants
