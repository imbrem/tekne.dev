import ProjectBeth.Defs.Closure

/-! Concrete closure codes for power levels and their bounded subsets. -/

universe u v w

namespace ProjectBeth

namespace PowerLevel

def raise {Base : Type u} : {n m : Nat} → n ≤ m → PowerLevel Base n ↪ PowerLevel Base m
  | 0, 0, _ => Function.Embedding.refl _
  | 0, m + 1, _ => (raise (Nat.zero_le m)).trans ix
  | n + 1, 0, h => nomatch h
  | n + 1, m + 1, h =>
      mapEmbedding (raise (Nat.succ_le_succ_iff.mp h)) 1

@[simp]
theorem raise_ix {Base : Type u} {n m : Nat} (h : n ≤ m)
    (x : PowerLevel Base n) :
    raise (Nat.succ_le_succ h) (ix x) = ix (raise h x) := by
  change Set.image (raise h) {x} = {raise h x}
  simp

end PowerLevel

structure BethLevel where
  level : Nat

instance : CoeSort BethLevel Type where
  coe A := PowerLevel Nat A.level

namespace BethLevel

private def common (A B : BethLevel) := max A.level B.level

private def leftCode {X : Type u} (x : X) : Set (Set X) := {{x}}
private def rightCode {X : Type u} (x : X) : Set (Set X) := {∅, {x}}

private theorem leftCode_injective {X : Type u} : Function.Injective (@leftCode X) := by
  intro x y h
  simpa [leftCode] using h

private theorem rightCode_injective {X : Type u} : Function.Injective (@rightCode X) := by
  intro x y h
  have h' : ({x} : Set X) ∈ rightCode x := by simp [rightCode]
  rw [h] at h'
  simpa [rightCode] using h'

private theorem left_ne_right {X : Type u} (x y : X) : leftCode x ≠ rightCode y := by
  intro h
  have h' : (∅ : Set X) ∈ leftCode x := by simpa [h, rightCode]
  simpa [leftCode] using h'

private def sumCode {X : Type u} : (X ⊕ X) ↪ Set (Set X) where
  toFun
    | Sum.inl x => leftCode x
    | Sum.inr y => rightCode y
  inj' a b h := by
    cases a with
    | inl x =>
      cases b with
      | inl y => exact congrArg Sum.inl (leftCode_injective h)
      | inr y => exact False.elim (left_ne_right x y h)
    | inr x =>
      cases b with
      | inl y => exact False.elim (left_ne_right y x h.symm)
      | inr y => exact congrArg Sum.inr (rightCode_injective h)

private def pairCode {X : Type u} : (X × X) ↪ Set (Set (Set X)) where
  toFun p := {leftCode p.1, rightCode p.2}
  inj' a b h := by
    change ({leftCode a.1, rightCode a.2} : Set (Set (Set X))) =
      {leftCode b.1, rightCode b.2} at h
    have ha : leftCode a.1 ∈ ({leftCode b.1, rightCode b.2} : Set (Set (Set X))) := by
      rw [← h]
      simp
    have hb : rightCode a.2 ∈ ({leftCode b.1, rightCode b.2} : Set (Set (Set X))) := by
      rw [← h]
      simp
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact False.elim (left_ne_right b.1 a.2 hb.symm)
      · exact Prod.ext (leftCode_injective ha) (rightCode_injective hb)
    · exact False.elim (left_ne_right a.1 b.2 ha)

private def intoCommon (A B : BethLevel) : UEl A ↪ PowerLevel Nat (common A B) :=
  PowerLevel.raise (Nat.le_max_left _ _)

private def intoCommonRight (A B : BethLevel) : UEl B ↪ PowerLevel Nat (common A B) :=
  PowerLevel.raise (Nat.le_max_right _ _)

private def sumEmbedding (A B : BethLevel) :
    (UEl A ⊕ UEl B) ↪ PowerLevel Nat (common A B + 2) :=
  (Function.Embedding.sumMap (intoCommon A B) (intoCommonRight A B)).trans sumCode

private def prodEmbedding (A B : BethLevel) :
    (UEl A × UEl B) ↪ PowerLevel Nat (common A B + 3) :=
  (Function.Embedding.prodMap (intoCommon A B) (intoCommonRight A B)).trans pairCode

private def graphCode {A B X : Type u} (ea : A ↪ X) (eb : B ↪ X) :
    (A → B) ↪ Set (Set (Set (Set X))) :=
  let pair : Code (A × B) (Set (Set (Set X))) := {
    code := (ea.prodMap eb).trans pairCode
    code_inj := ((ea.prodMap eb).trans pairCode).injective
  }
  let graph := FunCode.graph₂.comp pair.set
  { toFun := graph.code, inj' := graph.code_inj }

private def arrowEmbedding (A B : BethLevel) :
    (UEl A → UEl B) ↪ PowerLevel Nat (common A B + 4) :=
  graphCode (intoCommon A B) (intoCommonRight A B)

instance : SumClosed BethLevel where
  sum A B := ⟨common A B + 2⟩
  embed := sumEmbedding

instance : ProdClosed BethLevel where
  prod A B := ⟨common A B + 3⟩
  embed := prodEmbedding

instance : ArrowClosed BethLevel where
  arrow A B := ⟨common A B + 4⟩
  embed := arrowEmbedding

end BethLevel

namespace BoundedSet

variable {Base : Type u} {Base' : Type v} {Base'' : Type w}

def common (A B : BoundedSet Base) := max A.level B.level

def map (f : Base ↪ Base') (A : BoundedSet Base) : BoundedSet Base' :=
  ⟨A.level, PowerLevel.map f A.level '' A.carrier⟩

@[simp]
theorem map_refl (A : BoundedSet Base) :
    map (Function.Embedding.refl Base) A = A := by
  cases A with
  | mk level carrier =>
      simp only [map]
      congr
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        change PowerLevel.map id level y = x at hxy
        rw [PowerLevel.map_id] at hxy
        simpa [← hxy] using hy
      · intro hx
        refine ⟨x, hx, ?_⟩
        change PowerLevel.map id level x = x
        exact PowerLevel.map_id level x

theorem map_trans (f : Base ↪ Base') (g : Base' ↪ Base'') (A : BoundedSet Base) :
    map (f.trans g) A = map g (map f A) := by
  cases A with
  | mk level carrier =>
      simp only [map]
      congr
      ext x
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨PowerLevel.map f level y, ⟨y, hy, rfl⟩,
          (PowerLevel.map_comp g f level y).symm⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, PowerLevel.map_comp g f level y⟩

noncomputable def mapEquiv (f : Base ↪ Base') (A : BoundedSet Base) :
    UEl A ≃ UEl (map f A) where
  toFun x := ⟨PowerLevel.map f A.level x.val, x.val, x.property, rfl⟩
  invFun y := ⟨Classical.choose y.property, (Classical.choose_spec y.property).1⟩
  left_inv x := Subtype.ext ((PowerLevel.map_injective f.injective A.level)
    (Classical.choose_spec
      (show PowerLevel.map f A.level x.val ∈ PowerLevel.map f A.level '' A.carrier from
        ⟨x.val, x.property, rfl⟩)).2)
  right_inv y := Subtype.ext (Classical.choose_spec y.property).2

noncomputable def mapEmbedding (f : Base ↪ Base') (A : BoundedSet Base) :
    UEl A ↪ UEl (map f A) :=
  (mapEquiv f A).toEmbedding

@[simp]
theorem mapEmbedding_val (f : Base ↪ Base') (A : BoundedSet Base) (x : UEl A) :
    (mapEmbedding f A x).val = PowerLevel.map f A.level x.val := rfl

def intoCommon (A B : BoundedSet Base) :
    UEl A ↪ PowerLevel Base (common A B) :=
  (Function.Embedding.subtype _).trans
    (PowerLevel.raise (Nat.le_max_left A.level B.level))

def intoCommonRight (A B : BoundedSet Base) :
    UEl B ↪ PowerLevel Base (common A B) :=
  (Function.Embedding.subtype _).trans
    (PowerLevel.raise (Nat.le_max_right A.level B.level))

def sumEmbedding (A B : BoundedSet Base) :
    (UEl A ⊕ UEl B) ↪ PowerLevel Base (common A B + 2) :=
  (Function.Embedding.sumMap (intoCommon A B) (intoCommonRight A B)).trans BethLevel.sumCode

def prodEmbedding (A B : BoundedSet Base) :
    (UEl A × UEl B) ↪ PowerLevel Base (common A B + 3) :=
  (Function.Embedding.prodMap (intoCommon A B) (intoCommonRight A B)).trans BethLevel.pairCode

def arrowEmbedding (A B : BoundedSet Base) :
    (UEl A → UEl B) ↪ PowerLevel Base (common A B + 4) :=
  BethLevel.graphCode (intoCommon A B) (intoCommonRight A B)

def powersetEmbedding (A : BoundedSet Base) :
    Set (UEl A) ↪ PowerLevel Base (A.level + 1) :=
  PowerLevel.mapEmbedding (Function.Embedding.subtype _) 1

noncomputable def rangeEquiv (e : α ↪ β) : α ≃ Set.range e where
  toFun x := ⟨e x, x, rfl⟩
  invFun y := Classical.choose y.property
  left_inv x := e.injective (Classical.choose_spec (show e x ∈ Set.range e from ⟨x, rfl⟩))
  right_inv y := Subtype.ext (Classical.choose_spec y.property)

@[simp]
theorem rangeEquiv_val (e : α ↪ β) (x : α) : (rangeEquiv e x).val = e x := rfl

def sumObj (A B : BoundedSet Base) : BoundedSet Base :=
  ⟨common A B + 2, Set.range (sumEmbedding A B)⟩

def prodObj (A B : BoundedSet Base) : BoundedSet Base :=
  ⟨common A B + 3, Set.range (prodEmbedding A B)⟩

def arrowObj (A B : BoundedSet Base) : BoundedSet Base :=
  ⟨common A B + 4, Set.range (arrowEmbedding A B)⟩

def powersetObj (A : BoundedSet Base) : BoundedSet Base :=
  ⟨A.level + 1, Set.range (powersetEmbedding A)⟩

noncomputable instance : SumExact (BoundedSet Base) where
  sum := sumObj
  embed A B := (rangeEquiv (sumEmbedding A B)).toEmbedding
  equiv A B := rangeEquiv (sumEmbedding A B)
  embed_eq _ _ := rfl

noncomputable instance : ProdExact (BoundedSet Base) where
  prod := prodObj
  embed A B := (rangeEquiv (prodEmbedding A B)).toEmbedding
  equiv A B := rangeEquiv (prodEmbedding A B)
  embed_eq _ _ := rfl

noncomputable instance : ArrowExact (BoundedSet Base) where
  arrow := arrowObj
  embed A B := (rangeEquiv (arrowEmbedding A B)).toEmbedding
  equiv A B := rangeEquiv (arrowEmbedding A B)
  embed_eq _ _ := rfl

noncomputable instance : PowersetExact (BoundedSet Base) where
  powerset := powersetObj
  embed A := (rangeEquiv (powersetEmbedding A)).toEmbedding
  equiv A := rangeEquiv (powersetEmbedding A)
  embed_eq _ := rfl

@[simp]
theorem sum_embed_val (A B : BoundedSet Base) (x : UEl A ⊕ UEl B) :
    (SumClosed.embed A B x).val = sumEmbedding A B x := rfl

@[simp]
theorem prod_embed_val (A B : BoundedSet Base) (x : UEl A × UEl B) :
    (ProdClosed.embed A B x).val = prodEmbedding A B x := rfl

@[simp]
theorem arrow_embed_val (A B : BoundedSet Base) (f : UEl A → UEl B) :
    (ArrowClosed.embed A B f).val = arrowEmbedding A B f := rfl

@[simp]
theorem powerset_embed_val (A : BoundedSet Base) (s : Set (UEl A)) :
    (PowersetClosed.embed A s).val = powersetEmbedding A s := rfl

@[simp]
theorem powersetEmbedding_apply (A : BoundedSet Base) (s : Set (UEl A)) :
    powersetEmbedding A s = Subtype.val '' s := rfl

end BoundedSet

end ProjectBeth
