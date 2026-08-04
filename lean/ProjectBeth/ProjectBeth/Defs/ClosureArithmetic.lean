import ProjectBeth.Defs.BethClosure
import Mathlib.Data.Fintype.BigOperators

namespace ProjectBeth

namespace FinLevel

@[simp]
theorem sum_card (A B : FinLevel) :
    (SumClosed.sum A B).card = A.card + B.card := by
  simp [SumClosed.sum]

@[simp]
theorem prod_card (A B : FinLevel) :
    (ProdClosed.prod A B).card = A.card * B.card := by
  simp [ProdClosed.prod]

@[simp]
theorem arrow_card (A B : FinLevel) :
    (ArrowClosed.arrow A B).card = B.card ^ A.card := by
  change Fintype.card (Fin A.card → Fin B.card) = _
  rw [Fintype.card_pi_const]
  simp

end FinLevel

namespace BethLevel

@[simp]
theorem sum_level (A B : BethLevel) :
    (SumClosed.sum A B).level = max A.level B.level + 2 := rfl

@[simp]
theorem prod_level (A B : BethLevel) :
    (ProdClosed.prod A B).level = max A.level B.level + 3 := rfl

@[simp]
theorem arrow_level (A B : BethLevel) :
    (ArrowClosed.arrow A B).level = max A.level B.level + 4 := rfl

end BethLevel

end ProjectBeth
