import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.ENNReal.Lemmas

theorem NNRat.toENNReal_sub (a b : ℚ≥0) (h : b ≤ a) :
    (((a - b) : ℚ≥0) : ENNReal) = (↑a : ENNReal) - ↑b := by
  have := Rat.cast_sub (α := Real) a b
  simp only [Rat.cast_nnratCast] at this
  refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_ ).mp ?_

@[grind =, simp]
theorem NNRat.ennreal_cast : (1 : NNRat) = (1 : ENNReal) := by
  simp [NNRat.cast]
  simp [NNRatCast.nnratCast]

example (p : ℚ≥0) (hp : p ≤ 1) : 1 - (↑p : ENNReal) = (↑(1 - p) : ENNReal) := by
  simp [NNRat.toENNReal_sub, hp]

/-
 ∃ X Y Z,
  Z ≠ ∅ ∧

↑(List.map Form.weight ((↑(List.map Form.atoms as ++ [b] ++ imps')).sort LE.le) ++ [1]) = X + Y ∧
↑(List.map Form.weight ((↑(List.map Form.atoms as ++ (Form.atoms a ⊃ b) :: imps')).sort LE.le) ++ [1]) = X + Z ∧

∀ y ∈ Y, ∃ z ∈ Z, y < z

X= List.map Form.atoms as
         -/
