/- Example of some edge cases, try those examples by uncommenting them! -/
import Mathlib.Data.Real.Basic
import RealIneq.Horn

theorem not_prop_example (x y : Real) (h1 : x > 0) (h2 : 3*y > 0) : x + y > 0 := by
  -- horn [x, h2]
  sorry

theorem unknown_hyp_example (x : Real) (h1 : x > 0) : x + 1 > 1 := by
  -- horn [h2]
  sorry

theorem no_hyp_example : ∀ x : Real, x ≥ x := by
  intro x
  -- horn
  sorry

theorem unsupported_example : ∀ x : Real, √x ≥ √x := by
  intro x
  -- horn
  sorry
