/-This example is from Math competition,
we showcase the imandra-geo ability to close the goal and compare with a Lean-user's manual proof.
Notice that once the proof is found by Imandra, the compile time is quite fast compared with Lean's native automation like `nlinarith` -/

import Mathlib
import RealIneq.Horn

set_option linter.unreachableTactic false
set_option linter.unusedTactic false


/- Example 1.11.7. Let \(a, b, c\) be non-negative real numbers with sum 3. Prove that
$$\frac{a+b}{1+b}+\frac{b+c}{1+c}+\frac{c+a}{1+a} \geq 3$$ -/

theorem ex5_imandra (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 3) :
    3 ≤ (a + b) / (1 + b) + (b + c) / (1 + c) + (c + a) / (1 + a) := by
    field_simp
    rw[le_div_iff₀ (by positivity)]
    horn_all
    have imandra_proof : ∀ a b c : ℝ, ((0 ≤ a) → (0 ≤ b) → (0 ≤ c) → (((a + b) + c) = 3) → ((3 * (((1 + b) * (1 + c)) * (1 + a))) ≤ (((((a + b) * (1 + c)) + ((b + c) * (1 + b))) * (1 + a)) + ((c + a) * ((1 + b) * (1 + c)))))) := by
      intros a b c
      by_contra! goal
      rcases goal with ⟨h1, h2, h3, h4, h5⟩

    --  problem polynomials and their properties from the goal
      let prob0 : ℝ := (0 - (0 - a))
      have h_prob_0_nonneg : prob0 ≥ 0 := by unfold prob0; linarith
      let prob1 : ℝ := (0 - (0 - b))
      have h_prob_1_nonneg : prob1 ≥ 0 := by unfold prob1; linarith
      let prob2 : ℝ := (0 - (0 - c))
      have h_prob_2_nonneg : prob2 ≥ 0 := by unfold prob2; linarith
      let prob3 : ℝ := (((a + b) + c) - 3)
      let prob4 : ℝ := ((3 * (((1 + b) * (1 + c)) * (1 + a))) - (((((a + b) * (1 + c)) + ((b + c) * (1 + b))) * (1 + a)) + ((c + a) * ((1 + b) * (1 + c)))))
      have h_prob_4_pos : prob4 > 0 := by unfold prob4; linarith

    --  ideal cofactors
      let ideal_cf_0 : ℝ := (((-1 / 9) * (a ^ 2)) + (((4 / 9) * (a * b)) + (((4 / 9) * (a * c)) + (((-1 / 9) * (b ^ 2)) + (((4 / 9) * (b * c)) + (((-1 / 9) * (c ^ 2)) + (((2 / 3) * a) + (((2 / 3) * b) + (((2 / 3) * c) + 1)))))))))

    --  cone cofactors (sums of squares)
      let cone_cf_0 : ℝ := (((0 - (0 - c)) * (1)) * ((1/9) * (((-2 * a) + (b + c)))^2))
      have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith
      let cone_cf_1 : ℝ := (((0 - (0 - b)) * (1)) * ((4/9) * ((((-1 / 2) * a) + (((-1 / 2) * b) + c)))^2))
      have h_cone_cf_1_nonneg : cone_cf_1 ≥ 0 := by unfold cone_cf_1; first | positivity | linarith
      let cone_cf_2 : ℝ := (((0 - (0 - a)) * (1)) * ((1/9) * ((a + ((-2 * b) + c)))^2))
      have h_cone_cf_2_nonneg : cone_cf_2 ≥ 0 := by unfold cone_cf_2; first | positivity | linarith

    --  monoid cofactors (products of non-equalities)
      let monoid_cf_0 : ℝ := ((3 * (((1 + b) * (1 + c)) * (1 + a))) - (((((a + b) * (1 + c)) + ((b + c) * (1 + b))) * (1 + a)) + ((c + a) * ((1 + b) * (1 + c)))))
      have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

    --  Proofs for ideal products being zero
      have h_ideal_prod_0_zero : ideal_cf_0 * prob3 = 0 := by simp [prob3]; right; linarith

    --  Positivstellensatz Certificate
      let cert : ℝ := monoid_cf_0 + cone_cf_0 + cone_cf_1 + cone_cf_2 + (ideal_cf_0 * prob3)

    --  Show the certificate is identically zero using the problem constraints
      have h_cert_key : cert = 0 := by unfold cert prob3 ideal_cf_0 cone_cf_0 cone_cf_1 cone_cf_2 monoid_cf_0; linarith

    --  Show the certificate is non_zero, which is the key contradiction
      have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

      tauto

    simp_all

------------------------------------------------------------------------------------
------------------------------------------------------------------------------------

theorem ex5_human (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 3) :
    3 ≤ (a + b) / (1 + b) + (b + c) / (1 + c) + (c + a) / (1 + a) := by
  -- Prove that denominators are positive
  have h1 : 1 + a > 0 := by linarith
  have h2 : 1 + b > 0 := by linarith
  have h3 : 1 + c > 0 := by linarith

  -- Reformulate the problem as showing that the difference with 3 is non-negative
  have h : (a + b) / (1 + b) + (b + c) / (1 + c) + (c + a) / (1 + a) - 3 ≥ 0 := by
    -- Express the difference as a single fraction
    have h4 : (a + b) / (1 + b) + (b + c) / (1 + c) + (c + a) / (1 + a) - 3 =
        ((a + b) * (1 + c) * (1 + a) + (b + c) * (1 + a) * (1 + b) + (c + a) * (1 + b) * (1 + c) - 3 * (1 + a) * (1 + b) * (1 + c)) /
        ((1 + a) * (1 + b) * (1 + c)) := by
      -- Simplify using field operations and ring properties
      field_simp
      ring

    -- Use the reformulated expression
    rw [h4]

    -- Prove that the fraction is non-negative
    apply div_nonneg
    -- Use non-linear arithmetic with various square non-negativity facts
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      hsum, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
    -- Prove that the denominator is positive
    positivity

  -- Conclude the proof using linear arithmetic
  linarith
