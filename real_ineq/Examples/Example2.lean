import Mathlib
import RealIneq.Horn

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem prob6 : ∀ a b c x: ℝ, a ≥ 0 → b ≥ 0 → c ≥ 0 → c * (2 * a + b)^3 ≤ 27 * x → c * a^2 * b ≤ x := by
  intros a b c x h1 h2 h3 h4
  horn [h1,h2,h3,h4]
  have imandra_proof : ∀ a b c x : ℝ, ((a ≥ 0) → (b ≥ 0) → (c ≥ 0) → ((c * (((2 * a) + b) ^ 3)) ≤ (27 * x)) → (((c * (a ^ 2)) * b) ≤ x)) := by
    intros a b c x
    by_contra! goal
    rcases goal with ⟨h1, h2, h3, h4, h5⟩

  --  problem polynomials and their properties from the goal
    let prob0 : ℝ := a
    have h_prob_0_nonneg : prob0 ≥ 0 := by unfold prob0; linarith
    let prob1 : ℝ := b
    have h_prob_1_nonneg : prob1 ≥ 0 := by unfold prob1; linarith
    let prob2 : ℝ := c
    have h_prob_2_nonneg : prob2 ≥ 0 := by unfold prob2; linarith
    let prob3 : ℝ := (0 - ((c * (((2 * a) + b) ^ 3)) - (27 * x)))
    have h_prob_3_nonneg : prob3 ≥ 0 := by unfold prob3; linarith
    let prob4 : ℝ := (((c * (a ^ 2)) * b) - x)
    have h_prob_4_pos : prob4 > 0 := by unfold prob4; linarith

  --  ideal cofactors

  --  cone cofactors (sums of squares)
    let cone_cf_0 : ℝ := (((((c * (a ^ 2)) * b) - x) * (1)) * ((1/26) * (1)^2))
    have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith
    let cone_cf_1 : ℝ := (((0 - ((c * (((2 * a) + b) ^ 3)) - (27 * x))) * (1)) * ((1/26) * (1)^2))
    have h_cone_cf_1_nonneg : cone_cf_1 ≥ 0 := by unfold cone_cf_1; first | positivity | linarith
    let cone_cf_2 : ℝ := ((b * (c * (1))) * ((1/26) * (((-1 * a) + b))^2))
    have h_cone_cf_2_nonneg : cone_cf_2 ≥ 0 := by unfold cone_cf_2; first | positivity | linarith
    let cone_cf_3 : ℝ := ((a * (c * (1))) * ((4/13) * (((-1 * a) + b))^2))
    have h_cone_cf_3_nonneg : cone_cf_3 ≥ 0 := by unfold cone_cf_3; first | positivity | linarith

  --  monoid cofactors (products of non-equalities)
    let monoid_cf_0 : ℝ := (((c * (a ^ 2)) * b) - x)
    have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

  --  Proofs for ideal products being zero

  --  Positivstellensatz Certificate
    let cert : ℝ := monoid_cf_0 + cone_cf_0 + cone_cf_1 + cone_cf_2 + cone_cf_3

  --  Show the certificate is identically zero using the problem constraints
    have h_cert_key : cert = 0 := by unfold cert cone_cf_0 cone_cf_1 cone_cf_2 cone_cf_3 monoid_cf_0; linarith

  --  Show the certificate is non_zero, which is the key contradiction
    have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

    tauto

  simp_all  -- or alternatively, apply imandra_proof a b c x h1 h2 h3 h4
