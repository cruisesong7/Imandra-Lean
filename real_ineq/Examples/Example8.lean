/-This example is from another Math competition (French_envois),
we showcase the imandra-geo ability to close the goal and compare with a Lean-user's manual proof.-/

import Mathlib
import RealIneq.Horn
import RealIneq.NormHorn
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/- Soit $x \geqslant 0$ un réel. Montrer que :

$$
1+x^{2}+x^{6}+x^{8} \geqslant 4 x^{4}
$$

et trouver les cas d'égalité. -/

theorem ex8_imandra (x : ℝ) (hx : 0 ≤ x) : 1 + x^2 + x^6 + x^8 ≥ 4 * x^4 ∧
(1 + x^2 + x^6 + x^8 = 4 * x^4 ↔ x = 1) := by
constructor
horn_all
have imandra_proof : ∀ x : ℝ, ((0 ≤ x) → ((((1 + (x ^ 2)) + (x ^ 6)) + (x ^ 8)) ≥ (4 * (x ^ 4)))) := by
  intros x
  by_contra! goal
  rcases goal with ⟨h1, h2⟩

--  problem polynomials and their properties from the goal
  let prob0 : ℝ := (0 - (0 - x))
  have h_prob_0_nonneg : prob0 ≥ 0 := by unfold prob0; linarith
  let prob1 : ℝ := (0 - ((((1 + (x ^ 2)) + (x ^ 6)) + (x ^ 8)) - (4 * (x ^ 4))))
  have h_prob_1_pos : prob1 > 0 := by unfold prob1; linarith

--  ideal cofactors

--  cone cofactors (sums of squares)
  let cone_cf_0 : ℝ := ((1) * (((1) * (((-1 * (x ^ 4)) + 1))^2) + ((1) * (((-1 * (x ^ 3)) + x))^2)))
  have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith

--  monoid cofactors (products of non-equalities)
  let monoid_cf_0 : ℝ := (0 - ((((1 + (x ^ 2)) + (x ^ 6)) + (x ^ 8)) - (4 * (x ^ 4))))
  have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

--  Proofs for ideal products being zero

--  Positivstellensatz Certificate
  let cert : ℝ := monoid_cf_0 + cone_cf_0

--  Show the certificate is identically zero using the problem constraints
  have h_cert_key : cert = 0 := by unfold cert cone_cf_0 monoid_cf_0; linarith

--  Show the certificate is non_zero, which is the key contradiction
  have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

  tauto
simp_all
constructor
horn_all
have imandra_proof : ∀ x : ℝ, ((0 ≤ x) → ((((1 + (x ^ 2)) + (x ^ 6)) + (x ^ 8)) = (4 * (x ^ 4))) → (x = 1)) := by
  intros x
  by_contra! goal
  rcases goal with ⟨h1, h2, h3⟩

--  problem polynomials and their properties from the goal
  let prob0 : ℝ := (0 - (0 - x))
  have h_prob_0_nonneg : prob0 ≥ 0 := by unfold prob0; linarith
  let prob1 : ℝ := ((((1 + (x ^ 2)) + (x ^ 6)) + (x ^ 8)) - (4 * (x ^ 4)))
  let prob2 : ℝ := (x - 1)
  have h_prob_2_ne_zero : prob2 ≠ 0 := by unfold prob2; rcases lt_or_gt_of_ne h3 with _ | _ <;> linarith

--  ideal cofactors
  let ideal_cf_0 : ℝ := -1

--  cone cofactors (sums of squares)
  let cone_cf_0 : ℝ := ((1) * ((1) * (((-1 * (x ^ 4)) + (x ^ 3)))^2))
  have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith
  let cone_cf_1 : ℝ := (((0 - (0 - x)) * (1)) * ((2) * (((-1 * (x ^ 3)) + 1))^2))
  have h_cone_cf_1_nonneg : cone_cf_1 ≥ 0 := by unfold cone_cf_1; first | positivity | linarith

--  monoid cofactors (products of non-equalities)
  let monoid_cf_0 : ℝ := ((x - 1))^2
  have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

--  Proofs for ideal products being zero
  have h_ideal_prod_0_zero : ideal_cf_0 * prob1 = 0 := by simp [prob1]; right; linarith

--  Positivstellensatz Certificate
  let cert : ℝ := monoid_cf_0 + cone_cf_0 + cone_cf_1 + (ideal_cf_0 * prob1)

--  Show the certificate is identically zero using the problem constraints
  have h_cert_key : cert = 0 := by unfold cert prob1 ideal_cf_0 cone_cf_0 cone_cf_1 monoid_cf_0; linarith

--  Show the certificate is non_zero, which is the key contradiction
  have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

  tauto
exact imandra_proof x hx
horn_all
have imandra_proof : ∀ x : ℝ, ((0 ≤ x) → (x = 1) → ((((1 + (x ^ 2)) + (x ^ 6)) + (x ^ 8)) = (4 * (x ^ 4)))) := by
  intros x
  by_contra! goal
  rcases goal with ⟨h1, h2, h3⟩

--  problem polynomials and their properties from the goal
  let prob0 : ℝ := (0 - (0 - x))
  have h_prob_0_nonneg : prob0 ≥ 0 := by unfold prob0; linarith
  let prob1 : ℝ := (x - 1)
  let prob2 : ℝ := ((((1 + (x ^ 2)) + (x ^ 6)) + (x ^ 8)) - (4 * (x ^ 4)))
  have h_prob_2_ne_zero : prob2 ≠ 0 := by unfold prob2; rcases lt_or_gt_of_ne h3 with _ | _ <;> linarith

--  ideal cofactors
  let ideal_cf_0 : ℝ := ((-1 * (x ^ 15)) + ((-1 * (x ^ 14)) + ((-3 * (x ^ 13)) + ((-3 * (x ^ 12)) + ((4 * (x ^ 11)) + ((4 * (x ^ 10)) + ((10 * (x ^ 9)) + ((10 * (x ^ 8)) + ((-10 * (x ^ 7)) + ((-10 * (x ^ 6)) + ((-4 * (x ^ 5)) + ((-4 * (x ^ 4)) + ((3 * (x ^ 3)) + ((3 * (x ^ 2)) + (x + 1)))))))))))))))

--  cone cofactors (sums of squares)

--  monoid cofactors (products of non-equalities)
  let monoid_cf_0 : ℝ := (((((1 + (x ^ 2)) + (x ^ 6)) + (x ^ 8)) - (4 * (x ^ 4))))^2
  have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

--  Proofs for ideal products being zero
  have h_ideal_prod_0_zero : ideal_cf_0 * prob1 = 0 := by simp [prob1]; right; linarith

--  Positivstellensatz Certificate
  let cert : ℝ := monoid_cf_0 + (ideal_cf_0 * prob1)

--  Show the certificate is identically zero using the problem constraints
  have h_cert_key : cert = 0 := by unfold cert prob1 ideal_cf_0 monoid_cf_0; linarith

--  Show the certificate is non_zero, which is the key contradiction
  have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

  tauto
exact imandra_proof x hx

------------------------------------------------------------------------------------
------------------------------------------------------------------------------------

/- Soit $x \geqslant 0$ un réel. Montrer que :

$$
1+x^{2}+x^{6}+x^{8} \geqslant 4 x^{4}
$$

et trouver les cas d'égalité. -/
theorem inequalities_607249 (x : ℝ) (hx : 0 ≤ x) : 1 + x^2 + x^6 + x^8 ≥ 4 * x^4 ∧
(1 + x^2 + x^6 + x^8 = 4 * x^4 ↔ x = 1) := by
-- Prove the nonnegativity of the following squares
  have : 0 ≤ (x ^ 4 - 1) ^ 2 := by positivity
  have : 0 ≤ (x ^ 3 - x) ^ 2 := by positivity
  constructor
  -- Rearrange terms and rewrite the goal to a square sum form, then use positivity to finish
  · rw [ge_iff_le, ← sub_nonneg]; calc
      _ ≤ (x ^ 4 - 1) ^ 2 + (x ^ 3 - x) ^ 2 := by positivity
      _ = _ := by ring
-- Rearrange terms and rewrite the goal to a square sum form, then use linarith to find $x=1$
  constructor
  · intro h; rw [← sub_eq_zero] at h
    rw [show 1 + x ^ 2 + x ^ 6 + x ^ 8 - 4 * x ^ 4 = (x ^ 4 - 1) ^ 2 + (x ^ 3 - x) ^ 2 by ring] at h
    have : (x ^ 4 - 1) ^ 2 = 0 := by rw [eq_iff_le_not_lt]; constructor; all_goals linarith
    simp at this; simp [sub_eq_zero, pow_eq_one_iff_cases] at this
    cases this; assumption; linarith
  intro; simp_all; norm_num
