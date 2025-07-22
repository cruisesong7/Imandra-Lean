/-This example is from another Math competition (IMO),
we showcase the imandra-geo ability to close the goal and compare with a Lean-user's manual proof.-/

import Mathlib
import RealIneq.Horn

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-For all real numbers $x, y, z$, prove that:

\[
\left( (x-y)^2 + (x-z)^2 + (y-z)^2 \right)^3 \ge 54 \left[ (x-y)(x-z)(y-z) \right]^2
\]

Determine the conditions under which equality holds.-/
set_option maxHeartbeats 2000000
theorem ex7_imandra (x y z : ℝ) : ((x - y)^2 + (x - z)^2 + (y - z)^2)^3 ≥ 54*((x - y)*(x - z)*(y - z))^2 ∧ (((x - y)^2 + (x - z)^2 + (y - z)^2)^3 = 54*((x - y)*(x - z)*(y - z))^2 ↔ ((x - y = y - z) ∨ x - y = -2 * (y - z) ∨ -2 * (x - y) = y - z))  := by
  constructor
  · horn
    have imandra_proof : ∀ x y z : ℝ, ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) ≥ (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2))) := by
      intros x y z
      by_contra! goal

    --  problem polynomials and their properties from the goal
      let prob0 : ℝ := (0 - ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) - (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2))))
      have h_prob_0_pos : prob0 > 0 := by unfold prob0; linarith

    --  ideal cofactors

    --  cone cofactors (sums of squares)
      let cone_cf_0 : ℝ := ((1) * ((8) * (((x ^ 3) + (((-3 / 2) * ((x ^ 2) * y)) + (((-3 / 2) * ((x ^ 2) * z)) + (((-3 / 2) * (x * (y ^ 2))) + ((6 * (x * (y * z))) + (((-3 / 2) * (x * (z ^ 2))) + ((y ^ 3) + (((-3 / 2) * ((y ^ 2) * z)) + (((-3 / 2) * (y * (z ^ 2))) + (z ^ 3)))))))))))^2))
      have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith

    --  monoid cofactors (products of non-equalities)
      let monoid_cf_0 : ℝ := (0 - ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) - (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2))))
      have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; linarith

    --  Proofs for ideal products being zero

    --  Positivstellensatz Certificate
      let cert : ℝ := monoid_cf_0 + cone_cf_0

    --  Show the certificate is identically zero using the problem constraints
      have h_cert_key : cert = 0 := by unfold cert cone_cf_0 monoid_cf_0; linarith

    --  Show the certificate is non_zero, which is the key contradiction
      have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

      tauto
    simp_all
  · constructor
    · contrapose!
      rintro ⟨h1,h2,h3⟩
      horn_all
      have imandra_proof : ∀ x y z : ℝ, (((x - y) ≠ (y - z)) → ((x - y) ≠ ((-2) * (y - z))) → (((-2) * (x - y)) ≠ (y - z)) → ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) ≠ (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2)))) := by
        intros x y z
        by_contra! goal
        rcases goal with ⟨h1, h2, h3, h4⟩

      --  problem polynomials and their properties from the goal
        let prob0 : ℝ := ((x - y) - (y - z))
        have h_prob_0_ne_zero : prob0 ≠ 0 := by unfold prob0; rcases lt_or_gt_of_ne h1 with _ | _ <;> linarith
        let prob1 : ℝ := ((x - y) - ((0 - 2) * (y - z)))
        have h_prob_1_ne_zero : prob1 ≠ 0 := by unfold prob1; rcases lt_or_gt_of_ne h2 with _ | _ <;> linarith
        let prob2 : ℝ := (((0 - 2) * (x - y)) - (y - z))
        have h_prob_2_ne_zero : prob2 ≠ 0 := by unfold prob2; rcases lt_or_gt_of_ne h3 with _ | _ <;> linarith
        let prob3 : ℝ := ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) - (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2)))

      --  ideal cofactors
        let ideal_cf_0 : ℝ := (-1 / 2)

      --  cone cofactors (sums of squares)

      --  monoid cofactors (products of non-equalities)
        let monoid_cf_0 : ℝ := (((x - y) - (y - z)))^2
        have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity
        let monoid_cf_1 : ℝ := (((x - y) - ((0 - 2) * (y - z))))^2
        have h_monoid_cf_1_pos : monoid_cf_1 > 0 := by unfold monoid_cf_1; positivity
        let monoid_cf_2 : ℝ := ((((0 - 2) * (x - y)) - (y - z)))^2
        have h_monoid_cf_2_pos : monoid_cf_2 > 0 := by unfold monoid_cf_2; positivity

      --  Proofs for ideal products being zero
        have h_ideal_prod_0_zero : ideal_cf_0 * prob3 = 0 := by simp [prob3]; right; linarith

      --  Positivstellensatz Certificate
        let cert : ℝ := (monoid_cf_0 * monoid_cf_1 * monoid_cf_2) + (ideal_cf_0 * prob3)

      --  Show the certificate is identically zero using the problem constraints
        have h_cert_key : cert = 0 := by unfold cert prob3 ideal_cf_0 monoid_cf_0 monoid_cf_1 monoid_cf_2; linarith

      --  Show the certificate is non_zero, which is the key contradiction
        have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

        tauto

      simp_all
    · intro h
      rcases h with h1|h2|h3
      · horn_all
        have imandra_proof : ∀ x y z : ℝ, (((x - y) = (y - z)) → ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) = (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2)))) := by
          intros x y z
          by_contra! goal
          rcases goal with ⟨h1, h2⟩

        --  problem polynomials and their properties from the goal
          let prob0 : ℝ := ((x - y) - (y - z))
          let prob1 : ℝ := ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) - (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2)))
          have h_prob_1_ne_zero : prob1 ≠ 0 := by unfold prob1; rcases lt_or_gt_of_ne h2 with _ | _ <;> linarith

        --  ideal cofactors
          let ideal_cf_0 : ℝ := ((-64 * (x ^ 11)) + ((256 * ((x ^ 10) * y)) + ((448 * ((x ^ 10) * z)) + ((32 * ((x ^ 9) * (y ^ 2))) + ((-2624 * ((x ^ 9) * (y * z))) + ((-928 * ((x ^ 9) * (z ^ 2))) + ((-1056 * ((x ^ 8) * (y ^ 3))) + ((2880 * ((x ^ 8) * ((y ^ 2) * z))) + ((8928 * ((x ^ 8) * (y * (z ^ 2)))) + ((-192 * ((x ^ 8) * (z ^ 3))) + ((444 * ((x ^ 7) * (y ^ 4))) + ((6672 * ((x ^ 7) * ((y ^ 3) * z))) + ((-21528 * ((x ^ 7) * ((y ^ 2) * (z ^ 2)))) + ((-9456 * ((x ^ 7) * (y * (z ^ 3)))) + ((2748 * ((x ^ 7) * (z ^ 4))) + ((1608 * ((x ^ 6) * (y ^ 5))) + ((-11148 * ((x ^ 6) * ((y ^ 4) * z))) + ((-1056 * ((x ^ 6) * ((y ^ 3) * (z ^ 2)))) + ((51288 * ((x ^ 6) * ((y ^ 2) * (z ^ 3)))) + ((-9096 * ((x ^ 6) * (y * (z ^ 4)))) + ((-2028 * ((x ^ 6) * (z ^ 5))) + ((-840 * ((x ^ 5) * (y ^ 6))) + ((-4608 * ((x ^ 5) * ((y ^ 5) * z))) + ((44964 * ((x ^ 5) * ((y ^ 4) * (z ^ 2)))) + ((-57840 * ((x ^ 5) * ((y ^ 3) * (z ^ 3)))) + ((-33552 * ((x ^ 5) * ((y ^ 2) * (z ^ 4)))) + ((24336 * ((x ^ 5) * (y * (z ^ 5)))) + ((-2028 * ((x ^ 5) * (z ^ 6))) + ((-960 * ((x ^ 4) * (y ^ 7))) + ((10920 * ((x ^ 4) * ((y ^ 6) * z))) + ((-21240 * ((x ^ 4) * ((y ^ 5) * (z ^ 2)))) + ((-39540 * ((x ^ 4) * ((y ^ 4) * (z ^ 3)))) + ((111840 * ((x ^ 4) * ((y ^ 3) * (z ^ 4)))) + ((-33552 * ((x ^ 4) * ((y ^ 2) * (z ^ 5)))) + ((-9096 * ((x ^ 4) * (y * (z ^ 6)))) + ((2748 * ((x ^ 4) * (z ^ 7))) + ((636 * ((x ^ 3) * (y ^ 8))) + ((-1248 * ((x ^ 3) * ((y ^ 7) * z))) + ((-17472 * ((x ^ 3) * ((y ^ 6) * (z ^ 2)))) + ((63264 * ((x ^ 3) * ((y ^ 5) * (z ^ 3)))) + ((-39540 * ((x ^ 3) * ((y ^ 4) * (z ^ 4)))) + ((-57840 * ((x ^ 3) * ((y ^ 3) * (z ^ 5)))) + ((51288 * ((x ^ 3) * ((y ^ 2) * (z ^ 6)))) + ((-9456 * ((x ^ 3) * (y * (z ^ 7)))) + ((-192 * ((x ^ 3) * (z ^ 8))) + ((152 * ((x ^ 2) * (y ^ 9))) + ((-3276 * ((x ^ 2) * ((y ^ 8) * z))) + ((14976 * ((x ^ 2) * ((y ^ 7) * (z ^ 2)))) + ((-17472 * ((x ^ 2) * ((y ^ 6) * (z ^ 3)))) + ((-21240 * ((x ^ 2) * ((y ^ 5) * (z ^ 4)))) + ((44964 * ((x ^ 2) * ((y ^ 4) * (z ^ 5)))) + ((-1056 * ((x ^ 2) * ((y ^ 3) * (z ^ 6)))) + ((-21528 * ((x ^ 2) * ((y ^ 2) * (z ^ 7)))) + ((8928 * ((x ^ 2) * (y * (z ^ 8)))) + ((-928 * ((x ^ 2) * (z ^ 9))) + ((-176 * (x * (y ^ 10))) + ((1456 * (x * ((y ^ 9) * z))) + ((-3276 * (x * ((y ^ 8) * (z ^ 2)))) + ((-1248 * (x * ((y ^ 7) * (z ^ 3)))) + ((10920 * (x * ((y ^ 6) * (z ^ 4)))) + ((-4608 * (x * ((y ^ 5) * (z ^ 5)))) + ((-11148 * (x * ((y ^ 4) * (z ^ 6)))) + ((6672 * (x * ((y ^ 3) * (z ^ 7)))) + ((2880 * (x * ((y ^ 2) * (z ^ 8)))) + ((-2624 * (x * (y * (z ^ 9)))) + ((448 * (x * (z ^ 10))) + ((32 * (y ^ 11)) + ((-176 * ((y ^ 10) * z)) + ((152 * ((y ^ 9) * (z ^ 2))) + ((636 * ((y ^ 8) * (z ^ 3))) + ((-960 * ((y ^ 7) * (z ^ 4))) + ((-840 * ((y ^ 6) * (z ^ 5))) + ((1608 * ((y ^ 5) * (z ^ 6))) + ((444 * ((y ^ 4) * (z ^ 7))) + ((-1056 * ((y ^ 3) * (z ^ 8))) + ((32 * ((y ^ 2) * (z ^ 9))) + ((256 * (y * (z ^ 10))) + (-64 * (z ^ 11)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

        --  cone cofactors (sums of squares)

        --  monoid cofactors (products of non-equalities)
          let monoid_cf_0 : ℝ := (((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) - (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2))))^2
          have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

        --  Proofs for ideal products being zero
          have h_ideal_prod_0_zero : ideal_cf_0 * prob0 = 0 := by simp [prob0]; right; linarith

        --  Positivstellensatz Certificate
          let cert : ℝ := monoid_cf_0 + (ideal_cf_0 * prob0)

        --  Show the certificate is identically zero using the problem constraints
          have h_cert_key : cert = 0 := by unfold cert prob0 ideal_cf_0 monoid_cf_0; linarith

        --  Show the certificate is non_zero, which is the key contradiction
          have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

          tauto
        apply imandra_proof x y z h1
      · horn_all
        have imandra_proof : ∀ x y z : ℝ, (((x - y) = ((-2) * (y - z))) → ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) = (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2)))) := by
          intros x y z
          by_contra! goal
          rcases goal with ⟨h1, h2⟩

        --  problem polynomials and their properties from the goal
          let prob0 : ℝ := ((x - y) - ((0 - 2) * (y - z)))
          let prob1 : ℝ := ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) - (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2)))
          have h_prob_1_ne_zero : prob1 ≠ 0 := by unfold prob1; rcases lt_or_gt_of_ne h2 with _ | _ <;> linarith

        --  ideal cofactors
          let ideal_cf_0 : ℝ := ((-64 * (x ^ 11)) + ((448 * ((x ^ 10) * y)) + ((256 * ((x ^ 10) * z)) + ((-928 * ((x ^ 9) * (y ^ 2))) + ((-2624 * ((x ^ 9) * (y * z))) + ((32 * ((x ^ 9) * (z ^ 2))) + ((-192 * ((x ^ 8) * (y ^ 3))) + ((8928 * ((x ^ 8) * ((y ^ 2) * z))) + ((2880 * ((x ^ 8) * (y * (z ^ 2)))) + ((-1056 * ((x ^ 8) * (z ^ 3))) + ((2748 * ((x ^ 7) * (y ^ 4))) + ((-9456 * ((x ^ 7) * ((y ^ 3) * z))) + ((-21528 * ((x ^ 7) * ((y ^ 2) * (z ^ 2)))) + ((6672 * ((x ^ 7) * (y * (z ^ 3)))) + ((444 * ((x ^ 7) * (z ^ 4))) + ((-2028 * ((x ^ 6) * (y ^ 5))) + ((-9096 * ((x ^ 6) * ((y ^ 4) * z))) + ((51288 * ((x ^ 6) * ((y ^ 3) * (z ^ 2)))) + ((-1056 * ((x ^ 6) * ((y ^ 2) * (z ^ 3)))) + ((-11148 * ((x ^ 6) * (y * (z ^ 4)))) + ((1608 * ((x ^ 6) * (z ^ 5))) + ((-2028 * ((x ^ 5) * (y ^ 6))) + ((24336 * ((x ^ 5) * ((y ^ 5) * z))) + ((-33552 * ((x ^ 5) * ((y ^ 4) * (z ^ 2)))) + ((-57840 * ((x ^ 5) * ((y ^ 3) * (z ^ 3)))) + ((44964 * ((x ^ 5) * ((y ^ 2) * (z ^ 4)))) + ((-4608 * ((x ^ 5) * (y * (z ^ 5)))) + ((-840 * ((x ^ 5) * (z ^ 6))) + ((2748 * ((x ^ 4) * (y ^ 7))) + ((-9096 * ((x ^ 4) * ((y ^ 6) * z))) + ((-33552 * ((x ^ 4) * ((y ^ 5) * (z ^ 2)))) + ((111840 * ((x ^ 4) * ((y ^ 4) * (z ^ 3)))) + ((-39540 * ((x ^ 4) * ((y ^ 3) * (z ^ 4)))) + ((-21240 * ((x ^ 4) * ((y ^ 2) * (z ^ 5)))) + ((10920 * ((x ^ 4) * (y * (z ^ 6)))) + ((-960 * ((x ^ 4) * (z ^ 7))) + ((-192 * ((x ^ 3) * (y ^ 8))) + ((-9456 * ((x ^ 3) * ((y ^ 7) * z))) + ((51288 * ((x ^ 3) * ((y ^ 6) * (z ^ 2)))) + ((-57840 * ((x ^ 3) * ((y ^ 5) * (z ^ 3)))) + ((-39540 * ((x ^ 3) * ((y ^ 4) * (z ^ 4)))) + ((63264 * ((x ^ 3) * ((y ^ 3) * (z ^ 5)))) + ((-17472 * ((x ^ 3) * ((y ^ 2) * (z ^ 6)))) + ((-1248 * ((x ^ 3) * (y * (z ^ 7)))) + ((636 * ((x ^ 3) * (z ^ 8))) + ((-928 * ((x ^ 2) * (y ^ 9))) + ((8928 * ((x ^ 2) * ((y ^ 8) * z))) + ((-21528 * ((x ^ 2) * ((y ^ 7) * (z ^ 2)))) + ((-1056 * ((x ^ 2) * ((y ^ 6) * (z ^ 3)))) + ((44964 * ((x ^ 2) * ((y ^ 5) * (z ^ 4)))) + ((-21240 * ((x ^ 2) * ((y ^ 4) * (z ^ 5)))) + ((-17472 * ((x ^ 2) * ((y ^ 3) * (z ^ 6)))) + ((14976 * ((x ^ 2) * ((y ^ 2) * (z ^ 7)))) + ((-3276 * ((x ^ 2) * (y * (z ^ 8)))) + ((152 * ((x ^ 2) * (z ^ 9))) + ((448 * (x * (y ^ 10))) + ((-2624 * (x * ((y ^ 9) * z))) + ((2880 * (x * ((y ^ 8) * (z ^ 2)))) + ((6672 * (x * ((y ^ 7) * (z ^ 3)))) + ((-11148 * (x * ((y ^ 6) * (z ^ 4)))) + ((-4608 * (x * ((y ^ 5) * (z ^ 5)))) + ((10920 * (x * ((y ^ 4) * (z ^ 6)))) + ((-1248 * (x * ((y ^ 3) * (z ^ 7)))) + ((-3276 * (x * ((y ^ 2) * (z ^ 8)))) + ((1456 * (x * (y * (z ^ 9)))) + ((-176 * (x * (z ^ 10))) + ((-64 * (y ^ 11)) + ((256 * ((y ^ 10) * z)) + ((32 * ((y ^ 9) * (z ^ 2))) + ((-1056 * ((y ^ 8) * (z ^ 3))) + ((444 * ((y ^ 7) * (z ^ 4))) + ((1608 * ((y ^ 6) * (z ^ 5))) + ((-840 * ((y ^ 5) * (z ^ 6))) + ((-960 * ((y ^ 4) * (z ^ 7))) + ((636 * ((y ^ 3) * (z ^ 8))) + ((152 * ((y ^ 2) * (z ^ 9))) + ((-176 * (y * (z ^ 10))) + (32 * (z ^ 11)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

        --  cone cofactors (sums of squares)

        --  monoid cofactors (products of non-equalities)
          let monoid_cf_0 : ℝ := (((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) - (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2))))^2
          have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

        --  Proofs for ideal products being zero
          have h_ideal_prod_0_zero : ideal_cf_0 * prob0 = 0 := by simp [prob0]; right; linarith

        --  Positivstellensatz Certificate
          let cert : ℝ := monoid_cf_0 + (ideal_cf_0 * prob0)

        --  Show the certificate is identically zero using the problem constraints
          have h_cert_key : cert = 0 := by unfold cert prob0 ideal_cf_0 monoid_cf_0; linarith

        --  Show the certificate is non_zero, which is the key contradiction
          have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

          tauto
        apply imandra_proof x y z h2
      · horn_all
        have imandra_proof : ∀ x y z : ℝ, ((((-2) * (x - y)) = (y - z)) → ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) = (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2)))) := by
          intros x y z
          by_contra! goal
          rcases goal with ⟨h1, h2⟩

        --  problem polynomials and their properties from the goal
          let prob0 : ℝ := (((0 - 2) * (x - y)) - (y - z))
          let prob1 : ℝ := ((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) - (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2)))
          have h_prob_1_ne_zero : prob1 ≠ 0 := by unfold prob1; rcases lt_or_gt_of_ne h2 with _ | _ <;> linarith

        --  ideal cofactors
          let ideal_cf_0 : ℝ := ((32 * (x ^ 11)) + ((-176 * ((x ^ 10) * y)) + ((-176 * ((x ^ 10) * z)) + ((152 * ((x ^ 9) * (y ^ 2))) + ((1456 * ((x ^ 9) * (y * z))) + ((152 * ((x ^ 9) * (z ^ 2))) + ((636 * ((x ^ 8) * (y ^ 3))) + ((-3276 * ((x ^ 8) * ((y ^ 2) * z))) + ((-3276 * ((x ^ 8) * (y * (z ^ 2)))) + ((636 * ((x ^ 8) * (z ^ 3))) + ((-960 * ((x ^ 7) * (y ^ 4))) + ((-1248 * ((x ^ 7) * ((y ^ 3) * z))) + ((14976 * ((x ^ 7) * ((y ^ 2) * (z ^ 2)))) + ((-1248 * ((x ^ 7) * (y * (z ^ 3)))) + ((-960 * ((x ^ 7) * (z ^ 4))) + ((-840 * ((x ^ 6) * (y ^ 5))) + ((10920 * ((x ^ 6) * ((y ^ 4) * z))) + ((-17472 * ((x ^ 6) * ((y ^ 3) * (z ^ 2)))) + ((-17472 * ((x ^ 6) * ((y ^ 2) * (z ^ 3)))) + ((10920 * ((x ^ 6) * (y * (z ^ 4)))) + ((-840 * ((x ^ 6) * (z ^ 5))) + ((1608 * ((x ^ 5) * (y ^ 6))) + ((-4608 * ((x ^ 5) * ((y ^ 5) * z))) + ((-21240 * ((x ^ 5) * ((y ^ 4) * (z ^ 2)))) + ((63264 * ((x ^ 5) * ((y ^ 3) * (z ^ 3)))) + ((-21240 * ((x ^ 5) * ((y ^ 2) * (z ^ 4)))) + ((-4608 * ((x ^ 5) * (y * (z ^ 5)))) + ((1608 * ((x ^ 5) * (z ^ 6))) + ((444 * ((x ^ 4) * (y ^ 7))) + ((-11148 * ((x ^ 4) * ((y ^ 6) * z))) + ((44964 * ((x ^ 4) * ((y ^ 5) * (z ^ 2)))) + ((-39540 * ((x ^ 4) * ((y ^ 4) * (z ^ 3)))) + ((-39540 * ((x ^ 4) * ((y ^ 3) * (z ^ 4)))) + ((44964 * ((x ^ 4) * ((y ^ 2) * (z ^ 5)))) + ((-11148 * ((x ^ 4) * (y * (z ^ 6)))) + ((444 * ((x ^ 4) * (z ^ 7))) + ((-1056 * ((x ^ 3) * (y ^ 8))) + ((6672 * ((x ^ 3) * ((y ^ 7) * z))) + ((-1056 * ((x ^ 3) * ((y ^ 6) * (z ^ 2)))) + ((-57840 * ((x ^ 3) * ((y ^ 5) * (z ^ 3)))) + ((111840 * ((x ^ 3) * ((y ^ 4) * (z ^ 4)))) + ((-57840 * ((x ^ 3) * ((y ^ 3) * (z ^ 5)))) + ((-1056 * ((x ^ 3) * ((y ^ 2) * (z ^ 6)))) + ((6672 * ((x ^ 3) * (y * (z ^ 7)))) + ((-1056 * ((x ^ 3) * (z ^ 8))) + ((32 * ((x ^ 2) * (y ^ 9))) + ((2880 * ((x ^ 2) * ((y ^ 8) * z))) + ((-21528 * ((x ^ 2) * ((y ^ 7) * (z ^ 2)))) + ((51288 * ((x ^ 2) * ((y ^ 6) * (z ^ 3)))) + ((-33552 * ((x ^ 2) * ((y ^ 5) * (z ^ 4)))) + ((-33552 * ((x ^ 2) * ((y ^ 4) * (z ^ 5)))) + ((51288 * ((x ^ 2) * ((y ^ 3) * (z ^ 6)))) + ((-21528 * ((x ^ 2) * ((y ^ 2) * (z ^ 7)))) + ((2880 * ((x ^ 2) * (y * (z ^ 8)))) + ((32 * ((x ^ 2) * (z ^ 9))) + ((256 * (x * (y ^ 10))) + ((-2624 * (x * ((y ^ 9) * z))) + ((8928 * (x * ((y ^ 8) * (z ^ 2)))) + ((-9456 * (x * ((y ^ 7) * (z ^ 3)))) + ((-9096 * (x * ((y ^ 6) * (z ^ 4)))) + ((24336 * (x * ((y ^ 5) * (z ^ 5)))) + ((-9096 * (x * ((y ^ 4) * (z ^ 6)))) + ((-9456 * (x * ((y ^ 3) * (z ^ 7)))) + ((8928 * (x * ((y ^ 2) * (z ^ 8)))) + ((-2624 * (x * (y * (z ^ 9)))) + ((256 * (x * (z ^ 10))) + ((-64 * (y ^ 11)) + ((448 * ((y ^ 10) * z)) + ((-928 * ((y ^ 9) * (z ^ 2))) + ((-192 * ((y ^ 8) * (z ^ 3))) + ((2748 * ((y ^ 7) * (z ^ 4))) + ((-2028 * ((y ^ 6) * (z ^ 5))) + ((-2028 * ((y ^ 5) * (z ^ 6))) + ((2748 * ((y ^ 4) * (z ^ 7))) + ((-192 * ((y ^ 3) * (z ^ 8))) + ((-928 * ((y ^ 2) * (z ^ 9))) + ((448 * (y * (z ^ 10))) + (-64 * (z ^ 11)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

        --  cone cofactors (sums of squares)

        --  monoid cofactors (products of non-equalities)
          let monoid_cf_0 : ℝ := (((((((x - y) ^ 2) + ((x - z) ^ 2)) + ((y - z) ^ 2)) ^ 3) - (54 * ((((x - y) * (x - z)) * (y - z)) ^ 2))))^2
          have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

        --  Proofs for ideal products being zero
          have h_ideal_prod_0_zero : ideal_cf_0 * prob0 = 0 := by simp [prob0]; right; linarith

        --  Positivstellensatz Certificate
          let cert : ℝ := monoid_cf_0 + (ideal_cf_0 * prob0)

        --  Show the certificate is identically zero using the problem constraints
          have h_cert_key : cert = 0 := by unfold cert prob0 ideal_cf_0 monoid_cf_0; linarith

        --  Show the certificate is non_zero, which is the key contradiction
          have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

          tauto

        apply imandra_proof x y z h3


------------------------------------------------------------------------------------
------------------------------------------------------------------------------------

theorem inequalities_613886 (x y z : ℝ) : ((x - y)^2 + (x - z)^2 + (y - z)^2)^3 ≥ 54*((x - y)*(x - z)*(y - z))^2 ∧ (((x - y)^2 + (x - z)^2 + (y - z)^2)^3 = 54*((x - y)*(x - z)*(y - z))^2 ↔ ((x - y = y - z) ∨ x - y = -2 * (y - z) ∨ -2 * (x - y) = y - z))  := by
  constructor
  · wlog hxy : y ≤ x generalizing y x with h₁
    · push_neg at hxy
      specialize h₁ y x hxy.le
      bound
    wlog hxz : z ≤ x generalizing z x with h₂
    · push_neg at hxz
      specialize h₂ x z (by linarith) hxz.le
      bound
    wlog hyz : z ≤ y generalizing z y with h₃
    · push_neg at hyz
      specialize h₃ z y (by linarith) (by linarith) hyz.le
      bound
    set a := x - y with ha₁
    set b := y - z with hb₁
    rw [show x - z = a + b by linarith]
    have ha : 0 ≤ a := by linarith
    have hb : 0 ≤ b := by linarith
    nlinarith [sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - a * b), mul_nonneg ha hb]
  · obtain ⟨a, ha₁⟩ := show ∃ a : ℝ, a = x - y by simp
    obtain ⟨b, hb₁⟩ := show ∃ b : ℝ, b = y - z by simp
    rw [←ha₁, ←hb₁, show x - z = a + b by linarith]
    constructor
    · intro hxy
      rw [show a ^ 2 + (a + b) ^ 2 + b ^ 2 = 2 * (a^2 + a * b + b^2) by ring] at hxy
      by_cases ha₂ : a = 0
      · rw [ha₂] at hxy ⊢
        ring_nf at hxy
        simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, or_false] at hxy
        simp [hxy]
      obtain ⟨t, ht₁⟩ := show ∃ k, k = b / a by simp
      have ht₂ : b = a * t := by rw [ht₁, mul_div_cancel₀ _ ha₂]
      have : (2 * (a ^ 2 + a * b + b ^ 2)) ^ 3 = a^6 * (2 * (1 + t + t^2))^3 := by
        rw [ht₂]
        ring_nf
      rw [this] at hxy
      have : 54 * (a * (a + b) * b) ^ 2 = a^6 * (54 * t^2 * (1 + t) ^ 2) := by
        rw [ht₂]
        ring_nf
      rw [this] at hxy
      simp only [mul_eq_mul_left_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, ha₂, or_false] at hxy
      have ht₃ : (t - 1)^2 * (t + 2)^2 * (2 * t + 1)^2 = 0 := by linarith
      simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, or_assoc] at ht₃
      obtain (ht₃ | ht₃ | ht₃) := ht₃
      · -- t - 1 = 0
        rw [show t = 1 by linarith, Eq.comm, div_eq_one_iff_eq ha₂] at ht₁
        simp [ht₁]
      · -- t + 2 = 0
        rw [show t = -2 by linarith, Eq.comm, div_eq_iff_mul_eq ha₂] at ht₁
        simp [ht₁]
      · -- 2 * t + 1 = 0
        rw [show t = -1 / 2 by linarith, Eq.comm, div_eq_iff_mul_eq ha₂] at ht₁
        simp only [←ht₁]
        ring_nf
        simp
    · rintro (h | h | h)
      · rw [h]
        ring_nf
      · rw [h]
        ring_nf
      · rw [←h]
        ring_nf
