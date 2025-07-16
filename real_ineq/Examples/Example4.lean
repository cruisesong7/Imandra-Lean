/-This example is from another Math competition (Baltic Way),
we showcase the imandra-geo ability to close the goal and compare with a Lean-user's manual proof.-/

import Mathlib
import RealIneq.Horn

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-A ray emanating from the vertex $A$ of the triangle $A B C$ intersects the side $B C$ at $X$ and the circumcircle of $A B C$ at $Y$. Prove that $\frac{1}{A X}+\frac{1}{X Y} \geq \frac{4}{B C}$.-/
theorem ex4_imandra (AB BC CA AX XY BX XC: ℝ )(hside : AB > 0 ∧ BC > 0 ∧ CA > 0 ∧ AX > 0 ∧ XY > 0 ∧ BX > 0 ∧ XC > 0)
(hBC : BC=BX+XC)(intersecting_chords : AX*XY=BX*XC):1/AX+1/XY ≥ 4/BC:=by
    rcases hside with ⟨AB_pos, BC_pos, CA_pos, AX_pos, XY_pos, BX_pos, XC_pos⟩
    field_simp
    rw[div_le_div_iff₀ (by positivity) (by positivity)]
    horn[AB_pos,BC_pos,CA_pos,XY_pos,BX_pos,XC_pos,hBC,intersecting_chords]
    have imandra_proof : ∀ ab ax bc bx ca xc xy : ℝ, ((ab > 0) → (bc > 0) → (ca > 0) → (xy > 0) → (bx > 0) → (xc > 0) → (bc = (bx + xc)) → ((ax * xy) = (bx * xc)) → ((4 * (ax * xy)) ≤ ((xy + ax) * bc))) := by
      intros ab ax bc bx ca xc xy
      by_contra! goal
      rcases goal with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

    --  problem polynomials and their properties from the goal
      let prob0 : ℝ := ab
      have h_prob_0_pos : prob0 > 0 := by unfold prob0; linarith
      let prob1 : ℝ := bc
      have h_prob_1_pos : prob1 > 0 := by unfold prob1; linarith
      let prob2 : ℝ := ca
      have h_prob_2_pos : prob2 > 0 := by unfold prob2; linarith
      let prob3 : ℝ := xy
      have h_prob_3_pos : prob3 > 0 := by unfold prob3; linarith
      let prob4 : ℝ := bx
      have h_prob_4_pos : prob4 > 0 := by unfold prob4; linarith
      let prob5 : ℝ := xc
      have h_prob_5_pos : prob5 > 0 := by unfold prob5; linarith
      let prob6 : ℝ := (bc - (bx + xc))
      let prob7 : ℝ := ((ax * xy) - (bx * xc))
      let prob8 : ℝ := ((4 * (ax * xy)) - ((xy + ax) * bc))
      have h_prob_8_pos : prob8 > 0 := by unfold prob8; linarith

    --  ideal cofactors
      let ideal_cf_0 : ℝ := (((-8 / 9) * (ax * xy)) + (((-1 / 9) * (bc * bx)) + (((-1 / 9) * (bc * xc)) + (((1 / 9) * (bx ^ 2)) + (((7 / 9) * (bx * xc)) + (((2 / 3) * (bx * xy)) + (((1 / 9) * (xc ^ 2)) + (((2 / 3) * (xc * xy)) + (xy ^ 2)))))))))
      let ideal_cf_1 : ℝ := (((17 / 9) * bc) + (((-8 / 9) * bx) + (((-8 / 9) * xc) + (-4 * xy))))

    --  cone cofactors (sums of squares)
      let cone_cf_0 : ℝ := ((xc * (1)) * ((1) * ((((-1 / 3) * bc) + (((-2 / 3) * bx) + (((1 / 3) * xc) + xy))))^2))
      have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith
      let cone_cf_1 : ℝ := ((bx * (1)) * ((1) * ((((-1 / 3) * bc) + (((1 / 3) * bx) + (((-2 / 3) * xc) + xy))))^2))
      have h_cone_cf_1_nonneg : cone_cf_1 ≥ 0 := by unfold cone_cf_1; first | positivity | linarith

    --  monoid cofactors (products of non-equalities)
      let monoid_cf_0 : ℝ := xy
      have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; linarith
      let monoid_cf_1 : ℝ := ((4 * (ax * xy)) - ((xy + ax) * bc))
      have h_monoid_cf_1_pos : monoid_cf_1 > 0 := by unfold monoid_cf_1; linarith

    --  Proofs for ideal products being zero
      have h_ideal_prod_0_zero : ideal_cf_0 * prob6 = 0 := by simp [prob6]; right; linarith
      have h_ideal_prod_1_zero : ideal_cf_1 * prob7 = 0 := by simp [prob7]; right; linarith

    --  Positivstellensatz Certificate
      let cert : ℝ := (monoid_cf_0 * monoid_cf_1) + cone_cf_0 + cone_cf_1 + (ideal_cf_0 * prob6) + (ideal_cf_1 * prob7)

    --  Show the certificate is identically zero using the problem constraints
      have h_cert_key : cert = 0 := by unfold cert prob6 prob7 ideal_cf_0 ideal_cf_1 cone_cf_0 cone_cf_1 monoid_cf_0 monoid_cf_1; linarith

    --  Show the certificate is non_zero, which is the key contradiction
      have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

      tauto
    apply imandra_proof AB AX BC BX CA XC XY AB_pos BC_pos CA_pos XY_pos BX_pos XC_pos hBC intersecting_chords

------------------------------------------------------------------------------------
------------------------------------------------------------------------------------

theorem ex4_human(AB BC CA AX XY BX XC: ℝ )(hside : AB > 0 ∧ BC > 0 ∧ CA > 0 ∧ AX > 0 ∧ XY > 0 ∧ BX > 0 ∧ XC > 0)
(hBC : BC=BX+XC)(intersecting_chords : AX*XY=BX*XC):1/AX+1/XY ≥ 4/BC:=by
    rcases hside with ⟨AB_pos, BC_pos, CA_pos, AX_pos, XY_pos, BX_pos, XC_pos⟩
    have h1 : BC = BX + XC := by linarith
    have h2 : AX * XY = BX * XC := by linarith

    have h3 : 1 / AX + 1 / XY = (AX + XY) / (AX * XY) := by
      field_simp [AX_pos, XY_pos]
      linarith

    have h4 : 1 / AX + 1 / XY - 4 / BC ≥ 0 := by
        have h5 : BC * (AX + XY) ≥ 4 * (AX * XY) := by
            nlinarith [sq_nonneg (AX - XY), sq_nonneg (BX - XC), sq_nonneg (AX - BX), sq_nonneg (AX - XC), sq_nonneg (XY - BX), sq_nonneg (XY - XC), mul_pos AX_pos XY_pos, mul_pos BX_pos XC_pos, hBC, intersecting_chords]

        have h6 : AX * XY > 0 := mul_pos AX_pos XY_pos
        have h7 : BC > 0 := BC_pos

        have h8 : (AX + XY) / (AX * XY) - 4 / BC ≥ 0 := by
            have h9 : AX * XY > 0 := h6
            have h10 : BC > 0 := h7

            have h11 : (AX + XY) / (AX * XY) - 4 / BC = (BC * (AX + XY) - 4 * (AX * XY)) / (AX * XY * BC) := by
                field_simp [h9, h10]
                ring

            have h12 : BC * (AX + XY) - 4 * (AX * XY) ≥ 0 := by linarith [h5]

            have h13 : AX * XY * BC > 0 := mul_pos (mul_pos AX_pos XY_pos) BC_pos

            rw [h11]
            exact div_nonneg h12 (by positivity)

        have h14 : 1 / AX + 1 / XY - 4 / BC = (AX + XY) / (AX * XY) - 4 / BC := by
            rw [h3]

        linarith [h14, h8]

    linarith [h4]
