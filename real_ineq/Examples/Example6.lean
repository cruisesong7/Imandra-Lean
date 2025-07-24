/-This example is from another Math competition (JBMO),
we showcase the imandra-geo ability to close the goal and compare with a Lean-user's manual proof.-/

import Mathlib
import RealIneq.Horn
import RealIneq.NormHorn

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/- Let $x, y, z$ be positive real numbers. Prove that:
$$
\frac{x+2 y}{z+2 x+3 y}+\frac{y+2 z}{x+2 y+3 z}+\frac{z+2 x}{y+2 z+3 x} \leq \frac{3}{2}
$$ -/
theorem ex6_imandra
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    (x + 2 * y) / (z + 2 * x + 3 * y) +
    (y + 2 * z) / (x + 2 * y + 3 * z) +
    (z + 2 * x) / (y + 2 * z + 3 * x) ≤ 3 / 2 := by
  -- field_simp
  -- rw[div_le_div_iff₀ (by positivity) (by positivity)]
  norm_horn
  horn_all
  have imandra_proof : ∀ x y z : ℝ, ((0 < x) → (0 < y) → (0 < z) → (((((((x + (2 * y)) * ((x + (2 * y)) + (3 * z))) + ((y + (2 * z)) * ((z + (2 * x)) + (3 * y)))) * ((y + (2 * z)) + (3 * x))) + ((z + (2 * x)) * (((z + (2 * x)) + (3 * y)) * ((x + (2 * y)) + (3 * z))))) * 2) ≤ (3 * ((((z + (2 * x)) + (3 * y)) * ((x + (2 * y)) + (3 * z))) * ((y + (2 * z)) + (3 * x)))))) := by
    intros x y z
    by_contra! goal
    rcases goal with ⟨h1, h2, h3, h4⟩

  --  problem polynomials and their properties from the goal
    let prob0 : ℝ := (0 - (0 - x))
    have h_prob_0_pos : prob0 > 0 := by unfold prob0; linarith
    let prob1 : ℝ := (0 - (0 - y))
    have h_prob_1_pos : prob1 > 0 := by unfold prob1; linarith
    let prob2 : ℝ := (0 - (0 - z))
    have h_prob_2_pos : prob2 > 0 := by unfold prob2; linarith
    let prob3 : ℝ := (((((((x + (2 * y)) * ((x + (2 * y)) + (3 * z))) + ((y + (2 * z)) * ((z + (2 * x)) + (3 * y)))) * ((y + (2 * z)) + (3 * x))) + ((z + (2 * x)) * (((z + (2 * x)) + (3 * y)) * ((x + (2 * y)) + (3 * z))))) * 2) - (3 * ((((z + (2 * x)) + (3 * y)) * ((x + (2 * y)) + (3 * z))) * ((y + (2 * z)) + (3 * x)))))
    have h_prob_3_pos : prob3 > 0 := by unfold prob3; linarith

  --  ideal cofactors

  --  cone cofactors (sums of squares)
    let cone_cf_0 : ℝ := (((0 - (0 - z)) * (1)) * (((4) * ((((-1 / 4) * x) + (((-3 / 4) * y) + z)))^2) + ((11/4) * ((x + (-1 * y)))^2)))
    have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith
    let cone_cf_1 : ℝ := (((0 - (0 - y)) * (1)) * (((3) * ((((-2 / 3) * x) + (((-1 / 3) * y) + z)))^2) + ((11/3) * ((x + (-1 * y)))^2)))
    have h_cone_cf_1_nonneg : cone_cf_1 ≥ 0 := by unfold cone_cf_1; first | positivity | linarith
    let cone_cf_2 : ℝ := (((0 - (0 - x)) * (1)) * (((5) * ((((-3 / 5) * x) + (((-2 / 5) * y) + z)))^2) + ((11/5) * ((x + (-1 * y)))^2)))
    have h_cone_cf_2_nonneg : cone_cf_2 ≥ 0 := by unfold cone_cf_2; first | positivity | linarith

  --  monoid cofactors (products of non-equalities)
    let monoid_cf_0 : ℝ := (((((((x + (2 * y)) * ((x + (2 * y)) + (3 * z))) + ((y + (2 * z)) * ((z + (2 * x)) + (3 * y)))) * ((y + (2 * z)) + (3 * x))) + ((z + (2 * x)) * (((z + (2 * x)) + (3 * y)) * ((x + (2 * y)) + (3 * z))))) * 2) - (3 * ((((z + (2 * x)) + (3 * y)) * ((x + (2 * y)) + (3 * z))) * ((y + (2 * z)) + (3 * x)))))
    have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

  --  Proofs for ideal products being zero

  --  Positivstellensatz Certificate
    let cert : ℝ := monoid_cf_0 + cone_cf_0 + cone_cf_1 + cone_cf_2

  --  Show the certificate is identically zero using the problem constraints
    have h_cert_key : cert = 0 := by unfold cert cone_cf_0 cone_cf_1 cone_cf_2 monoid_cf_0; linarith

  --  Show the certificate is non_zero, which is the key contradiction
    have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

    tauto
  simp_all

------------------------------------------------------------------------------------
------------------------------------------------------------------------------------

theorem ex6_human
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    (x + 2 * y) / (z + 2 * x + 3 * y) +
    (y + 2 * z) / (x + 2 * y + 3 * z) +
    (z + 2 * x) / (y + 2 * z + 3 * x) ≤ 3 / 2 := by

  -- Because the inequality is homogeneous, we can take $x+y+z=1$.
  wlog h_sumxyz : x + y + z = 1
  . convert this (x / (x + y + z)) (y / (x + y + z)) (z / (x + y + z)) ?_ ?_ ?_ ?_ using 1
    any_goals positivity
    any_goals field_simp

  -- Denote $x+2 y=a, y+2 z=b, z+2 x=c$.
  let a := x + 2 * y
  let b := y + 2 * z
  let c := z + 2 * x

  -- Hence, $a+b+c=3(x+y+z)=3$.
  have h_sumabc : a + b + c = 3 := by
    dsimp [a, b, c]
    linarith

  -- We have $(k-1)^{2} \geq 0 \Leftrightarrow(k+1)^{2} \geq 4 k \Leftrightarrow \frac{k+1}{4} \geq \frac{k}{k+1}$ for all $k>0$.
  have r1 {k : ℝ} : 0 < k → k / (k + 1) ≤ (k + 1) / 4 := by
    intro h_kpos

    -- $(k+1)^{2} \geq 4 k$
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mp
    simp_rw [div_inv_eq_mul, ← pow_two]

    -- (k-1)^{2} \geq 0
    apply sub_nonneg.mp
    rw [show (k + 1) ^ 2 - k * 4 = (k - 1) ^ 2 by ring]
    positivity

  -- Hence $\sum_{\text {cyc }} \frac{x+2 y}{z+2 x+3 y}=\sum \frac{a}{1+a} \leq \sum \frac{a+1}{4}=\frac{a+b+c+3}{4}=\frac{3}{2}$.
  calc
    -- $=\sum \frac{a}{1+a}$
    _ = a / (1 + a) + b / (1 + b) + c / (1 + c) := by
      simp only [a, b, c, ← h_sumxyz]
      ring
    -- $\leq \sum \frac{a+1}{4}$
    _ ≤ (a + 1) / 4 + (b + 1) / 4 + (c + 1) / 4 := by
      have h1 := r1 (show 0 < a by positivity)
      have h2 := r1 (show 0 < b by positivity)
      have h3 := r1 (show 0 < c by positivity)
      linear_combination h1 + h2 + h3
    -- $=\frac{a+b+c+3}{4}$
    _ = (a + b + c + 3) / 4 := by
      ring_nf
    -- $=\frac{3}{2}$
    _ = 3 / 2 := by
      norm_num [h_sumabc]
