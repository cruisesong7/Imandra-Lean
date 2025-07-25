import Mathlib
import RealIneq.Horn
import RealIneq.NormHorn

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem prob0 : ∀ x a b c : ℝ, ((((a * x^2) + (b * x) + c) = 0) → (((b * b) - (4 * a * c)) ≥ 0)) := by
  intros x a b c h1
  horn[h1]
  have imandra_proof : ∀ a b c x : ℝ, (((((a * (x ^ 2)) + (b * x)) + c) = 0) → (((b * b) - ((4 * a) * c)) ≥ 0)) := by
    intros a b c x
    by_contra! goal
    rcases goal with ⟨h1, h2⟩

  --  problem polynomials and their properties from the goal
    let prob0 : ℝ := (((a * (x ^ 2)) + (b * x)) + c)
    let prob1 : ℝ := (0 - ((b * b) - ((4 * a) * c)))
    have h_prob_1_pos : prob1 > 0 := by unfold prob1; linarith

  --  ideal cofactors
    let ideal_cf_0 : ℝ := (-4 * a)

  --  cone cofactors (sums of squares)
    let cone_cf_0 : ℝ := ((1) * ((1) * (((2 * (a * x)) + b))^2))
    have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith

  --  monoid cofactors (products of non-equalities)
    let monoid_cf_0 : ℝ := (0 - ((b * b) - ((4 * a) * c)))
    have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

  --  Proofs for ideal products being zero
    have h_ideal_prod_0_zero : ideal_cf_0 * prob0 = 0 := by simp [prob0]; right; linarith

  --  Positivstellensatz Certificate
    let cert : ℝ := monoid_cf_0 + cone_cf_0 + (ideal_cf_0 * prob0)

  --  Show the certificate is identically zero using the problem constraints
    have h_cert_key : cert = 0 := by unfold cert prob0 ideal_cf_0 cone_cf_0 monoid_cf_0; linarith

  --  Show the certificate is non_zero, which is the key contradiction
    have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

    tauto

  apply imandra_proof a b c x h1


theorem prob0' : ∀ a b c x: ℝ, a > 0 → b > 0 → c > 0 → ((((√a) * x^2) + (√b * x) + √c) = 0) → (((√b * √b) - (4 * (√a) * √c)) ≥ 0) := by
  intros a b c x ha hb hc h
  norm_horn at *
  horn_all
  have imandra_proof : ∀ a a_sqrt b b_sqrt c c_sqrt x : ℝ, ((0 < c) → (0 < b) → (0 < a) → ((c_sqrt ^ 2) = c) → ((a_sqrt ^ 2) = a) → ((((a_sqrt * (x ^ 2)) + (b_sqrt * x)) + c_sqrt) = 0) → ((b_sqrt ^ 2) = b) → (((4 * a_sqrt) * c_sqrt) ≤ b)) := by
    intros a a_sqrt b b_sqrt c c_sqrt x
    by_contra! goal
    rcases goal with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

  --  problem polynomials and their properties from the goal
    let prob0 : ℝ := (0 - (0 - c))
    have h_prob_0_pos : prob0 > 0 := by unfold prob0; linarith
    let prob1 : ℝ := (0 - (0 - b))
    have h_prob_1_pos : prob1 > 0 := by unfold prob1; linarith
    let prob2 : ℝ := (0 - (0 - a))
    have h_prob_2_pos : prob2 > 0 := by unfold prob2; linarith
    let prob3 : ℝ := ((c_sqrt ^ 2) - c)
    let prob4 : ℝ := ((a_sqrt ^ 2) - a)
    let prob5 : ℝ := (((a_sqrt * (x ^ 2)) + (b_sqrt * x)) + c_sqrt)
    let prob6 : ℝ := ((b_sqrt ^ 2) - b)
    let prob7 : ℝ := (((4 * a_sqrt) * c_sqrt) - b)
    have h_prob_7_pos : prob7 > 0 := by unfold prob7; linarith

  --  ideal cofactors
    let ideal_cf_0 : ℝ := ((6 * (a_sqrt ^ 2)) + ((5 * (b_sqrt ^ 2)) + ((-6 * a) + (-5 * b))))
    let ideal_cf_1 : ℝ := ((2 * (b_sqrt ^ 2)) + ((-6 * (c_sqrt ^ 2)) + ((-2 * b) + (6 * c))))
    let ideal_cf_2 : ℝ := (-4 * a_sqrt)
    let ideal_cf_3 : ℝ := ((-2 * (a_sqrt ^ 2)) + ((-5 * (c_sqrt ^ 2)) + ((2 * a) + ((5 * c) + -1))))

  --  cone cofactors (sums of squares)
    let cone_cf_0 : ℝ := ((1) * ((1) * (((2 * (a_sqrt * x)) + b_sqrt))^2))
    have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith

  --  monoid cofactors (products of non-equalities)
    let monoid_cf_0 : ℝ := (((4 * a_sqrt) * c_sqrt) - b)
    have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

  --  Proofs for ideal products being zero
    have h_ideal_prod_0_zero : ideal_cf_0 * prob3 = 0 := by simp [prob3]; right; linarith
    have h_ideal_prod_1_zero : ideal_cf_1 * prob4 = 0 := by simp [prob4]; right; linarith
    have h_ideal_prod_2_zero : ideal_cf_2 * prob5 = 0 := by simp [prob5]; right; linarith
    have h_ideal_prod_3_zero : ideal_cf_3 * prob6 = 0 := by simp [prob6]; right; linarith

  --  Positivstellensatz Certificate
    let cert : ℝ := monoid_cf_0 + cone_cf_0 + (ideal_cf_0 * prob3) + (ideal_cf_1 * prob4) + (ideal_cf_2 * prob5) + (ideal_cf_3 * prob6)

  --  Show the certificate is identically zero using the problem constraints
    have h_cert_key : cert = 0 := by unfold cert prob3 prob4 prob5 prob6 ideal_cf_0 ideal_cf_1 ideal_cf_2 ideal_cf_3 cone_cf_0 monoid_cf_0; linarith

  --  Show the certificate is non_zero, which is the key contradiction
    have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

    tauto
  specialize imandra_proof a a_sqrt b b_sqrt c c_sqrt x
  simp_all

theorem prob0'' : ∀ a b c x: ℝ, a > 0 → b > 0 → c > 0 → ((((1 / a ) * x^2) + (1 / b * x) + √c) = 0) → (((1 / b * 1 / b) - (4 * (1 / a) * √c)) ≥ 0) := by
  intros a b c x ha hb hc h
  norm_horn at *
  horn_all
  have imandra_proof : ∀ a b c c_sqrt x : ℝ, ((0 < c) → (0 < b) → (0 < a) → (((((x ^ 2) * b) + (x * a)) + (c_sqrt * (a * b))) = 0) → ((c_sqrt ^ 2) = c) → (((b * b) * (4 * c_sqrt)) ≤ a)) := by
    intros a b c c_sqrt x
    by_contra! goal
    rcases goal with ⟨h1, h2, h3, h4, h5, h6⟩

  --  problem polynomials and their properties from the goal
    let prob0 : ℝ := (0 - (0 - c))
    have h_prob_0_pos : prob0 > 0 := by unfold prob0; linarith
    let prob1 : ℝ := (0 - (0 - b))
    have h_prob_1_pos : prob1 > 0 := by unfold prob1; linarith
    let prob2 : ℝ := (0 - (0 - a))
    have h_prob_2_pos : prob2 > 0 := by unfold prob2; linarith
    let prob3 : ℝ := ((((x ^ 2) * b) + (x * a)) + (c_sqrt * (a * b)))
    let prob4 : ℝ := ((c_sqrt ^ 2) - c)
    let prob5 : ℝ := (((b * b) * (4 * c_sqrt)) - a)
    have h_prob_5_pos : prob5 > 0 := by unfold prob5; linarith

  --  ideal cofactors
    let ideal_cf_0 : ℝ := (-4 * b)
    let ideal_cf_1 : ℝ := 0

  --  cone cofactors (sums of squares)
    let cone_cf_0 : ℝ := ((1) * ((1) * (((2 * (b * x)) + a))^2))
    have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith

  --  monoid cofactors (products of non-equalities)
    let monoid_cf_0 : ℝ := (0 - (0 - a))
    have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity
    let monoid_cf_1 : ℝ := (((b * b) * (4 * c_sqrt)) - a)
    have h_monoid_cf_1_pos : monoid_cf_1 > 0 := by unfold monoid_cf_1; positivity

  --  Proofs for ideal products being zero
    have h_ideal_prod_0_zero : ideal_cf_0 * prob3 = 0 := by simp [prob3]; right; linarith
    have h_ideal_prod_1_zero : ideal_cf_1 * prob4 = 0 := by simp [prob4]; right; linarith

  --  Positivstellensatz Certificate
    let cert : ℝ := (monoid_cf_0 * monoid_cf_1) + cone_cf_0 + (ideal_cf_0 * prob3) + (ideal_cf_1 * prob4)

  --  Show the certificate is identically zero using the problem constraints
    have h_cert_key : cert = 0 := by unfold cert prob3 prob4 ideal_cf_0 ideal_cf_1 cone_cf_0 monoid_cf_0 monoid_cf_1; linarith

  --  Show the certificate is non_zero, which is the key contradiction
    have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

    tauto
  specialize imandra_proof a b c c_sqrt x
  simp_all
