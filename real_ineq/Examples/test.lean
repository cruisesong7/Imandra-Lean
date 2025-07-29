import Mathlib
import RealIneq.Horn
import RealIneq.NormHorn

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

-- theorem inequalities_605500
--     (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
--     2*a/(a^2+b*c) + 2*b/(b^2+c*a) + 2*c/(c^2+a*b) ≤ a/(b*c) + b/(c*a) + c/(a*b) := by
--     -- have : a^2+b*c > 0 := by positivity
--     -- have : b^2+c*a > 0 := by positivity
--     -- have :c^2+a*b > 0 := by positivity

--     -- field_simp
--     -- rw[div_le_div_iff₀]
--     norm_horn
--     horn [ha,hb,hc]

--     sorry

-- theorem inequalities_604157 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
--     2 < 1 / (a * Real.sqrt (c ^ 2 + 1)) + 1 / (b * Real.sqrt (a ^ 2 + 1)) + 1 / (c * Real.sqrt (b ^ 2 + 1)) := by
-- field_simp[show (a * √(c ^ 2 + 1) * (b * √(a ^ 2 + 1)) * (c * √(b ^ 2 + 1))) > 0 by positivity]
-- rw[lt_div_iff₀]
-- ring_nf
-- horn[ha,hb,hc, habc]

-- theorem inequalities_1674 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
--     2 * (a + b + c)^3 ≥ 3 * (a^2 + b^2 + c^2 + a * b + b * c + c * a) *
--       Real.sqrt (3 * (a * b + b * c + c * a)) := by
--   rw[ge_iff_le]
--   rw[← mul_le_mul_right (show 0 < Real.sqrt (3 * (a * b + b * c + c * a)) by positivity)]
--   rw[mul_assoc, ← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]


/-(IMPLIES (AND (< 0 a)
          (< 0 b)
          (< 0 c)
          (= (+ (+ a b) c) 3)
          (= (EXPT x 2) a)
          (= (EXPT y 2) b)
          (= (EXPT z 2) c))
    (<= (+ (+ (* a b) (* b c)) (* c a)) (+ (+ x y) z)))-/

 /-(IMPLIES (AND (< 0 a)
          (< 0 b)
          (< 0 c)
          (= (+ (+ a b) c) 3)
          (= (EXPT x 2) a)
          (= (EXPT y 2) b)
          (= (EXPT z 2) c))
    (<= (+ (+ (* a b) (* b c)) (* c a)) (+ (+ x y) z)))-/
-- open Real
-- theorem inequalities_45542 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
--     (h : a + b + c = 3) :
--     sqrt a + sqrt b + sqrt c ≥ a * b + b * c + c * a := by

--     norm_horn (vars := [x,y,z]) (hyps := [hx,hy,hz])
--     horn_all
    -- set x := sqrt a with hx
    -- set y := sqrt b with hy
    -- set z := sqrt c with hz
    -- rw[← sq_eq_sq₀ (by positivity) (by positivity)] at hx hy hz
    -- conv_rhs at hx => rw[sq_sqrt (by positivity)]
    -- conv_rhs at hy => rw[sq_sqrt (by positivity)]
    -- conv_rhs at hz => rw[sq_sqrt (by positivity)]
    -- norm_num
    -- horn_all

--   have h1 : sqrt a ≥ a * (3 - a) / 2 := by
--     have h1 : 0 ≤ a := by linarith
--     have h2 : a ≤ 3 := by nlinarith [sq_nonneg (a - 3), h]
--     have h3 : sqrt a ≥ 0 := Real.sqrt_nonneg a
--     have h4 : 2 * sqrt a ≥ a * (3 - a) := by
--       nlinarith [sq_nonneg (sqrt a - (a * (3 - a) / 2)), Real.sq_sqrt (show 0 ≤ a by linarith),
--         sq_nonneg (a - 1), sq_nonneg (a - 2), sq_nonneg (a - 3)]
--     linarith
--   have h2 : sqrt b ≥ b * (3 - b) / 2 := by
--     have h1 : 0 ≤ b := by linarith
--     have h2 : b ≤ 3 := by nlinarith [sq_nonneg (b - 3), h]
--     have h3 : sqrt b ≥ 0 := Real.sqrt_nonneg b
--     have h4 : 2 * sqrt b ≥ b * (3 - b) := by
--       nlinarith [sq_nonneg (sqrt b - (b * (3 - b) / 2)), Real.sq_sqrt (show 0 ≤ b by linarith),
--         sq_nonneg (b - 1), sq_nonneg (b - 2), sq_nonneg (b - 3)]
--     linarith
--   have h3 : sqrt c ≥ c * (3 - c) / 2 := by
--     have h1 : 0 ≤ c := by linarith
--     have h2 : c ≤ 3 := by nlinarith [sq_nonneg (c - 3), h]
--     have h3 : sqrt c ≥ 0 := Real.sqrt_nonneg c
--     have h4 : 2 * sqrt c ≥ c * (3 - c) := by
--       nlinarith [sq_nonneg (sqrt c - (c * (3 - c) / 2)), Real.sq_sqrt (show 0 ≤ c by linarith),
--         sq_nonneg (c - 1), sq_nonneg (c - 2), sq_nonneg (c - 3)]
--     linarith
--   have h4 : sqrt a + sqrt b + sqrt c ≥ a * b + b * c + c * a := by
--     have h4 : a * b + b * c + c * a ≤ (9 - (a^2 + b^2 + c^2)) / 2 := by
--       nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
--         h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
--     nlinarith [h1, h2, h3, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
--   linarith [h4]

-- theorem inequalities_124969 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
--     (h : a + b + c ≤ 3) :
--     a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ 3 / 2 ∧
--     3 / 2 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) := by
--     constructor
--     · norm_horn
--       -- field_simp
--       -- rw[div_le_div_iff₀ (by positivity) (by positivity)]
--       ring_nf
--       simp[pow_two]
--       horn[ha,hb,hc,h]
--       sorry
--     · field_simp
--       rw[div_le_div_iff₀ (by positivity) (by positivity)]
--       horn[ha,hb,hc,h]
--       have imandra_proof : ∀ a b c : ℝ, ((0 ≤ a) → (0 ≤ b) → (0 ≤ c) → (((a + b) + c) ≤ 3) → ((3 * (((1 + a) * (1 + b)) * (1 + c))) ≤ (((((1 + b) + (1 + a)) * (1 + c)) + ((1 + a) * (1 + b))) * 2))) := by
--         intros a b c
--         by_contra! goal
--         rcases goal with ⟨h1, h2, h3, h4, h5⟩

--       --  problem polynomials and their properties from the goal
--         let prob0 : ℝ := (0 - (0 - a))
--         have h_prob_0_nonneg : prob0 ≥ 0 := by unfold prob0; linarith
--         let prob1 : ℝ := (0 - (0 - b))
--         have h_prob_1_nonneg : prob1 ≥ 0 := by unfold prob1; linarith
--         let prob2 : ℝ := (0 - (0 - c))
--         have h_prob_2_nonneg : prob2 ≥ 0 := by unfold prob2; linarith
--         let prob3 : ℝ := (0 - (((a + b) + c) - 3))
--         have h_prob_3_nonneg : prob3 ≥ 0 := by unfold prob3; linarith
--         let prob4 : ℝ := ((3 * (((1 + a) * (1 + b)) * (1 + c))) - (((((1 + b) + (1 + a)) * (1 + c)) + ((1 + a) * (1 + b))) * 2))
--         have h_prob_4_pos : prob4 > 0 := by unfold prob4; linarith

--       --  ideal cofactors

--       --  cone cofactors (sums of squares)
--         let cone_cf_0 : ℝ := ((1) * (((1/3) * ((((-1 / 2) * a) + (((-1 / 2) * b) + c)))^2) + ((1/4) * ((a + (-1 * b)))^2)))
--         have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith
--         let cone_cf_1 : ℝ := (((0 - (((a + b) + c) - 3)) * (1)) * ((1) * ((((1 / 3) * a) + (((1 / 3) * b) + (((1 / 3) * c) + 1))))^2))
--         have h_cone_cf_1_nonneg : cone_cf_1 ≥ 0 := by unfold cone_cf_1; first | positivity | linarith
--         let cone_cf_2 : ℝ := (((0 - (0 - c)) * (1)) * (((1/9) * ((((-1 / 2) * a) + (((-1 / 2) * b) + c)))^2) + ((5/12) * ((a + (-1 * b)))^2)))
--         have h_cone_cf_2_nonneg : cone_cf_2 ≥ 0 := by unfold cone_cf_2; first | positivity | linarith
--         let cone_cf_3 : ℝ := (((0 - (0 - b)) * (1)) * (((4/9) * ((((-7 / 8) * a) + (((-1 / 8) * b) + c)))^2) + ((5/48) * ((a + (-1 * b)))^2)))
--         have h_cone_cf_3_nonneg : cone_cf_3 ≥ 0 := by unfold cone_cf_3; first | positivity | linarith
--         let cone_cf_4 : ℝ := (((0 - (0 - a)) * (1)) * (((4/9) * ((((-1 / 8) * a) + (((-7 / 8) * b) + c)))^2) + ((5/48) * ((a + (-1 * b)))^2)))
--         have h_cone_cf_4_nonneg : cone_cf_4 ≥ 0 := by unfold cone_cf_4; first | positivity | linarith

--       --  monoid cofactors (products of non-equalities)
--         let monoid_cf_0 : ℝ := ((3 * (((1 + a) * (1 + b)) * (1 + c))) - (((((1 + b) + (1 + a)) * (1 + c)) + ((1 + a) * (1 + b))) * 2))
--         have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; linarith

--       --  Proofs for ideal products being zero

--       --  Positivstellensatz Certificate
--         let cert : ℝ := monoid_cf_0 + cone_cf_0 + cone_cf_1 + cone_cf_2 + cone_cf_3 + cone_cf_4

--       --  Show the certificate is identically zero using the problem constraints
--         have h_cert_key : cert = 0 := by unfold cert cone_cf_0 cone_cf_1 cone_cf_2 cone_cf_3 cone_cf_4 monoid_cf_0; linarith

--       --  Show the certificate is non_zero, which is the key contradiction
--         have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

--         tauto

--       simp_all








-- theorem inequalities_1674 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
--     2 * (a + b + c)^3 ≥ 3 * (a^2 + b^2 + c^2 + a * b + b * c + c * a) *
--       Real.sqrt (3 * (a * b + b * c + c * a)) := by
--   norm_horn (vars := [x1,x2]) (hyps := [hx1,hx2])
--   horn[ha,hb,hc]
/-S-expression output:
(IMPLIES (AND (< 0 a)
          (< 0 b)
          (< 0 c))
    (>= (* 2 (EXPT (+ (+ a b) c) 3)) (* (* 3 (+ (+ (+ (+ (+ (EXPT a 2) (EXPT b 2)) (EXPT c 2)) (* a b)) (* b c)) (* c a))) (EXPT (* 3 (+ (+ (* a b) (* b c)) (* c a))) (/ 1 2)))))-/

-- theorem inequalities_605843 (a b c : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ b) (h₂ : b ≤ c)
--     (h₃ : a + b + c = a * b + b * c + c * a) (h₄ : 0 < a + b + c) (h₅ : a + b + c > 0):
--     Real.sqrt (b * c) * (a + 1) ≥ 2 ∧ (Real.sqrt (b * c) * (a + 1) = 2 ↔ (a = 1 ∧ b = 1 ∧ c = 1 ∨ a = 0 ∧ b = 2 ∧ c = 2)) := by
--     constructor
--     rw[ge_iff_le]
--     rw[← Real.sq_sqrt (show 0 ≤ a + 1 by positivity ), pow_two, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul ]
--     rw [Real.le_sqrt' (by positivity)]
--     norm_num
--     have h₆ : a * b + b * c + c * a > 0 := by rw[h₃] at h₅; exact h₅
--     have : b * c ≥ 1 := by
--       horn[h₀,h₁,h₂,h₃,h₄, h₅,h₆]

-- theorem inequalities_262331 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
--     (h : a + b + c ≥ a * b * c) :
--     (2 / a + 3 / b + 6 / c ≥ 6 ∧ 2 / b + 3 / c + 6 / a ≥ 6) ∨
--     (2 / a + 3 / b + 6 / c ≥ 6 ∧ 2 / c + 3 / a + 6 / b ≥ 6) ∨
--     (2 / b + 3 / c + 6 / a ≥ 6 ∧ 2 / c + 3 / a + 6 / b ≥ 6) := by

-- theorem inequalities_605327 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (_ : 0 < z)
--     (h1 : x ≤ 2) (h2 : y ≤ 3) (h3 : x + y + z = 11) :
--     Real.sqrt (x * y * z) ≤ 6 := by
--     rw[Real.sqrt_le_iff]
--     norm_num
--     horn_all
--     sorry
-- theorem inequalities_605327 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (_ : 0 < z)
--     (h1 : x ≤ 2) (h2 : y ≤ 3) (h3 : x + y + z = 11) :
--     Real.sqrt (x * y * z) ≤ 6 := by
--   -- The goal `sqrt(A) ≤ B` is equivalent to `A ≤ B²` for non-negative A and B.
--   -- The `rw` tactic with `Real.sqrt_le_iff_sq_le` splits the goal into two parts:
--   -- 1. The main goal: `x * y * z ≤ 6 ^ 2`
--   -- 2. A side goal: `0 ≤ x * y * z`, to ensure the arguments of `sqrt` are valid.
--   rw [Real.sqrt_le_iff]
--   norm_num
--   horn_all
--   suffices 36 - x * y * z ≥ 0 by linarith

--   -- First, substitute `z` using the constraint `x + y + z = 11`.
--   have h_z_rw : z = 11 - x - y := by linarith [h3]
--   rw [h_z_rw]

--   -- Now, we use the key algebraic identity.
--   -- `36 - x*y*(11-x-y) = (2-x)²*y + (3-y)²*x + (2-x)*(9+y) + 6*(3-y)`
--   -- The `ring` tactic can verify this polynomial identity automatically.
--   have h_identity : 36 - x * y * (11 - x - y) =
--       (2 - x) ^ 2 * y + (3 - y) ^ 2 * x + (2 - x) * (9 + y) + 6 * (3 - y) := by
--     ring

--   -- We rewrite our goal using this identity.
--   rw [h_identity]

--   -- The goal is now to prove that the sum of these terms is non-negative.
--   -- The `positivity` tactic is designed for this. It analyzes each term
--   -- and uses the given hypotheses (`hx`, `hy`, `h1`, `h2`) to prove
--   -- that each part of the sum is non-negative.
--   norm_num
--   horn[hx,hy,h1,h2]
--   positivity


-- theorem with_all_hyps (a b c : ℝ) (h1 : 0 < a) (h2 : a ≤ b) : a * c^2 ≤ b * c^2 := by
--   horn_all

-- theorem inequalities_606244 (x y z : ℝ) : (x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) + (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) ≤ (x + y + z) ^ 2 ∧ ((x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) + (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) = (x + y + z) ^ 2 ↔ x = 0 ∧ y = 0 ∧ z = 0):= by
--   field_simp
--   rw[div_le_iff₀ (by positivity)]
--   constructor
--   horn

-- theorem inequalities_605980 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h : a * b * c * d = 1) :
--     (1 / (a ^ 3 + b + c + d) + 1 / (a + b ^ 3 + c + d) + 1 / (a + b + c ^ 3 + d) + 1 / (a + b + c + d ^ 3)) ≤ (a + b + c + d) / 4 := by
--   field_simp
--   rw[div_le_div_iff₀ (by positivity) (by positivity)]
--   horn_all

-- theorem inequalities_605980 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h : a * b * c * d = 1) :
--     (1 / (a ^ 3 + b + c + d) + 1 / (a + b ^ 3 + c + d) + 1 / (a + b + c ^ 3 + d) + 1 / (a + b + c + d ^ 3)) ≤ (a + b + c + d) / 4 := by
--   -- First prove the Cauchy-Schwarz inequality.
--   have CS_ineq (x₁ y₁ z₁ w₁ x₂ y₂ z₂ w₂ : ℝ) : (x₁ * x₂ + y₁ * y₂ + z₁ * z₂ + w₁ * w₂) ^ 2 ≤ (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2 + w₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2 + w₂ ^ 2) := by
--     horn
--     have imandra_proof : ∀ w1 w2 x1 x2 y1 y2 z1 z2 : ℝ, ((((((x1 * x2) + (y1 * y2)) + (z1 * z2)) + (w1 * w2)) ^ 2) ≤ (((((x1 ^ 2) + (y1 ^ 2)) + (z1 ^ 2)) + (w1 ^ 2)) * ((((x2 ^ 2) + (y2 ^ 2)) + (z2 ^ 2)) + (w2 ^ 2)))) := by
--       intros w1 w2 x1 x2 y1 y2 z1 z2
--       by_contra! goal

--     --  problem polynomials and their properties from the goal
--       let prob0 : ℝ := ((((((x1 * x2) + (y1 * y2)) + (z1 * z2)) + (w1 * w2)) ^ 2) - (((((x1 ^ 2) + (y1 ^ 2)) + (z1 ^ 2)) + (w1 ^ 2)) * ((((x2 ^ 2) + (y2 ^ 2)) + (z2 ^ 2)) + (w2 ^ 2))))
--       have h_prob_0_pos : prob0 > 0 := by unfold prob0; linarith

--     --  ideal cofactors

--     --  cone cofactors (sums of squares)
--       let cone_cf_0 : ℝ := ((1) * (((1) * (((x1 * y2) + (-1 * (x2 * y1))))^2) + (((1) * (((x1 * z2) + (-1 * (x2 * z1))))^2) + (((1) * (((w1 * y2) + (-1 * (w2 * y1))))^2) + (((1) * (((w1 * z2) + (-1 * (w2 * z1))))^2) + (((1) * (((-1 * (y1 * z2)) + (y2 * z1)))^2) + ((1) * (((-1 * (w1 * x2)) + (w2 * x1)))^2)))))))
--       have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith

--     --  monoid cofactors (products of non-equalities)
--       let monoid_cf_0 : ℝ := ((((((x1 * x2) + (y1 * y2)) + (z1 * z2)) + (w1 * w2)) ^ 2) - (((((x1 ^ 2) + (y1 ^ 2)) + (z1 ^ 2)) + (w1 ^ 2)) * ((((x2 ^ 2) + (y2 ^ 2)) + (z2 ^ 2)) + (w2 ^ 2))))
--       have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; linarith

--     --  Proofs for ideal products being zero

--     --  Positivstellensatz Certificate
--       let cert : ℝ := monoid_cf_0 + cone_cf_0

--     --  Show the certificate is identically zero using the problem constraints
--       have h_cert_key : cert = 0 := by unfold cert cone_cf_0 monoid_cf_0; linarith

--     --  Show the certificate is non_zero, which is the key contradiction
--       have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

--       tauto
--     simp_all
--   --   nlinarith [sq_nonneg (x₁ * y₂ - y₁ * x₂), sq_nonneg (y₁ * z₂ - z₁ * y₂), sq_nonneg (z₁ * x₂ - x₁ * z₂), sq_nonneg (w₁ * x₂ - x₁ * w₂), sq_nonneg (w₁ * y₂ - y₁ * w₂), sq_nonneg (w₁ * z₂ - z₁ * w₂)]
--   -- Show that (a + b + c + d)² ≤ (a³ + b + c + d)(1 / a + b + c + d).
--   have h₁ : (a + b + c + d) ^ 2 ≤ (a ^ 3 + b + c + d) * (1 / a + b + c + d) := by

--     specialize CS_ineq (Real.sqrt (a ^ 3)) (Real.sqrt b) (Real.sqrt c) (Real.sqrt d) (Real.sqrt (1 / a)) (Real.sqrt b) (Real.sqrt c) (Real.sqrt d)
--     repeat rw [<-Real.sqrt_mul (by positivity)] at CS_ineq
--     repeat rw [<-pow_two, Real.sqrt_sq (by positivity)] at CS_ineq
--     repeat rw [Real.sq_sqrt (by positivity)] at CS_ineq
--     rw [show a ^ 3 * (1 / a) = a ^ 2 by field_simp; ring, Real.sqrt_sq (by positivity)] at CS_ineq
--     exact CS_ineq
--   -- Show that (a + b + c + d)² ≤ (a + b³ + c + d)(a + 1 / b + c + d).
--   have h₂ : (a + b + c + d) ^ 2 ≤ (a + b ^ 3 + c + d) * (a + 1 / b + c + d) := by
--     specialize CS_ineq (Real.sqrt a) (Real.sqrt (b ^ 3)) (Real.sqrt c) (Real.sqrt d) (Real.sqrt a) (Real.sqrt (1 / b)) (Real.sqrt c) (Real.sqrt d)
--     repeat rw [<-Real.sqrt_mul (by positivity)] at CS_ineq
--     repeat rw [<-pow_two, Real.sqrt_sq (by positivity)] at CS_ineq
--     repeat rw [Real.sq_sqrt (by positivity)] at CS_ineq
--     rw [show b ^ 3 * (1 / b) = b ^ 2 by field_simp; ring, Real.sqrt_sq (by positivity)] at CS_ineq
--     exact CS_ineq
--   -- Show that (a + b + c + d)² ≤ (a + b + c³ + d)(a + b + 1 / c + d).
--   have h₃ : (a + b + c + d) ^ 2 ≤ (a + b + c ^ 3 + d) * (a + b + 1 / c + d) := by
--     specialize CS_ineq (Real.sqrt a) (Real.sqrt b) (Real.sqrt (c ^ 3)) (Real.sqrt d) (Real.sqrt a) (Real.sqrt b) (Real.sqrt (1 / c)) (Real.sqrt d)
--     repeat rw [<-Real.sqrt_mul (by positivity)] at CS_ineq
--     repeat rw [<-pow_two, Real.sqrt_sq (by positivity)] at CS_ineq
--     repeat rw [Real.sq_sqrt (by positivity)] at CS_ineq
--     rw [show c ^ 3 * (1 / c) = c ^ 2 by field_simp; ring, Real.sqrt_sq (by positivity)] at CS_ineq
--     exact CS_ineq
--   -- Show that (a + b + c + d)² ≤ (a + b + c + d⁴)(a + b + c + 1 / d).
--   have h₄ : (a + b + c + d) ^ 2 ≤ (a + b + c + d ^ 3) * (a + b + c + 1 / d) := by
--     specialize CS_ineq (Real.sqrt a) (Real.sqrt b) (Real.sqrt c) (Real.sqrt (d ^ 3)) (Real.sqrt a) (Real.sqrt b) (Real.sqrt c) (Real.sqrt (1 / d))
--     repeat rw [<-Real.sqrt_mul (by positivity)] at CS_ineq
--     repeat rw [<-pow_two, Real.sqrt_sq (by positivity)] at CS_ineq
--     repeat rw [Real.sq_sqrt (by positivity)] at CS_ineq
--     rw [show d ^ 3 * (1 / d) = d ^ 2 by field_simp; ring, Real.sqrt_sq (by positivity)] at CS_ineq
--     exact CS_ineq
--   -- Add the inequalities.
--   field_simp at h₁ h₂ h₃ h₄ ⊢
--   rw[le_div_iff₀ (by positivity)] at h₁
--   rw[le_div_iff₀ (by positivity)] at h₂
--   rw[le_div_iff₀ (by positivity)] at h₃
--   rw[le_div_iff₀ (by positivity)] at h₄

--   rw[div_le_div_iff₀ (by positivity) (by positivity)]

--   horn[ha,hb,hc,hd,h₁,h₂,h₃,h₄]

  -- calc
  --   1 / (a ^ 3 + b + c + d) + 1 / (a + b ^ 3 + c + d) + 1 / (a + b + c ^ 3 + d) + 1 / (a + b + c + d ^ 3)
  --   _ ≤ ((1 / a + b + c + d) + (a + 1 / b + c + d) + (a + b + 1 / c + d) + (a + b + c + 1 / d)) / (a + b + c + d) ^ 2 := by
  --     -- Use the four lemmas proved above.
  --     iterate 3 rw [add_div]
  --     iterate 3 apply add_le_add
  --     . rw [le_div_iff₀ (by positivity), div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity), mul_comm]
  --       exact h₁
  --     . rw [le_div_iff₀ (by positivity), div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity), mul_comm]
  --       exact h₂
  --     . rw [le_div_iff₀ (by positivity), div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity), mul_comm]
  --       exact h₃
  --     . rw [le_div_iff₀ (by positivity), div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity), mul_comm]
  --       exact h₄
  --   _ = (3 * (a + b + c + d) + (1 / a + 1 / b + 1 / c + 1 / d)) / (a + b + c + d) ^ 2 := by
  --     -- Group terms together.
  --     congrm ?_ / ?_
  --     . ring
  --     . rfl
  --   _ ≤ (a + b + c + d) / 4 := by
  --     -- Let x = a + b + c + d and y = 1 / a + 1 / b + 1 / c + 1 / d.
  --     let x := a + b + c + d
  --     let y := 1 / a + 1 / b + 1 / c + 1 / d
  --     -- Since abcd = 1, we have y = bcd + cda + dab + abc.
  --     have hy : y = b * c * d + c * d * a + d * a * b + a * b * c := by
  --       rw [show y = 1 / a + 1 / b + 1 / c + 1 / d by rfl, <-h]
  --       field_simp
  --       ring
  --     rw [show a + b + c + d = x by rfl, show 1 / a + 1 / b + 1 / c + 1 / d = y by rfl]
  --     -- We need to show that x³ ≥ 12x + 4y.
  --     rw [div_le_div_iff₀ (by positivity) (by positivity)]
  --     -- Let s(i) = a if i = 0, b if i = 1, c if i = 2, d if i = 3.
  --     let s (i : ℕ) :=
  --       match i with
  --       | 0 => a
  --       | 1 => b
  --       | 2 => c
  --       | 3 => d
  --       | _ => 0
  --     -- Prove that a³ + a²b + a²b + a²c + a²c + a²d + a²d + b²a + c²a + d²a + bcd + bcd ≥ 12a, and cyclic for other three variables.
  --     have hs (i : ℕ) (hi : i ∈ Finset.range 4) : s i ^ 3 + s i ^ 2 * s ((i + 1) % 4) + s i ^ 2 * s ((i + 1) % 4) + s i ^ 2 * s ((i + 2) % 4) + s i ^ 2 * s ((i + 2) % 4) + s i ^ 2 * s ((i + 3) % 4) + s i ^ 2 * s ((i + 3) % 4) + s ((i + 1) % 4) ^ 2 * s i + s ((i + 2) % 4) ^ 2 * s i + s ((i + 3) % 4) ^ 2 * s i + s ((i + 1) % 4) * s ((i + 2) % 4) * s ((i + 3) % 4) + s ((i + 1) % 4) * s ((i + 2) % 4) * s ((i + 3) % 4) ≥ 12 * s i := by
  --       -- Preparing for the use of AM-GM inequality.
  --       let t (j : ℕ) :=
  --         match j with
  --         | 0 => s i ^ 3
  --         | 1 => s i ^ 2 * s ((i + 1) % 4)
  --         | 2 => s i ^ 2 * s ((i + 1) % 4)
  --         | 3 => s i ^ 2 * s ((i + 2) % 4)
  --         | 4 => s i ^ 2 * s ((i + 2) % 4)
  --         | 5 => s i ^ 2 * s ((i + 3) % 4)
  --         | 6 => s i ^ 2 * s ((i + 3) % 4)
  --         | 7 => s ((i + 1) % 4) ^ 2 * s i
  --         | 8 => s ((i + 2) % 4) ^ 2 * s i
  --         | 9 => s ((i + 3) % 4) ^ 2 * s i
  --         | 10 => s ((i + 1) % 4) * s ((i + 2) % 4) * s ((i + 3) % 4)
  --         | 11 => s ((i + 1) % 4) * s ((i + 2) % 4) * s ((i + 3) % 4)
  --         | _ => 0
  --       simp at hi
  --       have g₀ : ∀ i ∈ Finset.range 12, 0 ≤ t i := by
  --         intro j hj
  --         simp at hj
  --         interval_cases j
  --         all_goals
  --           simp [t]
  --           interval_cases i
  --           all_goals
  --             simp [s]
  --             positivity
  --       -- Apply AM-GM inequality for 12 variables.
  --       have := Real.geom_mean_le_arith_mean_weighted (Finset.range 12) (λ i => (1 / 12 : ℝ)) t (by norm_num) (by simp) g₀
  --       iterate 12 rw [Finset.sum_range_succ, Finset.prod_range_succ] at this
  --       rw [Finset.sum_range_zero, Finset.prod_range_zero] at this
  --       simp [s, -one_div] at this
  --       iterate 11 rw [<-Real.mul_rpow (by simp [t]; interval_cases i; all_goals {simp [s]; positivity}) (by simp [t]; interval_cases i; all_goals {simp [s]; positivity}), <-mul_add] at this
  --       calc
  --         s i ^ 3 + s i ^ 2 * s ((i + 1) % 4) + s i ^ 2 * s ((i + 1) % 4) + s i ^ 2 * s ((i + 2) % 4) + s i ^ 2 * s ((i + 2) % 4) + s i ^ 2 * s ((i + 3) % 4) + s i ^ 2 * s ((i + 3) % 4) + s ((i + 1) % 4) ^ 2 * s i + s ((i + 2) % 4) ^ 2 * s i + s ((i + 3) % 4) ^ 2 * s i + s ((i + 1) % 4) * s ((i + 2) % 4) * s ((i + 3) % 4) + s ((i + 1) % 4) * s ((i + 2) % 4) * s ((i + 3) % 4)
  --         _ = 12 * (1 / 12 * (t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + t 6 + t 7 + t 8 + t 9 + t 10 + t 11)) := by
  --           simp [t]
  --         _ ≥ 12 * (t 0 * t 1 * t 2 * t 3 * t 4 * t 5 * t 6 * t 7 * t 8 * t 9 * t 10 * t 11) ^ (1 / 12 : ℝ) := by
  --           rw [ge_iff_le, mul_le_mul_left (by norm_num)]
  --           exact this
  --         _ = 12 * (s i ^ 12 * (s i * s ((i + 1) % 4) * s ((i + 2) % 4) * s ((i + 3) % 4)) ^ 6) ^ (1 / 12 : ℝ) := by
  --           congrm ?_ * ?_ ^ ?_
  --           . rfl
  --           . simp [t]
  --             ring
  --           . rfl
  --         _ = 12 * s i := by
  --           have g₁ : s i * s ((i + 1) % 4) * s ((i + 2) % 4) * s ((i + 3) % 4) = a * b * c * d := by
  --             interval_cases i
  --             all_goals
  --               simp [s]
  --               try ring
  --           rw [g₁, h, one_pow, mul_one, <-Real.rpow_natCast, <-Real.rpow_mul (by interval_cases i; all_goals {simp [s]; positivity})]
  --           norm_num
  --     -- Specialize hs for i = 0, 1, 2, 3.
  --     have hs0 := hs 0 (by norm_num)
  --     have hs1 := hs 1 (by norm_num)
  --     have hs2 := hs 2 (by norm_num)
  --     have hs3 := hs 3 (by norm_num)
  --     simp [s] at hs0 hs1 hs2 hs3
  --     simp [x, hy]
  --     -- The required result is a simple sum of the four inequalities.
  --     linarith only [hs0, hs1, hs2, hs3]

--JBMO
-- theorem inequalities_604693 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h1 : a < 1) (h2 : b < 1) (h3 : c < 1) (h4 : d < 1) :
-- 1 + a * b + b * c + c * d + d * a + a * c + b * d > a + b + c + d := by
--   horn_all

-- theorem Inequalities_613610
--     (a b c : ℝ)
--     (ha : 0 < a)
--     (hb : 0 < b)
--     (hc : 0 < c) :
--     (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 1 / 3 ≥
--     8 / 9 * (a / (b + c) + b / (c + a) + c / (a + b)) := by
--   -- norm_horn
--   field_simp
--   rw[div_le_div_iff₀ (by positivity) (by positivity)]
--   horn_all

-- theorem inequalities_604729 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z + x * y + y * z + z * x = x + y + z + 1) : (1 / 3) * (√((1 + x ^ 2) / (1 + x)) + √((1 + y ^ 2) / (1 + y)) + √((1 + z ^ 2) / (1 + z))) ≤ ((x + y + z) / 3) ^ ((5 : ℝ) / 8):= by


-- norm_horn (vars := [a,b,c,d,e,f,g]) (hyps := [ha,hb,hc,hd,he,hf,hg])

-- horn_all

-- theorem algebra_605787 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
--     √((a ^ 2 + a * b + b ^ 2) / 3) + √(a * b) ≤ a + b := by
-- norm_horn (vars := [w, x,y,z]) (hyps := [hw, hx, hy,hz])
-- horn_all


-- theorem inequalities_306868 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
--     (h : 9 * x * y * z + x * y + y * z + z * x = 4) :
--     x * y + y * z + z * x ≥ 4 / 3 ∧ x + y + z ≥ 2 := by
--     constructor
--     norm_horn
--     horn_all
--     sorry
--     horn_all

lemma lemma1 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : 1/a + 1/b + 1/c + 1/d ≥ 16 / (a + b + c + d) := by
  norm_horn
  horn_all
  have imandra_proof : ∀ a b c d : ℝ, ((a > 0) → (b > 0) → (c > 0) → (d > 0) → ((16 * (((a * b) * c) * d)) ≤ ((((((b + a) * c) + (a * b)) * d) + ((a * b) * c)) * (((a + b) + c) + d)))) := by
    intros a b c d
    by_contra! goal
    rcases goal with ⟨h1, h2, h3, h4, h5⟩

  --  problem polynomials and their properties from the goal
    let prob0 : ℝ := a
    have h_prob_0_pos : prob0 > 0 := by unfold prob0; linarith
    let prob1 : ℝ := b
    have h_prob_1_pos : prob1 > 0 := by unfold prob1; linarith
    let prob2 : ℝ := c
    have h_prob_2_pos : prob2 > 0 := by unfold prob2; linarith
    let prob3 : ℝ := d
    have h_prob_3_pos : prob3 > 0 := by unfold prob3; linarith
    let prob4 : ℝ := ((16 * (((a * b) * c) * d)) - ((((((b + a) * c) + (a * b)) * d) + ((a * b) * c)) * (((a + b) + c) + d)))
    have h_prob_4_pos : prob4 > 0 := by unfold prob4; linarith

  --  ideal cofactors

  --  cone cofactors (sums of squares)
    let cone_cf_0 : ℝ := ((c * (d * (1))) * ((1) * ((a + (-1 * b)))^2))
    have h_cone_cf_0_nonneg : cone_cf_0 ≥ 0 := by unfold cone_cf_0; first | positivity | linarith
    let cone_cf_1 : ℝ := ((b * (d * (1))) * ((1) * (((-1 * a) + c))^2))
    have h_cone_cf_1_nonneg : cone_cf_1 ≥ 0 := by unfold cone_cf_1; first | positivity | linarith
    let cone_cf_2 : ℝ := ((b * (c * (1))) * ((1) * (((-1 * a) + d))^2))
    have h_cone_cf_2_nonneg : cone_cf_2 ≥ 0 := by unfold cone_cf_2; first | positivity | linarith
    let cone_cf_3 : ℝ := ((a * (d * (1))) * ((1) * (((-1 * b) + c))^2))
    have h_cone_cf_3_nonneg : cone_cf_3 ≥ 0 := by unfold cone_cf_3; first | positivity | linarith
    let cone_cf_4 : ℝ := ((a * (c * (1))) * ((1) * (((-1 * b) + d))^2))
    have h_cone_cf_4_nonneg : cone_cf_4 ≥ 0 := by unfold cone_cf_4; first | positivity | linarith
    let cone_cf_5 : ℝ := ((a * (b * (1))) * ((1) * (((-1 * c) + d))^2))
    have h_cone_cf_5_nonneg : cone_cf_5 ≥ 0 := by unfold cone_cf_5; first | positivity | linarith

  --  monoid cofactors (products of non-equalities)
    let monoid_cf_0 : ℝ := ((16 * (((a * b) * c) * d)) - ((((((b + a) * c) + (a * b)) * d) + ((a * b) * c)) * (((a + b) + c) + d)))
    have h_monoid_cf_0_pos : monoid_cf_0 > 0 := by unfold monoid_cf_0; positivity

  --  Proofs for ideal products being zero

  --  Positivstellensatz Certificate
    let cert : ℝ := monoid_cf_0 + cone_cf_0 + cone_cf_1 + cone_cf_2 + cone_cf_3 + cone_cf_4 + cone_cf_5

  --  Show the certificate is identically zero using the problem constraints
    have h_cert_key : cert = 0 := by unfold cert cone_cf_0 cone_cf_1 cone_cf_2 cone_cf_3 cone_cf_4 cone_cf_5 monoid_cf_0; linarith

  --  Show the certificate is non_zero, which is the key contradiction
    have h_cert_contra : cert ≠ 0 := by unfold cert; positivity

    tauto
  simp_all
-- theorem inequalities_263245 (a b c d : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2)
--     (hc : 1 ≤ c ∧ c ≤ 2) (hd : 1 ≤ d ∧ d ≤ 2) (h : (a + c) * (b + d) = 8) :
--     1 ≤ 1 / (a ^ 2 + b ^ 2 - 1) + 1 / (b ^ 2 + c ^ 2 - 1) +
--         1 / (c ^ 2 + d ^ 2 - 1) + 1 / (d ^ 2 + a ^ 2 - 1) ∧
--     (1 = 1 / (a ^ 2 + b ^ 2 - 1) + 1 / (b ^ 2 + c ^ 2 - 1) +
--         1 / (c ^ 2 + d ^ 2 - 1) + 1 / (d ^ 2 + a ^ 2 - 1) ↔
--       (a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 2 ∨ a = 2 ∧ b = 1 ∧ c = 2 ∧ d = 1)) := by
--   constructor
--   have:= lemma1 (a^2 + b^2 - 1) (b^2 + c^2 - 1) (c^2 + d^2 - 1) (d^2 + a^2 - 1) (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)

-- theorem inequalities_608064 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y + y * z + z * x = x + y + z) : 1 / (x ^ 2 + y + 1) + 1 / (y ^ 2 + z + 1) + 1 / (z ^ 2 + x + 1) ≤ 1 ∧ (1 / (x ^ 2 + y + 1) + 1 / (y ^ 2 + z + 1) + 1 / (z ^ 2 + x + 1) = 1 ↔ x = 1 ∧ y = 1 ∧ z = 1):= by
-- constructor
-- norm_horn
-- horn_all
-- sorry
-- constructor
-- intro h1
-- norm_horn at h1
-- refine ⟨ ?_, ?_, ?_⟩
-- horn_all]

-- theorem inequalities_619358 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : b * c + c * a + a * b = 1 / 3) : 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1) ≤ 3:= by
-- by_cases h0 : a = 0 ∨ b = 0 ∨ c = 0
-- sorry
-- simp at h0
-- rcases h0 with ⟨h1,h2,h3⟩
-- replace ha : 0 < a := by sorry
-- replace hb : 0 < b := by sorry
-- replace hc : 0 < c  := by sorry

-- norm_horn

--CANADA_MO
-- theorem algebra_605332 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) :
--   (a - b * c) / (a + b * c) + (b - c * a) / (b + c * a) + (c - a * b) / (c + a * b) ≤ 3 / 2 := by
--   norm_horn
--   horn_all

-- theorem algebra_240469 (t : ℝ) (ht : t ≥ 1 / 2) (n : ℕ) (hn : n > 0) :
-- t ^ (2 * n) ≥ (t - 1) ^ (2 * n) + (2 * t - 1) ^ n:= by
-- norm_horn at ht
-- horn_all


-- lemma lm : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → b + √(a * c) ≤ √(b ^ 2 + (a + c) * b + a * c) := by
-- intros a b c h1 h2 h3
-- norm_horn (vars := [x, y,z]) (hyps :=[hx,hy,hz])
-- horn_all

-- theorem inequalities_130910 (a b c : ℝ) (apos : 0 < a) (bpos : 0 < b) (cpos : 0 < c)
--     (h : √a + √b + √c = 3) : 3 / 2 ≤ (a + b) / (2 + a + b) + (b + c) / (2 + b + c)
--     + (c + a) / (2 + c + a) ∧ ((a + b) / (2 + a + b) + (b + c) / (2 + b + c) +
--     (c + a) / (2 + c + a) = 3 / 2 ↔ a = 1 ∧ b = 1 ∧ c = 1) := by
--     constructor
--     norm_horn at *
--     horn_all



-- import Mathlib

-- open Real Finset

-- -- Prove an auxillary inequality which will be repeatedly used later
-- lemma lm : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → b + √(a * c) ≤ √(b ^ 2 + (a + c) * b + a * c) := by
--   intro a b c apos bpos cpos
--   rw [le_sqrt, ← sub_nonneg]; ring_nf
--   rw [sq_sqrt, sub_self, add_zero, add_sub, ← mul_add]
--   rw [mul_assoc, ← mul_sub]
--   have : a + c - √(a * c) * 2 = (√a - √c) ^ 2 := by
--     ring_nf; repeat rw [sq_sqrt]
--     rw [sqrt_mul]; ring
--     all_goals positivity
--   rw [this]; all_goals positivity

-- /-(22) Let $a, b, c \in \mathbf{R}^{+}$, and $\sqrt{a}+\sqrt{b}+\sqrt{c}=3$. Prove:
-- $$
-- \frac{a+b}{2+a+b}+\frac{b+c}{2+b+c}+\frac{c+a}{2+c+a} \geqslant \frac{3}{2},
-- $$

-- and specify the condition for equality.-/
-- theorem inequalities_130910 (a b c : ℝ) (apos : 0 < a) (bpos : 0 < b) (cpos : 0 < c)
--     (h : √a + √b + √c = 3) : 3 / 2 ≤ (a + b) / (2 + a + b) + (b + c) / (2 + b + c)
--     + (c + a) / (2 + c + a) ∧ ((a + b) / (2 + a + b) + (b + c) / (2 + b + c) +
--     (c + a) / (2 + c + a) = 3 / 2 ↔ a = 1 ∧ b = 1 ∧ c = 1) := by
-- -- Set up the following two vectors in $ℝ³$ and apply Cauchy-Schwartz inequality
--   let x : EuclideanSpace ℝ (Fin 3) := ![√(a + b) / √(2 + a + b),
--   √(b + c) / √(2 + b + c), √(c + a) / √(2 + c + a)]
--   let y : EuclideanSpace ℝ (Fin 3) := ![√(2 + a + b), √(2 + b + c), √(2 + c + a)]
--   have CS := abs_real_inner_le_norm x y
-- -- Simplify the inequality
--   rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)] at CS
--   rw [sq_abs, mul_pow] at CS
--   simp [x, y, EuclideanSpace.norm_eq] at CS
--   simp [sum_fin_eq_sum_range, show range 3 = {0, 1, 2} by rfl] at CS
--   repeat rw [div_pow] at CS
--   repeat rw [sq_sqrt] at CS
--   repeat rw [div_mul_cancel₀] at CS
--   constructor
--   -- Prove the following inequality with the help of the auxillary lemma `lm`
--   · have : 3 * (a + b + c + 3) ≤ (√(a + b) + (√(b + c) + √(c + a))) ^ 2 := by calc
--       _ = 3 * (a + b + c) + (√a + √b + √c) ^ 2 := by
--         rw [h]; ring
--       _ = 2 * (a + b + c) + 2 * (b + √(a * c) + (a + √(b * c)) + (c + √(a * b))) := by
--         repeat rw [sqrt_mul]
--         ring_nf; repeat rw [sq_sqrt]
--         ring; all_goals positivity
--       _ ≤ 2 * (a + b + c) + 2 * (√(b ^ 2 + (a + c) * b + a * c) +
--       √(a ^ 2 + (b + c) * a + b * c) + √(c ^ 2 + (a + b) * c + a * b)) := by
--         gcongr; all_goals apply lm
--         all_goals positivity
--       _ = _:= by
--         rw [← sub_eq_zero]; ring_nf
--         repeat rw [sq_sqrt]
--         repeat rw [← sqrt_mul]
--         ring_nf; all_goals positivity
--   -- The goal follows from transitivity
--     replace this := le_trans this CS
--     nth_rw 2 [mul_comm] at this
--     rw [mul_comm, show 2+a+b+(2+b+c+(2+c+a)) = (a+b+c+3)*2 by ring] at this
--     rw [mul_assoc, mul_le_mul_left] at this
--     linarith only [this]; positivity
--   constructor
--   -- Assume the equality holds, we show that $a$, $b$ and $c$ must be $1$. We first substitute `h'` to `CS` and simplify `CS`
--   · intro h'; rw [← add_assoc, ← add_assoc, h'] at CS
--     rw [← sub_nonneg] at CS; ring_nf at CS
--     rw [show (9:ℝ) = 3^2 by ring] at CS
--     nth_rw 1 [← h] at CS; ring_nf at CS
--     repeat rw [sq_sqrt] at CS
--     repeat rw [← sqrt_mul] at CS
--     ring_nf at CS; rw [add_sub, add_sub, ← sub_eq_add_neg] at CS
--     rw [sub_nonneg, le_sub_iff_add_le, le_sub_iff_add_le] at CS
--     repeat rw [← add_mul] at CS
--     rw [mul_le_mul_right] at CS
--     have : a + b + √(a * b) + c + √(a * c) + √(b * c) =
--     c + √(a * b) + (a + √(b * c)) + (b + √(a * c)) := by ring
--     rw [this] at CS
--     replace this : a * b + a * c + b * c + c ^ 2 =
--     c ^ 2 + (a + b) * c + a * b := by ring
--     rw [this] at CS
--     replace this : a * b + a * c + a ^ 2 + b * c =
--     a ^ 2 + (b + c) * a + b * c := by ring
--     rw [this] at CS
--     replace this : a * b + a * c + b * c + b ^ 2 =
--     b ^ 2 + (a + c) * b + a * c := by ring
--     rw [this] at CS
--   -- Apply `lm` to $a$, $b$ and $c$ in different orders to get three inequality
--     have le1 := lm a b c apos bpos cpos
--     have le2 := lm b a c bpos apos cpos
--     have le3 := lm a c b apos cpos bpos
--     replace le1 : b + √(a * c) = √(b ^ 2 + (a + c) * b + a * c) := by linarith
--     replace le2 : a + √(b * c) = √(a ^ 2 + (b + c) * a + b * c) := by linarith
--     replace le3 : c + √(a * b) = √(c ^ 2 + (a + b) * c + a * b) := by linarith
--   -- Prove that $a=c$
--     replace le1 : a = c := by
--       symm at le1
--       rw [sqrt_eq_iff_eq_sq, ← sub_eq_zero] at le1
--       ring_nf at le1
--       rw [sq_sqrt, sub_self, add_zero, add_sub, ← mul_add] at le1
--       rw [mul_assoc, ← mul_sub] at le1
--       have : a + c - √(a * c) * 2 = (√a - √c) ^ 2 := by
--         ring_nf; repeat rw [sq_sqrt]
--         rw [sqrt_mul]; ring
--         all_goals positivity
--       simp [this] at le1; rcases le1 with _|h
--       · linarith
--       rw [sub_eq_zero, sqrt_eq_iff_eq_sq, sq_sqrt] at h
--       exact h; all_goals positivity
--   -- Prove that $b=c$
--     replace le2 : b = c := by
--       symm at le2
--       rw [sqrt_eq_iff_eq_sq, ← sub_eq_zero] at le2
--       ring_nf at le2
--       rw [sq_sqrt, sub_self, add_zero, add_sub, ← mul_add] at le2
--       rw [mul_assoc, ← mul_sub] at le2
--       have : b + c - √(b * c) * 2 = (√b - √c) ^ 2 := by
--         ring_nf; repeat rw [sq_sqrt]
--         rw [sqrt_mul]; ring
--         all_goals positivity
--       simp [this] at le2; rcases le2 with _|h
--       · linarith
--       rw [sub_eq_zero, sqrt_eq_iff_eq_sq, sq_sqrt] at h
--       exact h; all_goals positivity
--   -- The goal follows easily from $a=c$ and $b=c$
--     simp [le1, le2]; rw [le1, le2] at h
--     replace h : √c = 1 := by linarith only [h]
--     rw [sqrt_eq_iff_eq_sq] at h; simp at h
--     exact h; all_goals positivity
-- -- Conversely, it is straightforward to check that the equality holds true when $a$, $b$ and $c$ are all $1$
--   intro h; rcases h with ⟨ha, hb, hc⟩
--   norm_num [ha, hb, hc]; all_goals positivity
-- theorem algebra_607145 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
--     a / (9 * b * c + 1) + b / (9 * c * a + 1) + c / (9 * a * b + 1) ≥
--     (a + b + c) / (1 + (a + b + c)^2) := by
--     -- First, prove Cauchy-Schwarz inequality for 3D vectors
--     have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
--         (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
--         intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
--         have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
--         linarith
--     -- Transform Cauchy-Schwarz into a weighted form
--     replace h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
--         (x1 ^ 2 / x2 + y1 ^ 2 / y2 + z1 ^ 2 / z2) * (x2 + y2 + z2) ≥ (x1 + y1 + z1) ^ 2:= by
--         intro x1 y1 z1 x2 y2 z2 hx1 hy1 hz1 hx2 hy2 hz2
--         have g1 : √(x1 ^ 2 / x2) ^ 2 = x1 ^ 2 / x2:= by refine Real.sq_sqrt (by positivity)
--         have g2 : √(y1 ^ 2 / y2) ^ 2 = y1 ^ 2 / y2:= by refine Real.sq_sqrt (by positivity)
--         have g3 : √(z1 ^ 2 / z2) ^ 2 = z1 ^ 2 / z2:= by refine Real.sq_sqrt (by positivity)
--         have g4 : √x2 ^ 2 = x2:= by refine Real.sq_sqrt (by positivity)
--         have g5 : √y2 ^ 2 = y2:= by refine Real.sq_sqrt (by positivity)
--         have g6 : √z2 ^ 2 = z2:= by refine Real.sq_sqrt (by positivity)
--         have h1:= h1 (√(x1 ^ 2 / x2)) (√(y1 ^ 2 / y2)) (√(z1 ^ 2 / z2)) (√x2) (√y2) (√z2) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
--         rw [g1, g2, g3, g4, g5, g6] at h1
--         rw [(Eq.symm (Real.sqrt_mul (by positivity) x2)), (show x1 ^ 2 / x2 * x2 = x1 ^ 2 by field_simp), (show √(x1 ^ 2) = x1 by refine Real.sqrt_sq (by positivity))] at h1
--         rw [(Eq.symm (Real.sqrt_mul (by positivity) y2)), (show y1 ^ 2 / y2 * y2 = y1 ^ 2 by field_simp), (show √(y1 ^ 2) = y1 by refine Real.sqrt_sq (by positivity))] at h1
--         rw [(Eq.symm (Real.sqrt_mul (by positivity) z2)), (show z1 ^ 2 / z2 * z2 = z1 ^ 2 by field_simp), (show √(z1 ^ 2) = z1 by refine Real.sqrt_sq (by positivity))] at h1
--         exact h1
--     -- Rewrite fractions to match the form needed for applying the inequality
--     rw [show a / (9 * b * c + 1) = a ^ 2 / ((9 * b * c + 1) * a)  by field_simp ; linarith]
--     rw [show b / (9 * c * a + 1) = b ^ 2 / ((9 * c * a + 1) * b)  by field_simp ; linarith]
--     rw [show c / (9 * a * b + 1) = c ^ 2 / ((9 * a * b + 1) * c)  by field_simp ; linarith]
--     -- Apply the weighted Cauchy-Schwarz inequality with specific values
--     specialize h1 a b c ((9 * b * c + 1) * a) ((9 * c * a + 1) * b) ((9 * a * b + 1) * c) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

--     -- Simplify the denominator sum using ring normalization
--     rw [show (9 * b * c + 1) * a + (9 * c * a + 1) * b + (9 * a * b + 1) * c = 27 * a * b * c + a + b + c by ring_nf] at h1

--     -- Prove positivity of the denominator
--     have g1 : 27 * a * b * c + a + b + c > 0:= by positivity

--     -- Rewrite inequality using division
--     replace h1 : a ^ 2 / ((9 * b * c + 1) * a) + b ^ 2 / ((9 * c * a + 1) * b) + c ^ 2 / ((9 * a * b + 1) * c) ≥ (a + b + c) ^ 2 / (27 * a * b * c + a + b + c):= by exact (div_le_iff₀ g1).mpr h1

--     -- Set up final step of the proof
--     suffices (a + b + c) ^ 2 / (27 * a * b * c + a + b + c) ≥ (a + b + c) / (1 + (a + b + c) ^ 2) by linarith
--     clear h1

--     -- Prove key inequality about the denominator
--     have h1 : 27 * a * b * c + a + b + c ≤ (a + b + c) ^ 3 + a + b + c:= by
--         -- Use sum of squares inequalities
--         have g1 : (a + b) * (a - b) ^ 2 + (b + c) * (b - c) ^ 2 + (c + a) * (c - a) ^ 2 ≥ 0:= by positivity
--         have g2 : a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 ≥ 0:= by positivity
--         linarith

--     -- Square is nonnegative
--     have g2 : (a + b + c) ^ 2 ≥ 0:= by positivity

--     -- Apply division inequality
--     replace h1 : (a + b + c) ^ 2 / (27 * a * b * c + a + b + c) ≥ (a + b + c) ^ 2 / ((a + b + c) ^ 3 + a + b + c):= by refine div_le_div_of_nonneg_left g2 g1 h1

--     -- Final algebraic simplification
--     rw [show (a + b + c) ^ 2 / ((a + b + c) ^ 3 + a + b + c) = (a + b + c) / (1 + (a + b + c) ^ 2) by field_simp ; linarith] at h1
--     linarith
-- theorem algebra_70646 (a b c : ℝ) (h : a * b * c = 1) : 2 * a - 1 / b ≤ 1 ∨ 2 * b - 1 / c ≤ 1 ∨ 2 * c - 1 / a ≤ 1:= by
--   -- Proof by contradiction: assume all three expressions are greater than 1
--   by_contra H
--   simp at H
--   field_simp at H
--   rcases H with ⟨H1, H2, H3⟩
--   -- Since a*b*c = 1, none of a, b, c can be zero
--   have g1 : a * b * c ≠ 0:= by linarith
--   simp at g1
--   rcases g1 with ⟨⟨g1, g2⟩, g3⟩
--   -- Each of a, b, c must be either positive or negative
--   replace g1 : a < 0 ∨ a > 0:= by exact lt_or_gt_of_ne g1
--   replace g2 : b < 0 ∨ b > 0:= by exact lt_or_gt_of_ne g2
--   replace g3 : c < 0 ∨ c > 0:= by exact lt_or_gt_of_ne g3
--   -- Case analysis: first consider when a < 0
--   rcases g1 with g1 | g1
--   .
--     -- Case: a < 0
--     rcases g2 with g2 | g2
--     .
--       -- Case: a < 0, b < 0
--       rcases g3 with g3 | g3
--       .
--         -- Case: a < 0, b < 0, c < 0
--         -- This leads to a contradiction with a*b*c = 1
--         replace g1 : a * b > 0:= by exact mul_pos_of_neg_of_neg g1 g2
--         replace g1 : a * b * c < 0:= by exact mul_neg_of_pos_of_neg g1 g3
--         linarith
--       .
--         -- Case: a < 0, b < 0, c > 0
--         -- This leads to a contradiction with our assumption
--         replace g3 : 1 / c > 0:= by positivity
--         linarith
--     .
--       -- Case: a < 0, b > 0
--       rcases g3 with _ | g3
--       .
--         -- Case: a < 0, b > 0, c < 0
--         -- This leads to a contradiction with our assumption
--         replace g2 : 1 / b > 0:= by positivity
--         linarith
--       .
--         -- Case: a < 0, b > 0, c > 0
--         -- This leads to a contradiction with a*b*c = 1
--         replace g1 : a * b < 0:= by exact mul_neg_of_neg_of_pos g1 g2
--         replace g1 : a * b * c < 0:= by exact mul_neg_of_neg_of_pos g1 g3
--         linarith
--   .
--     -- Case: a > 0
--     rcases g2 with g2 | g2
--     .
--       -- Case: a > 0, b < 0
--       rcases g3 with g3 | g3
--       .
--         -- Case: a > 0, b < 0, c < 0
--         -- This leads to a contradiction with our assumption
--         replace g1 : 1 / a > 0:= by positivity
--         linarith
--       .
--         -- Case: a > 0, b < 0, c > 0
--         -- This leads to a contradiction with a*b*c = 1
--         replace g1 : a * b < 0:= by exact mul_neg_of_pos_of_neg g1 g2
--         replace g1 : a * b * c < 0:= by exact mul_neg_of_neg_of_pos g1 g3
--         linarith
--     .
--       -- Case: a > 0, b > 0
--       rcases g3 with g3 | g3
--       .
--         -- Case: a > 0, b > 0, c < 0
--         -- This leads to a contradiction with a*b*c = 1
--         replace g1 : a * b > 0:= by positivity
--         replace g1 : a * b * c < 0:= by exact mul_neg_of_pos_of_neg g1 g3
--         linarith
--       .
--         -- Case: a > 0, b > 0, c > 0 (main case)
--         -- Rewrite the expressions using the fact that a*b*c = 1
--         rw [show 1 / b = a * c by field_simp ; linarith] at H1
--         rw [show 1 / c = a * b by field_simp ; linarith] at H2
--         rw [show 1 / a = b * c by field_simp ; linarith] at H3
--         -- Simplify the inequalities
--         replace H1 : a * (2 - c) > 1:= by linarith
--         replace H2 : b * (2 - a) > 1:= by linarith
--         replace H3 : c * (2 - b) > 1:= by linarith
--         -- Prove that 2-a > 0
--         have g4 : 2 - a > 0:= by
--           by_contra H
--           simp at H
--           replace H : a - 2 ≥ 0:= by linarith
--           replace H : b * (a - 2) ≥ 0:= by positivity
--           linarith
--         -- Prove that 2-b > 0
--         have g5 : 2 - b > 0:= by
--           by_contra H
--           simp at H
--           replace H : b - 2 ≥ 0:= by linarith
--           replace H : c * (b - 2) ≥ 0:= by positivity
--           linarith
--         -- Prove that 2-c > 0
--         have g6 : 2 - c > 0:= by
--           by_contra H
--           simp at H
--           replace H : c - 2 ≥ 0:= by linarith
--           replace H : a * (c - 2) ≥ 0:= by positivity
--           linarith
--         -- Multiply the inequalities together
--         replace H1 : a * (2 - c) * (b * (2 - a)) > 1 * 1:= by refine Right.mul_lt_mul_of_nonneg H1 H2 (by positivity) (by positivity)
--         replace H1:= Right.mul_lt_mul_of_nonneg H1 H3 (by positivity) (by positivity)
--         simp at H1
--         clear H2 H3
--         -- Simplify the product using a*b*c = 1
--         rw [show a * (2 - c) * (b * (2 - a)) * (c * (2 - b)) = 1 * (2 - a) * (2 - b) * (2 - c) by rw [←h] ; ring] at H1
--         simp at H1
--         -- Apply AM-GM inequality: for positive reals, x^3 + y^3 + z^3 - 3xyz ≥ 0
--         have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
--           intro x y z hx hy hz
--           have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
--           rw [h1]
--           positivity
--         -- Reformulate the inequality in terms of cube roots
--         replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
--           intro x y z hx hy hz
--           specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
--           rw [show (x ^ ((1 : ℝ) / 3)) ^ 3 = (x ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
--           rw [show (y ^ ((1 : ℝ) / 3)) ^ 3 = (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
--           rw [show (z ^ ((1 : ℝ) / 3)) ^ 3 = (z ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
--           rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
--           rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
--           rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
--           rw [show (1 : ℝ) / 3 * 3 = 1 by ring_nf] at h1
--           rw [Eq.symm (Real.mul_rpow (by linarith) (by linarith))] at h1
--           rw [Eq.symm (Real.mul_rpow (by positivity) (by linarith))] at h1
--           simp at h1
--           simp
--           linarith
--         -- Apply the inequality to a, b, c
--         specialize h1 a b c g1 g2 g3
--         rw [h] at h1
--         simp at h1
--         -- Apply AM-GM inequality: for positive reals, xyz ≤ ((x+y+z)/3)^3
--         have h2 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x * y * z ≤ ((x + y + z) / 3) ^ 3:= by
--           intro x y z hx hy hz
--           have g1 : x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 ≥ 0:= by positivity
--           have g2 : (y + z) * (y - z) ^ 2 + (z + x) * (z - x) ^ 2 + (x + y) * (x - y) ^ 2 ≥ 0:= by positivity
--           linarith
--         -- Apply the inequality to (2-a), (2-b), (2-c)
--         specialize h2 (2 - a) (2 - b) (2 - c) g4 g5 g6
--         rw [show (2 - a + (2 - b) + (2 - c)) / 3 = 2 - (a + b + c) / 3 by linarith] at h2
--         have h3 : 2 - (a + b + c) / 3 ≥ 0:= by linarith
--         replace h1 : 2 - (a + b + c) / 3 ≤ 1:= by linarith
--         replace h1 : (2 - (a + b + c) / 3) ^ 3 ≤ 1:= by exact pow_le_one₀ h3 h1
--         -- Final contradiction
--         linarith
-- theorem inequalities_605069 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
--     Real.sqrt (a ^ 3 * b + a ^ 3 * c) + Real.sqrt (b ^ 3 * c + b ^ 3 * a) + Real.sqrt (c ^ 3 * a + c ^ 3 * b) ≥ 4 / 3 * (a * b + b * c + c * a) := by
--     norm_horn
--     horn_all
-- theorem inequalities_278942 {x : ℝ} :
--   (x ≠ 1 → (1 / (x - 1) ≤ x - 1 ↔ x ∈ Set.Ico 0 1 ∪ Set.Ici 2)) ∧
--   (x ≠ 4 → x ≠ - 2 → ((1 / (4 - x) + 2 / (2 + x) ≤ 1) ↔
--     x ∈ Set.Iio (-2 : ℝ) ∪ Set.Icc 1 2 ∪ Set.Ioi 4)) := by

--   constructor
--   intro h
--   constructor
--   intro h1
--   have : x - 1 > 0 := by sorry
--   norm_horn at h1
--   simp
--   horn_all
-- theorem algebra_605126 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
--     (habc : a * b * c = 1) :
--     a + b + c ≥ √((a + 2) * (b + 2) * (c + 2) / 3) := by
--     norm_horn (vars := [x1,x2,x3,x4]) (hyps := [hx1,hx2,hx3,hx4])
--     horn_all
-- theorem inequalities_604335 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
--     (h : x * y + y * z + z * x = 3 * x * y * z) :
--     x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≥ 2 * (x + y + z) - 3 ∧
--     (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x = 2 * (x + y + z) - 3 ↔ x = 1 ∧ y = 1 ∧ z = 1) := by
--   refine ⟨ ?_, ⟨?_,?_⟩⟩
--   horn_all
-- theorem inequalities_152982 :
--     {a : ℝ | 0 < a ∧ ∃! x : ℤ, x ^ 3 + 3 * x ^ 2 - x - 3 > 0 ∧ x ^ 2 - 2 * a * x - 1 ≤ 0} = Set.Ico (3 / 4) (4 / 3) := by
--   -- Show that x ^ 3 + 3 * x ^ 2 - x - 3 > 0 if and only if x = -2 or x ≥ 2.
--   have hlm (x : ℤ) : x ^ 3 + 3 * x ^ 2 - x - 3 > 0 ↔ x = -2 ∨ x ≥ 2 := by
--     rw [show x ^ 3 + 3 * x ^ 2 - x - 3 = (x + 3) * (x + 1) * (x - 1) by ring]
--     constructor

-- theorem inequalities_607513 :
-- IsGreatest {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ 4 - a ^ 2 ≥ 0 ∧ 4 - b ^ 2 ≥ 0 ∧ 4 - c ^ 2 ≥ 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 6 ∧ x = √(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2)} (3 * √2) ∧
-- IsLeast {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ 4 - a ^ 2 ≥ 0 ∧ 4 - b ^ 2 ≥ 0 ∧ 4 - c ^ 2 ≥ 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 6 ∧ x = √(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2)} (2 + √2):= by
--   constructor
--   .
--     constructor
--     .
--       simp
--       use √2
--       simp
--       use √2
--       simp
--       use √2
--       simp
--       norm_num
--       linarith
--     .
--       simp [upperBounds]
--       intro x a ha b hb c hc ha1 hb1 hc1 h hx
--       subst x
--       norm_horn (vars := [x1,x2,x3,x4]) (hyps:=[hx1,hx2,hx3,hx4])
--       horn_all

--       have h1 : ∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2):= by
--         intro x y z
--         have h1 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0:= by positivity
--         linarith
--       specialize h1 (√(4 - a ^ 2)) (√(4 - b ^ 2)) (√(4 - c ^ 2))
--       rw [Real.sq_sqrt (by linarith)] at h1
--       rw [Real.sq_sqrt (by linarith)] at h1
--       rw [Real.sq_sqrt (by linarith)] at h1
--       rw [show 3 * (4 - a ^ 2 + (4 - b ^ 2) + (4 - c ^ 2)) = 18 by linarith] at h1
--       rw [show (18 : ℝ) = (3 * √2) ^ 2 by ring_nf ; field_simp ; linarith] at h1
--       replace h1 : |√(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2)| ≤ |3 * √2|:= by exact sq_le_sq.mp h1
--       rw [show |√(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2)| = √(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2) by exact abs_of_nonneg (by positivity)] at h1
--       rw [show |3 * √2| = 3 * √2 by exact abs_of_nonneg (by positivity)] at h1
--       exact h1
--   .
--     constructor
--     .
--       simp
--       use 0
--       simp
--       use √2
--       simp
--       use 2
--       simp
--       norm_num
--       rw [show (4 : ℝ) = 2 ^ 2 by ring_nf]
--       field_simp
--     .
--       simp [lowerBounds]
--       intro x a ha b hb c hc ha1 hb1 hc1 h hx
--       subst x
--       have h1 : ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ 4 - a ^ 2 ≥ 0 ∧ 4 - b ^ 2 ≥ 0 ∧ 4 - c ^ 2 ≥ 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 6 ∧ a ^ 2 ≤ 2 → √(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2) ≥ 2 + √2:= by
--         intro a b c ⟨_, _, _, ha1, hb1, hc1, h, hx⟩
--         have h1 : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → √x + √y ≥ √(x + y):= by
--           intro x y hx hy
--           have h1 : (√x + √y) ^ 2 ≥ (√(x + y)) ^ 2:= by
--             ring_nf
--             rw [Real.sq_sqrt (by linarith)]
--             rw [Real.sq_sqrt (by linarith)]
--             rw [Real.sq_sqrt (by linarith)]
--             have h1 : √x * √y ≥ 0:= by positivity
--             linarith
--           replace h1 : |√x + √y| ≥ |√(x + y)|:= by exact sq_le_sq.mp h1
--           rw [show |√x + √y| = √x + √y by exact abs_of_nonneg (by positivity)] at h1
--           rw [show |√(x + y)| = √(x + y) by exact abs_of_nonneg (by positivity)] at h1
--           exact h1
--         specialize h1 (4 - b ^ 2) (4 - c ^ 2) (by linarith) (by linarith)
--         rw [show (4 - b ^ 2) + (4 - c ^ 2) = 2 + a ^ 2 by linarith] at h1
--         suffices √(4 - a ^ 2) + √(2 + a ^ 2) ≥ 2 + √2 by linarith
--         clear h1 h hb1 hc1
--         rw [Eq.symm (abs_of_nonneg (show √(4 - a ^ 2) + √(2 + a ^ 2) ≥ 0 by positivity))]
--         rw [Eq.symm (abs_of_nonneg (show 2 + √2 ≥ 0 by positivity))]
--         suffices (√(4 - a ^ 2) + √(2 + a ^ 2)) ^ 2 ≥ (2 + √2) ^ 2 by exact sq_le_sq.mp this
--         ring_nf
--         field_simp
--         ring_nf
--         suffices √(4 - a ^ 2) * √(2 + a ^ 2) ≥ 2 * √2 by linarith
--         rw [show √(4 - a ^ 2) * √(2 + a ^ 2) = √((4 - a ^ 2) * (2 + a ^ 2)) by field_simp]
--         rw [show 2 * √2 = √(2 ^ 2 * 2) by field_simp]
--         suffices (4 - a ^ 2) * (2 + a ^ 2) ≥ 2 ^ 2 * 2 by exact Real.sqrt_le_sqrt this
--         suffices a ^ 2 * (2 - a ^ 2) ≥ 0 by linarith
--         replace hx : 2 - a ^ 2 ≥ 0:= by linarith
--         positivity
--       have h2 : a ^ 2 ≤ 2 ∨ b ^ 2 ≤ 2 ∨ c ^ 2 ≤ 2:= by
--         by_contra H
--         simp at H
--         rcases H with ⟨H1, H2, H3⟩
--         linarith
--       rcases h2 with h2 | h2 | h2
--       .
--         exact h1 a b c ⟨ha, hb, hc, (by linarith), (by linarith), (by linarith), h, h2⟩
--       .
--         specialize h1 b c a ⟨hb, hc, ha, (by linarith), (by linarith), (by linarith), (by linarith), h2⟩
--         linarith
--       .
--         specialize h1 c a b ⟨hc, ha, hb, (by linarith), (by linarith), (by linarith), (by linarith), h2⟩
--         linarith
/- Let $a, b, c$ be positive real numbers, such that $(a b)^{2}+(b c)^{2}+(c a)^{2}=3$. Prove that
$$
\left(a^{2}-a+1\right)\left(b^{2}-b+1\right)\left(c^{2}-c+1\right) \geq 1 .
$$ -/
-- theorem inequalities_605868 {a b c : ℝ}
--     (h_apos : 0 < a)
--     (h_bpos : 0 < b)
--     (h_cpos : 0 < c)
--     (h : (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 = 3) :
--     (a ^ 2 - a + 1) * (b ^ 2 - b + 1) * (c ^ 2 - c + 1) ≥ 1 := by

--   -- $$ \left(a^{2}-a+1\right)\left(b^{2}-b+1\right)\left(c^{2}-c+1\right) \geq 1 \Leftrightarrow\left(a^{3}+1\right)\left(b^{3}+1\right)\left(c^{3}+1\right) \geq(a+1)(b+1)(c+1) . $$
--   suffices : (a ^ 3 + 1) * (b ^ 3 + 1) * (c ^ 3 + 1) ≥ (a + 1) * (b + 1) * (c + 1)
--   . apply sub_nonneg.mpr at this
--     apply sub_nonneg.mp
--     convert this using 1
--     sorry

--   -- Thus, we have
--   have r1 : (a ^ 3 + 1) * (b ^ 3 + 1) * (c ^ 3 + 1) - (a + 1) * (b + 1) * (c + 1) ≥ a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c + 1 - 2 * (a * b + b * c + c * a) := by
--     -- $\prod_{c y c}\left(a^{3}+1\right)-\prod_{c y c}(a+1)$
--     calc

--       -- $&=\sum_{c y c} a^{3}+\sum_{c y c}(a b)^{3}+(a b c)^{3}-\sum_{c y c} a-\sum_{c y c} a b-a b c$
--       _ = a ^ 3 + b ^ 3 + c ^ 3 + (a * b) ^ 3 + (b * c) ^ 3 + (c * a) ^ 3 + (a * b * c) ^ 3 - (a + b + c) - (a * b + b * c + c * a) - a * b * c := by
--         ring

--       -- $&= \ \sum_{c y c}\left(a^{3}+a\right)+\sum_{c y c}\left(a^{3} b^{3}+a b\right)+\left[(a b c)^{3}+1+1\right]-2 \sum_{c y c} a-2 \sum_{c y c} a b-a b c-2$
--       _ = ((a ^ 3 + a) + (b ^ 3 + b) + (c ^ 3 + c)) + ((a ^ 3 * b ^ 3 + a * b) + (b ^ 3 * c ^ 3 + b * c) + (c ^ 3 * a ^ 3 + c * a)) + ((a * b * c) ^ 3 + 1 + 1) - 2 * (a + b + c) - 2 * (a * b + b * c + c * a) - a * b * c - 2 := by
--         ring

--       -- using $AM \ge GM$, $&\geq \ 2 \sum_{c y c} a^{2}+2 \sum_{c y c} a^{2} b^{2}+2 a b c-2 \sum_{c y c} a-2 \sum_{c y c} a b-2$
--       _ ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 2 * a * b * c - 2 * (a + b + c) - 2 * (a * b + b * c + c * a) - 2 := by
--         sorry

--       -- $&= \ \sum_{c y c}\left(a^{2}-2 a+1\right)+\left(\sum_{c y c} a^{2}+2 a b c+1-2 \sum_{c y c} a b\right)$
--       _  = ((a ^ 2 - 2 * a + 1) + (b ^ 2 - 2 * b + 1) + (c ^ 2 - 2 * c + 1)) + ((a ^ 2 + b ^ 2 + c ^ 2) + 2 * a * b * c + 1 - 2 * (a * b + b * c + c * a)) := by
--         linarith only [h]

--       -- $&= \ \sum_{c y c}(a-1)^{2}+\left(\sum_{c y c} a^{2}+2 a b c+1-2 \sum_{c y c} a b\right)$
--       _ = ((a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2) + ((a ^ 2 + b ^ 2 + c ^ 2) + 2 * a * b * c + 1 - 2 * (a * b + b * c + c * a)) := by
--         ring

--       -- &\geq\left(\sum_{c y c} a^{2}+2 a b c+1-2 \sum_{c y c} a b\right) .
--       _ ≥ (a ^ 2 + b ^ 2 + c ^ 2) + 2 * a * b * c + 1 - 2 * (a * b + b * c + c * a) := by
--         apply le_add_of_nonneg_left
--         positivity

--   -- We will show that $\sum_{c y c} a^{2}+2 a b c+1-2 \sum_{c y c} a b \geq 0 \quad$ (1) for every $a, b, c \geq 0$.
--   suffices : (a ^ 2 + b ^ 2 + c ^ 2) + 2 * a * b * c + 1 - 2 * (a * b + b * c + c * a) ≥ 0
--   . -- which gives us $\prod_{\text {cyc }}\left(a^{3}+1\right)-\prod_{c y c}(a+1) \geq 0$ and, respectively, $\prod_{\text {cyc }}\left(a^{2}-a+1\right) \geq 1$.
--     linarith

--   -- Firstly, let us observe that $$ (1+2 a b c)(a+b+c)=(1+a b c+a b c)(a+b+c) \geq 9 \sqrt[3]{a^{2} b^{2} c^{2} a b c}=9 a b c $$ implying $$ 1+2 a b c \geq \frac{9 a b c}{a+b+c} $$
--   have r2 : 1 + 2 * a * b * c ≥ 9 * a * b * c / (a + b + c) := by
--     sorry

--   -- Then, using Schur's Inequality, (i.e. $\sum_{c y c} a(a-b)(a-c) \geq 0$, for any $a, b, c \geq 0$ ) we obtain that $$ \sum_{c y c} a^{2} \geq 2 \sum_{c y c} a b-\frac{9 a b c}{a+b+c} $$
--   have r3 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 2 * (a * b + b * c + c * a) - 9 * a * b * c / (a + b + c) := by
--     sorry

--   -- Returning to (1), we get:
--   have r4 : a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c + 1 - 2 * (a * b + b * c + c * a) ≥ 0 := by
--     calc
--       -- $&\geq\left(2 \sum_{c y c} a b-\frac{9 a b c}{a+b+c}\right)+2 a b c+1-2 \sum_{c y c} a b \\$
--       _ ≥ (2 * (a * b + b * c + c * a) - 9 * a * b * c / (a + b + c)) + 2 * a * b * c + 1 - 2 * (a * b + b * c + c * a) := by
--         sorry

--       -- $&= \ (1+2 a b c)-\frac{9 a b c}{a+b+c} \\$
--       _ = (1 + 2 * a * b * c) - 9 * a * b * c / (a + b + c) := by
--         ring

--       -- $&\geq 0$
--       _ ≥ 0 := by
--         sorry

--   exact r4
