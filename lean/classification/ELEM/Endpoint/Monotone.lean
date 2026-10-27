import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# ELEM.Endpoint.Monotone: `log q ≤ (7/120) √q` for every `q ≥ 2^15`

The endpoint comparison (the companion's (16)-(17)) needs `(log q)/√q ≤ 7/120`,
not only at `q₀ = 2^15` but for every larger `q`. The elementary companion
(twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae) gets this from the sign of
a derivative. Here there are no derivatives: write `u = √q`,
so `u ≥ 181` (as `181² = 32761 ≤ 2^15`), and apply `log t ≤ t - 1` at `t = u / 181`. Together with
`2 log 181 < 15 log 2` (from `181² < 2^15`) and Mathlib's `log 2 < 0.6931471808`, this gives a bound
`log q ≤ 15 log 2 - 2 + 2u/181` that is linear in `u` with slope below `7/120`, and the bound holds
already at `u = 181`.

The only transcendental input is `Real.log_two_lt_d9`.
-/

set_option autoImplicit false

open Real

namespace ELEM.Endpoint

/-- `181 ≤ √q` for `q ≥ 2^15`. -/
theorem le_sqrt_of_large {q : ℝ} (hq : 32768 ≤ q) : (181 : ℝ) ≤ √q :=
  (Real.le_sqrt (by norm_num) (by linarith)).2 (by norm_num; linarith)

/-- `2 log 181 < 15 log 2`, from `181² = 32761 < 32768 = 2^15`. -/
theorem two_log_181_lt : 2 * Real.log 181 < 15 * Real.log 2 := by
  have h : Real.log ((181 : ℝ) ^ 2) < Real.log ((2 : ℝ) ^ 15) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  exact h

/-- **Monotonicity, without derivatives.** For every real `q ≥ 2^15`, `log q ≤ (7/120) √q`.
At `q = 2^15` this is `15 log 2 ≈ 10.397 ≤ 10.56`. -/
theorem log_le_of_large {q : ℝ} (hq : 32768 ≤ q) : Real.log q ≤ 7 / 120 * √q := by
  have hu : (181 : ℝ) ≤ √q := le_sqrt_of_large hq
  have hu0 : 0 < √q := by linarith
  -- `log q = 2 log √q`
  have hlog : Real.log q = 2 * Real.log √q := by
    rw [Real.log_sqrt (by linarith)]; ring
  -- `log √q = log 181 + log (√q / 181) ≤ log 181 + √q / 181 - 1`
  have hdiv : Real.log (√q / 181) = Real.log √q - Real.log 181 :=
    Real.log_div hu0.ne' (by norm_num)
  have hle : Real.log (√q / 181) ≤ √q / 181 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h181 := two_log_181_lt
  have h2 := Real.log_two_lt_d9
  rw [hlog]
  linarith

/-- `√q ≤ q / 181` for `q ≥ 2^15` (as `q = √q · √q ≥ 181 √q`). -/
theorem sqrt_le_div_of_large {q : ℝ} (hq : 32768 ≤ q) : √q ≤ q / 181 := by
  have hu : (181 : ℝ) ≤ √q := le_sqrt_of_large hq
  have hsq : √q * √q = q := Real.mul_self_sqrt (by linarith)
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

/-- `log q ≤ (7/21720) q` for `q ≥ 2^15`: the two bounds above combined. -/
theorem log_le_mul_of_large {q : ℝ} (hq : 32768 ≤ q) : Real.log q ≤ 7 / 21720 * q := by
  have h1 := log_le_of_large hq
  have h2 := sqrt_le_div_of_large hq
  linarith

end ELEM.Endpoint
