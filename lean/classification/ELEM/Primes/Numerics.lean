import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical facts about logarithms used by the prime estimates

Every bound here is derived from Mathlib's `Real.log_two_lt_d9`, `Real.log_two_gt_d9` and
`Real.exp_one_lt_d9` by exact rational arithmetic, or from an integer comparison such as
`3 ^ 3 < 2 ^ 5`.
-/

namespace ELEM.Primes

open Real

theorem log_four_eq : log 4 = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

theorem log_four_lt_three_halves : log 4 < 3 / 2 := by
  rw [log_four_eq]
  linarith [log_two_lt_d9]

/-- `log 3 < (5/3) log 2`, from `3 ^ 3 < 2 ^ 5`. -/
theorem log_three_lt : log 3 < 5 / 3 * log 2 := by
  have h : log ((3 : ℝ) ^ 3) < log ((2 : ℝ) ^ 5) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- `log 5 < (7/3) log 2`, from `5 ^ 3 < 2 ^ 7`. -/
theorem log_five_lt : log 5 < 7 / 3 * log 2 := by
  have h : log ((5 : ℝ) ^ 3) < log ((2 : ℝ) ^ 7) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- `3/2 < log 7`, from `exp 3 < 49`. -/
theorem three_halves_lt_log_seven : 3 / 2 < log 7 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h3 : exp 3 < 49 := by
    have he : exp 3 = exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he]
    have h1 := exp_one_lt_d9
    have h0 := (exp_pos 1).le
    calc exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 := by gcongr
      _ < 49 := by norm_num
  have hsq : exp (3 / 2) ^ 2 = exp 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  nlinarith [exp_pos (3 / 2)]

end ELEM.Primes
