import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import ELEM.Count.Partial

/-!
# The split-prime bound (companion (8)): `ELEM.SplitBound`

The elementary companion (twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae),
section 3, takes `Y = q/4` in (7). There are no split primes `p ≤ q/4`: by (1) every prime with
`4p < q` is inert, and `4p ≠ q` as `q` is odd. Since `log (q/4) > 2`, the term
`-(log Y)² + 2 log Y` is negative; `√q · √(q/4) = q/2` turns the second term into
`4 (log (q/4) + 1)/q ≤ 4 (log q + 1)/q`; and `π < 16/5` gives the coefficient `4/5`.
-/

set_option autoImplicit false

namespace ELEM.Count

open Real Finset

variable {q : ℕ}

/-- `e < 3`. -/
theorem exp_one_lt_three : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)

/-- `π < 16/5`. -/
theorem pi_lt_sixteen_fifths : π < 16 / 5 := lt_trans pi_lt_d2 (by norm_num)

/-- `2 < log 8`, from `e² < 8`. -/
theorem two_lt_log_eight : 2 < log 8 := by
  rw [lt_log_iff_exp_lt (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
  have := exp_one_lt_d9
  have h0 := exp_pos 1
  nlinarith

open Classical in
/-- The split primes `p ≤ X` all exceed `q/4`, so `S₊(X)` is the split weight of `(q/4, X]`. -/
theorem splus_eq_sum_Ioc (hq : AnalyticSetting q) (X : ℝ) :
    Splus q X = ∑ p ∈ (Ioc ⌊(q : ℝ) / 4⌋₊ ⌊X⌋₊).filter (fun k => k.Prime ∧ IsSplit q k),
      log (p : ℝ) / p := by
  unfold Splus
  refine sum_congr ?_ fun _ _ => rfl
  ext p
  have hfl : ⌊(q : ℝ) / 4⌋₊ = q / 4 := by
    exact_mod_cast Nat.floor_div_eq_div (K := ℝ) q 4
  simp only [mem_filter, Nat.mem_primesLE, mem_Ioc, hfl]
  constructor
  · rintro ⟨⟨hpX, hp⟩, hs⟩
    refine ⟨⟨?_, hpX⟩, hp, hs⟩
    have h4 : ¬ 4 * p < q := fun h => hs.1 (hq.inert_of_lt p hp h)
    have h8 := hq.mod_eight
    have : 4 * p ≠ q := by omega
    omega
  · rintro ⟨⟨_, hpX⟩, hp, hs⟩
    exact ⟨⟨hpX, hp⟩, hs⟩

/-- **(8).** `S₊(X) ≤ (4/(5√q)) (log X)² + 4 (log q + 1)/q` for `X ≥ q/4`. -/
theorem splitBound : ELEM.SplitBound := by
  intro q hq X hX
  have hq32 : (32768 : ℝ) ≤ q := by exact_mod_cast hq.large
  have hq0 : (0 : ℝ) < q := by linarith
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  set a : ℝ := (q : ℝ) / 4 with ha_def
  have ha8 : 8 ≤ a := by rw [ha_def]; linarith
  have ha : exp 1 ≤ a := by linarith [exp_one_lt_three]
  have h7 := split_weight_le hq ha hX
  rw [← splus_eq_sum_Ioc hq X] at h7
  -- `log a ≥ 2`
  have hloga : 2 ≤ log a := (two_lt_log_eight.trans_le (log_le_log (by norm_num) ha8)).le
  have hlogaq : log a ≤ log q := log_le_log (by linarith) (by rw [ha_def]; linarith)
  -- `√q √(q/4) = q/2`
  have hsqa : √(q : ℝ) * √a = q / 2 := by
    rw [ha_def, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
      ← mul_div_assoc, Real.mul_self_sqrt hq0.le]
  rw [hsqa] at h7
  -- the first term
  have hX2 : 0 ≤ log X ^ 2 := sq_nonneg _
  have hfirst : π / (4 * √q) * (log X ^ 2 - log a ^ 2 + 2 * log a) ≤ 4 / (5 * √q) * log X ^ 2 := by
    have hneg : log X ^ 2 - log a ^ 2 + 2 * log a ≤ log X ^ 2 := by nlinarith
    have hπ := pi_lt_sixteen_fifths
    have hc : π / (4 * √q) ≤ 4 / (5 * √q) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc π / (4 * √q) * (log X ^ 2 - log a ^ 2 + 2 * log a)
        ≤ π / (4 * √q) * log X ^ 2 :=
          mul_le_mul_of_nonneg_left hneg (div_nonneg pi_pos.le (by positivity))
      _ ≤ 4 / (5 * √q) * log X ^ 2 := mul_le_mul_of_nonneg_right hc hX2
  -- the second term
  have hsecond : 2 * (log a + 1) / ((q : ℝ) / 2) ≤ 4 * (log q + 1) / q := by
    rw [div_le_div_iff₀ (by positivity) hq0]
    nlinarith
  linarith

end ELEM.Count
