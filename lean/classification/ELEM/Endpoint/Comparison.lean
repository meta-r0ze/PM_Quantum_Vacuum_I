import ELEM.Hypotheses
import ELEM.Endpoint.Monotone

/-!
# ELEM.Endpoint.Comparison: the endpoint contradiction, `ELEM.Endpoint`

This proves the fixed statement `ELEM.Endpoint` (Hypotheses.lean): the real-number contradiction
of the elementary companion's section 5, its (15)-(17) (twinheterodox/tenth-discriminant,
companions/elementary, commit 64694aae, which supplies the explicit constants and the shape of the
final comparison). It is pure real arithmetic: nothing below is about primes.

Notation: `L = log q`, `x = log R`, `u = √q`, `v = 4/(5u)`. The argument, in our own arrangement:

* From `q⁴ < R ≤ q⁵`, `4L < x ≤ 5L`.
* `ELEM.Endpoint.log_le_of_large` (no derivatives) gives `L ≤ (7/120) u` for every `q ≥ 2^15`, hence
  `v L ≤ 7/150`.
* The quadratic term of (8) is controlled on `[4L, 5L]` by an identity instead of concavity:
  `v x² = (x - 4L) · v (x + 4L) + 16 L · (v L) ≤ (21/50)(x - 4L) + (112/150) L`.
* The error terms `(5L + 4)/q`, `I/(2S)` and `6x/R` are each below `1/100`; the source's sharper
  `1/500` is not needed (`I/(2S)` is bounded with the UPPER bound for `I`, since it is subtracted).
* Chaining Lemma 2 at `R`, the decomposition of `A`, (8), the size bound and the divisibility bound
  leaves `(7/400) x + (323/480) L < 121/18 + (25/24) log 2 + 1/25`. With `x > 4L` the left side
  exceeds `(1783/2400) L`, and `L ≥ 15 log 2 > 207/20` makes it more than `7.68`, while the right side
  is below `7.49` by `log 2 < 0.6931471808`.

The coefficient `1783/2400` is `143/96 - 56/75`, the companion's endpoint margin read as
`(143/96 - (64/5)(7/120)) L`; with the `6 (log R)/R` of the Leibniz size bound the endpoint closes
with room to spare. The only transcendental inputs are Mathlib's `log 2` bounds.
-/

set_option autoImplicit false

open Real

namespace ELEM.Endpoint

/-- **The closing rational comparison.** With `L ≥ 15 log 2` and Mathlib's
`0.6931471803 < log 2 < 0.6931471808`, the left side `(1783/2400) L` of the final inequality beats its
right side `121/18 + (25/24) log 2 + 1/25`. Checked by `norm_num` over `ℝ`. (The companion's form of the
same step divides by `L` and compares `56/75 + 50/69 = 846/575 < 143/96`.) -/
theorem final_comparison :
    121 / 18 + 25 / 24 * (0.6931471808 : ℝ) + 1 / 25 < 1783 / 2400 * (15 * 0.6931471803) := by
  norm_num

/-- The companion's endpoint comparison, recorded for cross-reference (not used in the proof):
`846/575 < 143/96`, with margin `1009/55200`. -/
theorem companion_comparison :
    (846 / 575 : ℚ) < 143 / 96 ∧ (143 / 96 : ℚ) - 846 / 575 = 1009 / 55200 := by
  norm_num

/-- **(15)-(17): the endpoint contradiction.** `ELEM.Endpoint` exactly as fixed in Hypotheses.lean. -/
theorem endpoint : ELEM.Endpoint := by
  intro q R S A I Sp Y hq hR4 hR5 hS hS0 hSp hA hA1 hA2 hSpb hY1 hY2
  -- basic positivity
  have hq0 : 0 < q := by linarith
  have hq4 : 0 < q ^ 4 := by positivity
  have hR0 : 0 < R := lt_trans hq4 hR4
  -- `L = log q` and its lower bound `L ≥ 15 log 2 > 207/20`
  have hL : 15 * Real.log 2 ≤ Real.log q := by
    have h : Real.log ((2 : ℝ) ^ 15) ≤ Real.log q :=
      (Real.log_le_log_iff (by norm_num) hq0).2 (by norm_num; linarith)
    rwa [Real.log_pow] at h
  have hl2lo := Real.log_two_gt_d9
  have hl2hi := Real.log_two_lt_d9
  have hL0 : 0 ≤ Real.log q := by linarith
  -- `4L < x ≤ 5L`, `x = log R`
  have hx4 : 4 * Real.log q < Real.log R := by
    have h := Real.log_lt_log hq4 hR4
    rwa [Real.log_pow] at h
  have hx5 : Real.log R ≤ 5 * Real.log q := by
    have h := (Real.log_le_log_iff hR0 (by positivity)).2 hR5
    rwa [Real.log_pow] at h
  -- monotonicity: `L ≤ (7/120) √q`, `√q ≤ q / 181`, `L ≤ (7/21720) q`
  have hu : (181 : ℝ) ≤ √q := le_sqrt_of_large hq
  have hu0 : 0 < √q := by linarith
  have hLu : Real.log q ≤ 7 / 120 * √q := log_le_of_large hq
  have hLq : Real.log q ≤ 7 / 21720 * q := log_le_mul_of_large hq
  -- `x ≤ q`
  have hxq : Real.log R ≤ q := by linarith
  -- `1000 q ≤ q⁴ < R`
  have hq1000 : 1000 * q ≤ q ^ 4 := by
    have h3 : (1000 : ℝ) ≤ q ^ 3 := by
      have : (32768 : ℝ) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq 3
      linarith
    have : q ^ 4 = q * q ^ 3 := by ring
    rw [this]
    nlinarith
  have hRq : 1000 * q < R := lt_of_le_of_lt hq1000 hR4
  -- the quadratic term of (8): `v x² ≤ (21/50) x - (14/15) L`, `v = 4/(5√q)`
  set v : ℝ := 4 / (5 * √q) with hv
  have hv0 : 0 < v := by positivity
  have hvL : v * Real.log q ≤ 7 / 150 := by
    have h : v * Real.log q ≤ v * (7 / 120 * √q) := mul_le_mul_of_nonneg_left hLu hv0.le
    have e : v * (7 / 120 * √q) = 7 / 150 := by
      rw [hv]; field_simp; ring
    linarith
  have hquad : v * Real.log R ^ 2 ≤ 21 / 50 * Real.log R - 14 / 15 * Real.log q := by
    have hd : 0 ≤ Real.log R - 4 * Real.log q := by linarith
    have hs : v * (Real.log R + 4 * Real.log q) ≤ 21 / 50 := by
      have : v * (Real.log R + 4 * Real.log q) ≤ v * (9 * Real.log q) :=
        mul_le_mul_of_nonneg_left (by linarith) hv0.le
      linarith
    have p1 := mul_le_mul_of_nonneg_left hs hd
    have p2 := mul_le_mul_of_nonneg_left hvL hL0
    have e : v * Real.log R ^ 2 =
        (Real.log R - 4 * Real.log q) * (v * (Real.log R + 4 * Real.log q)) +
          16 * (Real.log q * (v * Real.log q)) := by ring
    rw [e]
    linarith
  -- the small error terms, each below `1/100`
  have hE1 : 4 * (Real.log q + 1) / q ≤ 1 / 100 := by
    rw [div_le_iff₀ hq0]; linarith
  have hE2 : Real.log q / q ≤ 1 / 100 := by
    rw [div_le_iff₀ hq0]; linarith
  have hE3 : 6 * Real.log R / R ≤ 1 / 100 := by
    rw [div_le_iff₀ hR0]; linarith
  -- `I < x + 3/2` (as `Sp ≥ 0`, `L/q ≥ 0`), hence `I/(2S) ≤ 1/100`
  have hLq0 : 0 ≤ Real.log q / q := div_nonneg hL0 hq0.le
  have hI : I < Real.log R + 3 / 2 := by linarith
  have hE4 : I / (2 * S) ≤ 1 / 100 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- assemble (15)-(17); the constants close by `final_comparison`
  have hfin := final_comparison
  linarith

end ELEM.Endpoint
