import ELEM.Count.SplitBound
import ELEM.Primes.Mertens

/-!
# The auxiliary inert prime (companion Lemma 3): `ELEM.AuxPrime`

The elementary companion (twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae),
Lemma 3: for `q ≥ 2^15` there is an inert prime `R` with `q⁴ < R ≤ q⁵`. If there were none, every
prime in `(q⁴, q⁵]` would split (`q` itself is below the interval), so the whole weight
`∑_{q⁴ < p ≤ q⁵} log p / p`, which exceeds `L - 23/6` (`L = log q`) by Lemma 2
(`ELEM.Primes.log_sub_log_sub_lt_sum_Ioc`), would be at most the split weight (7) at `Y = q⁴`, `X = q⁵`:
`(π/(4√q)) (9 L² + 8 L) + 2 (4L + 1)/(√q q²)`. The companion's sufficient condition (9) then fails at
every `q ≥ q₀`.

For the monotonicity in `q` we avoid derivatives: `log x / √x ≤ log x₀ / √x₀` for
`x ≥ x₀` with `log x₀ ≥ 2`, from `log s ≤ s - 1` at `s = √(x/x₀)`. With `log q₀ < 21/2` and
`√q₀ > 180` (the companion's (3)) this gives `L/√q < 7/120`, and the inequality reduces to
`L (1 - 41/90 - 1/1000) < 23/6`, false for `L > 207/20`.
-/

set_option autoImplicit false

namespace ELEM.Count

open Real Finset

variable {q : ℕ}

/-- `log x / √x` decreases beyond `x₀` when `log x₀ ≥ 2` (no derivatives: `log s ≤ s - 1`). -/
theorem log_div_sqrt_le {x₀ x : ℝ} (hx₀ : 0 < x₀) (h2 : 2 ≤ log x₀) (hx : x₀ ≤ x) :
    log x / √x ≤ log x₀ / √x₀ := by
  have hx0 : 0 < x := hx₀.trans_le hx
  have hr : 0 < x / x₀ := div_pos hx0 hx₀
  set s := √(x / x₀) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hr
  have hs1 : 1 ≤ s := by rw [hs, Real.one_le_sqrt]; exact (one_le_div hx₀).mpr hx
  have hsx : √x = √x₀ * s := by
    rw [hs, ← Real.sqrt_mul hx₀.le, mul_div_cancel₀ _ hx₀.ne']
  have hlog : log x = log x₀ + 2 * log s := by
    have : x = x₀ * s ^ 2 := by rw [hs, Real.sq_sqrt hr.le]; field_simp
    rw [this, log_mul hx₀.ne' (pow_pos hs0 2).ne', log_pow]; push_cast; ring
  have hls : log s ≤ s - 1 := log_le_sub_one_of_pos hs0
  have hsq0 : 0 < √x₀ := Real.sqrt_pos.mpr hx₀
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hx0) hsq0, hsx, hlog]
  have : log x₀ + 2 * log s ≤ s * log x₀ := by nlinarith
  nlinarith

/-- `log 2^15 = 15 log 2`. -/
theorem log_q0 : log (32768 : ℝ) = 15 * log 2 := by
  rw [show (32768 : ℝ) = 2 ^ 15 by norm_num, log_pow]; norm_num

/-- `207/20 < log 2^15 < 21/2` (the companion's (3)). -/
theorem log_q0_bounds : 207 / 20 < log (32768 : ℝ) ∧ log (32768 : ℝ) < 21 / 2 := by
  rw [log_q0]
  constructor
  · linarith [log_two_gt_d9]
  · linarith [log_two_lt_d9]

/-- `180 < √2^15` (the companion's (3)). -/
theorem sqrt_q0_gt : 180 < √(32768 : ℝ) := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

/-- For `q ≥ 2^15`: `log q / √q < 7/120` (the companion's (4)). -/
theorem log_div_sqrt_lt (hq : (32768 : ℝ) ≤ q) : log q / √q < 7 / 120 := by
  obtain ⟨hl, hu⟩ := log_q0_bounds
  have h := log_div_sqrt_le (by norm_num) (by linarith) hq
  refine h.trans_lt ?_
  have hs := sqrt_q0_gt
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- **Lemma 3.** For `q` in the analytic setting there is an inert prime `R`, `q⁴ < R ≤ q⁵`. -/
theorem auxPrime : ELEM.AuxPrime := by
  classical
  intro q hq
  by_contra hno
  push Not at hno
  have hq32 : (32768 : ℝ) ≤ q := by exact_mod_cast hq.large
  have hq1 : 1 ≤ q := hq.prime.one_lt.le
  have hq0 : (0 : ℝ) < q := by linarith
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  set L := log (q : ℝ) with hL
  -- every prime in `(q⁴, q⁵]` splits
  have hset : (Ioc (q ^ 4) (q ^ 5)).filter Nat.Prime =
      (Ioc ⌊((q ^ 4 : ℕ) : ℝ)⌋₊ ⌊((q ^ 5 : ℕ) : ℝ)⌋₊).filter (fun k => k.Prime ∧ IsSplit q k) := by
    rw [Nat.floor_natCast, Nat.floor_natCast]
    ext p
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h4, h5⟩, hp⟩
      refine ⟨⟨h4, h5⟩, hp, fun hin => ?_, ?_⟩
      · exact absurd (hno p hp hin h4) (not_lt.mpr h5)
      · rintro rfl
        have : p ≤ p ^ 4 := Nat.le_self_pow (by norm_num) p
        omega
    · rintro ⟨h, hp, _⟩
      exact ⟨h, hp⟩
  -- the lower bound from Lemma 2
  have hlow := ELEM.Primes.log_sub_log_sub_lt_sum_Ioc (m := q ^ 4) (n := q ^ 5)
    (Nat.one_le_pow _ _ (by omega)) (Nat.pow_le_pow_right (by omega) (by norm_num))
  -- the upper bound (7) at `Y = q⁴`, `X = q⁵`
  have ha : exp 1 ≤ ((q ^ 4 : ℕ) : ℝ) := by
    push_cast
    have : (q : ℝ) ≤ (q : ℝ) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    linarith [exp_one_lt_three]
  have hab : ((q ^ 4 : ℕ) : ℝ) ≤ ((q ^ 5 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega) (by norm_num)
  have hup := split_weight_le hq ha hab
  rw [← hset] at hup
  have h4 : log ((q ^ 4 : ℕ) : ℝ) = 4 * L := by push_cast; rw [log_pow]; norm_num [hL]
  have h5 : log ((q ^ 5 : ℕ) : ℝ) = 5 * L := by push_cast; rw [log_pow]; norm_num [hL]
  have hs4 : √((q ^ 4 : ℕ) : ℝ) = (q : ℝ) ^ 2 := by
    push_cast
    rw [show (q : ℝ) ^ 4 = ((q : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [h4, h5, hs4] at hup
  rw [h4, h5] at hlow
  -- numerics
  obtain ⟨hl0, _⟩ := log_q0_bounds
  have hLq : 207 / 20 < L := hl0.trans_le (log_le_log (by norm_num) hq32)
  have hr : L ≤ 7 / 120 * √q := by
    have := log_div_sqrt_lt hq32
    rw [div_lt_iff₀ hsq] at this
    linarith
  have hu : 180 ≤ √(q : ℝ) := sqrt_q0_gt.le.trans (Real.sqrt_le_sqrt hq32)
  have hπ := pi_lt_sixteen_fifths
  have hT1 : π / (4 * √q) * ((5 * L) ^ 2 - (4 * L) ^ 2 + 2 * (4 * L)) ≤ 41 / 90 * L := by
    have hpos : 0 ≤ (5 * L) ^ 2 - (4 * L) ^ 2 + 2 * (4 * L) := by nlinarith
    calc π / (4 * √q) * ((5 * L) ^ 2 - (4 * L) ^ 2 + 2 * (4 * L))
        = π * (9 * L ^ 2 + 8 * L) / (4 * √q) := by ring
      _ ≤ 41 / 90 * L := by
          rw [div_le_iff₀ (by positivity)]
          have h9 : 9 * L ^ 2 + 8 * L ≤ (21 / 40 + 2 / 45) * L * √q := by nlinarith
          have hp0 : 0 ≤ 9 * L ^ 2 + 8 * L := by nlinarith
          have : π * (9 * L ^ 2 + 8 * L) ≤ 16 / 5 * (9 * L ^ 2 + 8 * L) :=
            mul_le_mul_of_nonneg_right hπ.le hp0
          nlinarith
  have hT2 : 2 * (4 * L + 1) / (√q * (q : ℝ) ^ 2) ≤ L / 1000 := by
    have hq2 : (32768 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hK : 10000 ≤ √q * (q : ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end ELEM.Count
