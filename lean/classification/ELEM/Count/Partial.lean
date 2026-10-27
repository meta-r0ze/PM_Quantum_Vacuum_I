import Mathlib.NumberTheory.AbelSummation
import ELEM.Count.Lattice

/-!
# Partial summation against the split-prime count (companion (7))

The elementary companion (twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae),
section 3, turns the count `π₊(t) ≤ G(t) = π t/(2√q) + √t/√q` of `ELEM.Count.Lattice` into a bound for
the weighted sum of `f(p) = log p / p` over the split primes `p ∈ (Y, X]`, by a Stieltjes integral.
We use Mathlib's Abel summation (`sum_mul_eq_sub_sub_integral_mul`) with `c` the indicator of the
split primes:

`∑_{Y < p ≤ X split} f(p) = f(X) π₊(X) - f(Y) π₊(Y) - ∫_Y^X f'(t) π₊(t) dt`.

For `t ≥ e` we have `f'(t) = (1 - log t)/t² ≤ 0`, so `π₊ ≤ G` bounds the integral term, and
`∫ f' G` is computed by the fundamental theorem of calculus with the antiderivative
`H(t) = (π/(2√q)) (log t - (log t)²/2) + 2 (log t + 1)/(√q √t)`. Dropping the two nonpositive terms
`-f(Y) π₊(Y)` and `-(log X + 2)/(√q √X)`, as the companion does, gives (7):

`∑_{Y < p ≤ X split} log p / p ≤ (π/(4√q)) ((log X)² - (log Y)² + 2 log Y) + 2 (log Y + 1)/(√q √Y)`.
-/

set_option autoImplicit false

namespace ELEM.Count

open Real Finset MeasureTheory

variable {q : ℕ}

open Classical in
/-- The indicator of the split primes, the coefficient sequence of the Abel summation. -/
noncomputable def splitInd (q : ℕ) (k : ℕ) : ℝ := if k.Prime ∧ IsSplit q k then 1 else 0

/-- The majorant of `π₊(t)` from `ELEM.Count.card_split_le`. -/
noncomputable def countBound (q : ℕ) (t : ℝ) : ℝ := π * t / (2 * √q) + √t / √q

/-- The antiderivative of `f'(t) G(t)`. -/
noncomputable def antiderivH (q : ℕ) (t : ℝ) : ℝ :=
  π / (2 * √q) * (log t - log t ^ 2 / 2) + 2 * (log t + 1) / (√q * √t)

theorem sum_splitInd_le (hq : AnalyticSetting q) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, splitInd q k ≤ countBound q t := by
  classical
  have h := card_split_le hq ht
  unfold splitInd countBound
  rw [sum_boole]
  convert h

theorem sum_splitInd_nonneg (q : ℕ) (t : ℝ) : 0 ≤ ∑ k ∈ Icc 0 ⌊t⌋₊, splitInd q k :=
  sum_nonneg fun k _ => by unfold splitInd; split_ifs <;> norm_num

/-- `(log t / t)' = (1 - log t)/t²`. -/
theorem hasDerivAt_log_div {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => log x / x) ((1 - log t) / t ^ 2) t := by
  have := (Real.hasDerivAt_log ht.ne').div (hasDerivAt_id' t) ht.ne'
  convert this using 1
  field_simp

/-- `H' = f' G`. -/
theorem hasDerivAt_antiderivH (hq0 : (0 : ℝ) < q) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (antiderivH q) ((1 - log t) / t ^ 2 * countBound q t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hst : 0 < √t := Real.sqrt_pos.mpr ht
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have h1 := ((hl.sub ((hl.pow 2).div_const 2)).const_mul (π / (2 * √(q : ℝ))))
  have h2 := ((hl.add_const 1).const_mul 2).div (hs.const_mul (√(q : ℝ)))
    (mul_ne_zero hsq.ne' hst.ne')
  have := h1.add h2
  unfold antiderivH
  convert this using 1
  unfold countBound
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 := ⟨√t, hst, (Real.sq_sqrt ht.le).symm⟩
  rw [Real.sqrt_sq hs0.le]
  generalize log (s ^ 2) = L
  field_simp
  ring

/-- `f(X) G(X) - H(X) = (π/(4√q)) (log X)² - (log X + 2)/(√q √X)`. -/
theorem boundary_identity (hq0 : (0 : ℝ) < q) {t : ℝ} (ht : 0 < t) :
    log t / t * countBound q t - antiderivH q t =
      π / (4 * √q) * log t ^ 2 - (log t + 2) / (√q * √t) := by
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  unfold countBound antiderivH
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨√t, Real.sqrt_pos.mpr ht, (Real.sq_sqrt ht.le).symm⟩
  rw [Real.sqrt_sq hs0.le]
  generalize log (s ^ 2) = L
  field_simp
  ring

open Classical in
/-- **(7).** For `e ≤ Y ≤ X`, the weight of the split primes in `(Y, X]` is at most
`(π/(4√q)) ((log X)² - (log Y)² + 2 log Y) + 2 (log Y + 1)/(√q √Y)`. -/
theorem split_weight_le (hq : AnalyticSetting q) {a b : ℝ} (ha : exp 1 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun k => k.Prime ∧ IsSplit q k), log (p : ℝ) / p ≤
      π / (4 * √q) * (log b ^ 2 - log a ^ 2 + 2 * log a) + 2 * (log a + 1) / (√q * √a) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.prime.pos
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have ha0 : 0 < a := (exp_pos 1).trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hloga : 1 ≤ log a := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) ha
  set f : ℝ → ℝ := fun x => log x / x with hf
  have hderiv : ∀ t, 0 < t → deriv f t = (1 - log t) / t ^ 2 :=
    fun t ht => (hasDerivAt_log_div ht).deriv
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha0.trans_le ht.1
  have hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t :=
    fun t ht => (hasDerivAt_log_div (hpos t ht)).differentiableAt
  have hcont : ContinuousOn (fun t => (1 - log t) / t ^ 2) (Set.Icc a b) := by
    refine ContinuousOn.div (continuousOn_const.sub (Real.continuousOn_log.mono fun t ht => ?_))
      (continuousOn_pow 2) fun t ht => (pow_pos (hpos t ht) 2).ne'
    exact (hpos t ht).ne'
  have hf_int : IntegrableOn (deriv f) (Set.Icc a b) :=
    (hcont.integrableOn_Icc).congr_fun (fun t ht => (hderiv t (hpos t ht)).symm) measurableSet_Icc
  have abel := sum_mul_eq_sub_sub_integral_mul (splitInd q) ha0.le hab hf_diff hf_int
  -- the left side is the weighted sum over split primes
  have hlhs : ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun k => k.Prime ∧ IsSplit q k), log (p : ℝ) / p =
      ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * splitInd q k := by
    rw [sum_filter]
    refine sum_congr rfl fun k _ => ?_
    simp only [hf, splitInd]
    split_ifs <;> simp
  rw [hlhs, abel]
  set N : ℝ → ℝ := fun t => ∑ k ∈ Icc 0 ⌊t⌋₊, splitInd q k with hN
  -- the integral term
  have hGc : ContinuousOn (countBound q) (Set.Icc a b) := by
    unfold countBound; fun_prop
  have hint_G : IntegrableOn (fun t => deriv f t * countBound q t) (Set.Icc a b) :=
    hf_int.mul_continuousOn hGc isCompact_Icc
  have hint_N : IntegrableOn (fun t => deriv f t * N t) (Set.Icc a b) :=
    integrableOn_mul_sum_Icc (splitInd q) ha0.le hf_int
  have hmono : ∫ t in Set.Ioc a b, deriv f t * countBound q t ≤
      ∫ t in Set.Ioc a b, deriv f t * N t := by
    refine setIntegral_mono_on (hint_G.mono_set Set.Ioc_subset_Icc_self)
      (hint_N.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := ha0.trans ht.1
    have hd : deriv f t ≤ 0 := by
      rw [hderiv t ht0]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg t)
      have : log a ≤ log t := log_le_log ha0 ht.1.le
      linarith
    exact mul_le_mul_of_nonpos_left (sum_splitInd_le hq ht0.le) hd
  have hftc : ∫ t in Set.Ioc a b, deriv f t * countBound q t = antiderivH q b - antiderivH q a := by
    rw [← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      rw [hderiv t (hpos t ht)]
      exact hasDerivAt_antiderivH hq0 (hpos t ht)
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hint_G
  -- the boundary terms
  have hfb : 0 ≤ f b := div_nonneg (log_nonneg (by linarith [one_le_exp (zero_le_one' ℝ)])) hb0.le
  have hfa : 0 ≤ f a := div_nonneg (by linarith) ha0.le
  have hNb : f b * N b ≤ f b * countBound q b :=
    mul_le_mul_of_nonneg_left (sum_splitInd_le hq hb0.le) hfb
  have hNa : 0 ≤ f a * N a := mul_nonneg hfa (sum_splitInd_nonneg q a)
  have hid := boundary_identity hq0 hb0
  have hHa : antiderivH q a =
      π / (4 * √q) * (2 * log a - log a ^ 2) + 2 * (log a + 1) / (√q * √a) := by
    unfold antiderivH; ring
  have hdrop : 0 ≤ (log b + 2) / (√q * √b) := by
    have : 0 ≤ log b := log_nonneg (by linarith [one_le_exp (zero_le_one' ℝ)])
    positivity
  simp only [hf] at hid hNb hNa ⊢
  have : π / (4 * √q) * (log b ^ 2 - log a ^ 2 + 2 * log a) =
      π / (4 * √q) * log b ^ 2 + π / (4 * √q) * (2 * log a - log a ^ 2) := by ring
  linarith

end ELEM.Count
