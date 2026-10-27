import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Algebra.InfiniteSum.Real
import ELEM.Primes.Numerics

/-!
# The constant `B = ∑_p (log p) / p² < 2/3`

The elementary companion (twinheterodox/tenth-discriminant, companions/elementary, commit
64694aae), Lemma 2, bounds `B` by comparing the odd terms with an integral and uses
`log 3 < 11/10`. We use a discrete telescoping comparison instead: for real `n ≥ 7`,
`2 (log n) / n² ≤ G(n - 2) - G(n)` with `G(x) = (log x + 1) / x`, an antiderivative of
`-(log x) / x²`. Summing over odd `n ≥ 7` and keeping the terms at `2, 3, 5` exactly gives

  `∑_{p ∈ s} (log p) / p² ≤ (log 2)/4 + (log 3)/9 + (log 5)/25 + (log 5 + 1)/10`

for every finite set `s` of primes, and the right side is below `2/3` using only
`log 3 < (5/3) log 2`, `log 5 < (7/3) log 2` and Mathlib's bound on `log 2`.
The constant `2/3` is the companion's.
-/

namespace ELEM.Primes

open Real Finset

/-- The explicit majorant of `∑_p (log p) / p²`. -/
noncomputable def sumLogDivSqBound : ℝ :=
  log 2 / 4 + log 3 / 9 + log 5 / 25 + (log 5 + 1) / 10

theorem sumLogDivSqBound_lt : sumLogDivSqBound < 2 / 3 := by
  unfold sumLogDivSqBound
  linarith [log_three_lt, log_five_lt, log_two_lt_d9]

/-- The telescoping step: for `n ≥ 7`, `2 (log n)/n² ≤ G(n-2) - G(n)`,
`G(x) = (log x + 1)/x`. -/
theorem two_mul_log_div_sq_le {n : ℝ} (hn : 7 ≤ n) :
    2 * (log n / n ^ 2) ≤ (log (n - 2) + 1) / (n - 2) - (log n + 1) / n := by
  have ha : 0 < n - 2 := by linarith
  have hn0 : 0 < n := by linarith
  -- `log n - log (n - 2) ≤ n/(n-2) - 1 = 2/(n-2)`
  have h1 : (n - 2) * log n - 2 ≤ (n - 2) * log (n - 2) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hn0 ha)
    rw [Real.log_div hn0.ne' ha.ne'] at h
    have h' : n / (n - 2) - 1 = 2 / (n - 2) := by field_simp; ring
    rw [h'] at h
    have h'' := mul_le_mul_of_nonneg_left h ha.le
    rw [mul_div_cancel₀ _ ha.ne'] at h''
    nlinarith
  -- `log n ≥ 3/2`, so `(n - 2) log n ≥ n`
  have hl : 3 / 2 ≤ log n :=
    (three_halves_lt_log_seven.trans_le (Real.log_le_log (by norm_num) hn)).le
  have h2 : n ≤ (n - 2) * log n := by nlinarith
  have key : (n - 2) * ((n - 2) * (2 * log n + (log n + 1) * n)) ≤
      (n - 2) * ((log (n - 2) + 1) * n ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg n)]
  have key' : (n - 2) * (2 * log n + (log n + 1) * n) ≤ (log (n - 2) + 1) * n ^ 2 :=
    le_of_mul_le_mul_left key ha
  have hq : (2 * log n + (log n + 1) * n) / n ^ 2 ≤ (log (n - 2) + 1) / (n - 2) := by
    rw [div_le_div_iff₀ (by positivity) ha]
    linarith
  have he : (2 * log n + (log n + 1) * n) / n ^ 2 = 2 * (log n / n ^ 2) + (log n + 1) / n := by
    field_simp
  linarith

/-- The odd tail: `∑_{k < K} (log (2k+7)) / (2k+7)² ≤ (log 5 + 1)/10`. -/
theorem sum_odd_tail_le (K : ℕ) :
    ∑ k ∈ range K, log ((2 * k + 7 : ℕ) : ℝ) / ((2 * k + 7 : ℕ) : ℝ) ^ 2 ≤
      (log 5 + 1) / 10 := by
  set G : ℕ → ℝ := fun k => (log ((2 * k + 5 : ℕ) : ℝ) + 1) / ((2 * k + 5 : ℕ) : ℝ) with hG
  have hstep : ∀ k, 2 * (log ((2 * k + 7 : ℕ) : ℝ) / ((2 * k + 7 : ℕ) : ℝ) ^ 2) ≤
      G k - G (k + 1) := by
    intro k
    have h7 : (7 : ℝ) ≤ ((2 * k + 7 : ℕ) : ℝ) := by push_cast; linarith [k.cast_nonneg (α := ℝ)]
    have h := two_mul_log_div_sq_le h7
    have e1 : ((2 * k + 7 : ℕ) : ℝ) - 2 = ((2 * k + 5 : ℕ) : ℝ) := by push_cast; ring
    have e2 : ((2 * (k + 1) + 5 : ℕ) : ℝ) = ((2 * k + 7 : ℕ) : ℝ) := by push_cast; ring
    rw [e1] at h
    simp only [hG, e2]
    exact h
  have htel := Finset.sum_range_sub' G K
  have hGK : 0 ≤ G K := by
    simp only [hG]
    have : (1 : ℝ) ≤ ((2 * K + 5 : ℕ) : ℝ) := by push_cast; linarith [K.cast_nonneg (α := ℝ)]
    exact div_nonneg (by linarith [Real.log_nonneg this]) (by linarith)
  have hG0 : G 0 = (log 5 + 1) / 5 := by norm_num [hG]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ range K) => hstep k
  rw [← Finset.mul_sum, htel, hG0] at hsum
  linarith

/-- `B < 2/3` in finite form: for every finite set `s` of primes,
`∑_{p ∈ s} (log p) / p² ≤ sumLogDivSqBound`. -/
theorem sum_log_div_sq_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, log (p : ℝ) / (p : ℝ) ^ 2 ≤ sumLogDivSqBound := by
  set f : ℕ → ℝ := fun p => log (p : ℝ) / (p : ℝ) ^ 2 with hf
  have hf0 : ∀ p, 0 ≤ f p := fun p => div_nonneg (log_natCast_nonneg p) (sq_nonneg _)
  set K := s.sup id + 1
  set img := (range K).image (fun k => 2 * k + 7)
  have hsub : s ⊆ {2, 3, 5} ∪ img := by
    intro p hp
    have hpp := hs p hp
    have hle : p ≤ s.sup id := Finset.le_sup (f := id) hp
    rcases hpp.eq_two_or_odd' with h2 | hodd
    · simp [h2]
    · by_cases h35 : p = 3 ∨ p = 5
      · rcases h35 with h | h <;> simp [h]
      · have h7 : 7 ≤ p := by
          have h2le := hpp.two_le
          obtain ⟨j, hj⟩ := hodd
          push Not at h35
          have h4 : p ≠ 4 := by omega
          have h6 : p ≠ 6 := by omega
          omega
        apply Finset.mem_union_right
        simp only [img, Finset.mem_image, Finset.mem_range]
        obtain ⟨j, hj⟩ := hodd
        refine ⟨(p - 7) / 2, by omega, by omega⟩
  have hdisj : Disjoint ({2, 3, 5} : Finset ℕ) img := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [img, Finset.mem_image] at hb
    obtain ⟨k, _, rfl⟩ := hb
    simp at ha
  have hinj : Set.InjOn (fun k => 2 * k + 7) (range K : Set ℕ) := by
    intro a _ b _ h
    simp only at h
    omega
  calc ∑ p ∈ s, f p ≤ ∑ p ∈ {2, 3, 5} ∪ img, f p :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hf0 p
    _ = ∑ p ∈ ({2, 3, 5} : Finset ℕ), f p + ∑ p ∈ img, f p := sum_union hdisj
    _ = (log 2 / 4 + log 3 / 9 + log 5 / 25) +
          ∑ k ∈ range K, log ((2 * k + 7 : ℕ) : ℝ) / ((2 * k + 7 : ℕ) : ℝ) ^ 2 := by
        rw [sum_image hinj]
        simp only [hf]
        norm_num
        ring
    _ ≤ (log 2 / 4 + log 3 / 9 + log 5 / 25) + (log 5 + 1) / 10 := by
        linarith [sum_odd_tail_le K]
    _ = sumLogDivSqBound := by unfold sumLogDivSqBound; ring

/-- `B < 2/3` for every finite set of primes. -/
theorem sum_log_div_sq_lt_two_thirds {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, log (p : ℝ) / (p : ℝ) ^ 2 < 2 / 3 :=
  (sum_log_div_sq_le hs).trans_lt sumLogDivSqBound_lt

/-- The series `B = ∑_p (log p) / p²` over all primes converges. -/
theorem summable_log_div_sq :
    Summable fun p : Nat.Primes => log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 := by
  refine summable_of_sum_le (c := sumLogDivSqBound)
    (fun p => div_nonneg (log_natCast_nonneg _) (sq_nonneg _)) fun u => ?_
  have h := sum_log_div_sq_le (s := u.map (Function.Embedding.subtype _))
    (by intro p hp; obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp; exact q.2)
  exact (Finset.sum_map u (Function.Embedding.subtype _)
    fun p : ℕ => log (p : ℝ) / (p : ℝ) ^ 2).symm.trans_le h

/-- The companion's `B < 2/3`, for the full series over the primes. -/
theorem tsum_log_div_sq_lt_two_thirds :
    ∑' p : Nat.Primes, log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 < 2 / 3 := by
  refine lt_of_le_of_lt ?_ sumLogDivSqBound_lt
  refine tsum_le_of_sum_le' ?_ fun u => ?_
  · unfold sumLogDivSqBound
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have h3 := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
    have h5 := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
    positivity
  · have h := sum_log_div_sq_le (s := u.map (Function.Embedding.subtype _))
      (by intro p hp; obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp; exact q.2)
    exact (Finset.sum_map u (Function.Embedding.subtype _)
    fun p : ℕ => log (p : ℝ) / (p : ℝ) ^ 2).symm.trans_le h

end ELEM.Primes
