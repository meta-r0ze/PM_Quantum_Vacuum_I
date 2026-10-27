import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import ELEM.Primes.Theta
import ELEM.Primes.SumLogDivSq

/-!
# Two-sided bounds for `A(m) = ∑_{p ≤ m} (log p) / p`

The elementary companion (twinheterodox/tenth-discriminant, companions/elementary, commit
64694aae), Lemma 2, states `log m - 7/3 < A(m) < log m + 3/2` for integers `m ≥ 2`.
The argument is Legendre's formula for `v_p(m!)` on both sides:

* `log (m!) = ∑_{p ≤ m} v_p(m!) log p`;
* `v_p(m!) ≤ m / (p - 1)`, from `(p - 1) v_p(m!) = m - s_p(m)` (Mathlib's
  `sub_one_mul_padicValNat_factorial`), and `m/(p-1) = m/p + m/(p(p-1)) ≤ m/p + 2m/p²`;
* `v_p(m!) ≥ ⌊m/p⌋ > m/p - 1`, from `Nat.factorization_factorial`;
* `m log m - m ≤ log (m!) ≤ m log m`, from `m^m / m! ≤ e^m` (`Real.pow_div_factorial_le_exp`)
  and `m! ≤ m^m`;
* `θ(m) < (3/2) m` and `∑_p (log p)/p² < 2/3` (the other two estimates of Lemma 2).

The companion's lower bound on `log (m!)` is the Stirling-type `m log m - m < log (m!)`; we use
the non-strict form from the exponential series and get the strict inequality from the strict
bound on `B`. The statements hold for all `m ≥ 1`.
-/

namespace ELEM.Primes

open Nat hiding log
open Real Finset

/-- `log (m!) = ∑_{p ≤ m} v_p(m!) log p`. -/
theorem log_factorial_eq_sum (m : ℕ) :
    log ((m ! : ℕ) : ℝ) = ∑ p ∈ primesLE m, ((m !).factorization p : ℝ) * log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  refine Finsupp.sum_of_support_subset _ ?_ _ (fun p _ => by simp)
  intro p hp
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
  exact mem_primesLE.mpr ⟨(Nat.Prime.dvd_factorial hp.1).mp hp.2.1, hp.1⟩

/-- Legendre, upper side: `(p - 1) v_p(m!) ≤ m`. -/
theorem factorization_factorial_mul_le {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (p - 1) * (m !).factorization p ≤ m := by
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, sub_one_mul_padicValNat_factorial]
  exact Nat.sub_le _ _

/-- Legendre, lower side: `⌊m / p⌋ ≤ v_p(m!)`. -/
theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (m : ℕ) :
    m / p ≤ (m !).factorization p := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hb : Nat.log p m < m + 1 := Nat.lt_succ_of_lt (Nat.log_lt_self p hm.ne')
  rw [Nat.factorization_factorial hp hb]
  have h1 : 1 ∈ Ico 1 (m + 1) := by simp; omega
  have := Finset.single_le_sum (f := fun i => m / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simpa using this

/-- The real form of the upper side: `v_p(m!) log p ≤ m (log p / p) + 2 m (log p / p²)`. -/
theorem factorization_factorial_mul_log_le {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ((m !).factorization p : ℝ) * log (p : ℝ) ≤
      m * (log (p : ℝ) / p) + 2 * m * (log (p : ℝ) / (p : ℝ) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hl : 0 ≤ log (p : ℝ) := log_natCast_nonneg p
  have hv : ((p : ℝ) - 1) * ((m !).factorization p : ℝ) ≤ m := by
    have := (Nat.cast_le (α := ℝ)).mpr (factorization_factorial_mul_le hp m)
    rwa [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] at this
  -- `v ≤ m/(p-1) ≤ m/p + 2m/p²`
  have hdiv : ((m !).factorization p : ℝ) ≤ m / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ hp1]; linarith
  have hfrac : (m : ℝ) / ((p : ℝ) - 1) ≤ m / p + 2 * m / (p : ℝ) ^ 2 := by
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    have hp0 : (0 : ℝ) < p := by linarith
    rw [div_add_div _ _ hp0.ne' (by positivity), div_le_div_iff₀ hp1 (by positivity)]
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hp2), mul_nonneg (mul_nonneg hm hp0.le)
      (sub_nonneg.mpr hp2)]
  calc ((m !).factorization p : ℝ) * log (p : ℝ) ≤ (m / p + 2 * m / (p : ℝ) ^ 2) * log p :=
        mul_le_mul_of_nonneg_right (hdiv.trans hfrac) hl
    _ = m * (log (p : ℝ) / p) + 2 * m * (log (p : ℝ) / (p : ℝ) ^ 2) := by ring

/-- The real form of the lower side: `m (log p / p) - log p ≤ v_p(m!) log p`. -/
theorem mul_log_div_sub_le {p : ℕ} (hp : p.Prime) (m : ℕ) :
    m * (log (p : ℝ) / p) - log (p : ℝ) ≤ ((m !).factorization p : ℝ) * log (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl : 0 ≤ log (p : ℝ) := log_natCast_nonneg p
  have hfl : (m : ℝ) / p - 1 ≤ ((m / p : ℕ) : ℝ) := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    exact (Nat.sub_one_lt_floor _).le
  have hv : (m : ℝ) / p - 1 ≤ ((m !).factorization p : ℝ) :=
    hfl.trans (by exact_mod_cast div_le_factorization_factorial hp m)
  calc m * (log (p : ℝ) / p) - log (p : ℝ) = ((m : ℝ) / p - 1) * log p := by ring
    _ ≤ ((m !).factorization p : ℝ) * log (p : ℝ) := mul_le_mul_of_nonneg_right hv hl

/-- `m log m - m ≤ log (m!)`, from the exponential series. -/
theorem mul_log_sub_le_log_factorial (m : ℕ) :
    (m : ℝ) * log m - m ≤ log ((m ! : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hf0 : (0 : ℝ) < (m ! : ℕ) := by exact_mod_cast m.factorial_pos
  have h := Real.pow_div_factorial_le_exp (m : ℝ) hm0.le m
  have h' := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div (by positivity) hf0.ne', Real.log_pow] at h'
  linarith

/-- `log (m!) ≤ m log m`, from `m! ≤ m^m`. -/
theorem log_factorial_le_mul_log (m : ℕ) : log ((m ! : ℕ) : ℝ) ≤ m * log m := by
  have hf0 : (0 : ℝ) < (m ! : ℕ) := by exact_mod_cast m.factorial_pos
  have h : ((m ! : ℕ) : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have := Real.log_le_log hf0 h
  rwa [Real.log_pow] at this

/-- Lower bound of Lemma 2: `log m - 7/3 < A(m)` for `m ≥ 1`. -/
theorem log_sub_lt_sum_log_div {m : ℕ} (hm : 1 ≤ m) :
    log (m : ℝ) - 7 / 3 < ∑ p ∈ primesLE m, log (p : ℝ) / p := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hB := sum_log_div_sq_lt_two_thirds (s := primesLE m) fun p hp => prime_of_mem_primesLE hp
  have hsum : log ((m ! : ℕ) : ℝ) ≤
      m * ∑ p ∈ primesLE m, log (p : ℝ) / p +
        2 * m * ∑ p ∈ primesLE m, log (p : ℝ) / (p : ℝ) ^ 2 := by
    rw [log_factorial_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p hp =>
      factorization_factorial_mul_log_le (prime_of_mem_primesLE hp) m
  have hlow := mul_log_sub_le_log_factorial m
  -- divide `m log m - m < m A + (4/3) m` by `m`
  have : (m : ℝ) * (log m - 7 / 3) < m * ∑ p ∈ primesLE m, log (p : ℝ) / p := by
    nlinarith
  exact lt_of_mul_lt_mul_left this hm0.le

/-- Upper bound of Lemma 2: `A(m) < log m + 3/2` for `m ≥ 1`. -/
theorem sum_log_div_lt_log_add {m : ℕ} (hm : 1 ≤ m) :
    ∑ p ∈ primesLE m, log (p : ℝ) / p < log (m : ℝ) + 3 / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hθ := sum_log_lt_three_halves_mul (s := primesLE m) (n := m) (subset_refl _) hm
  have hsum : m * ∑ p ∈ primesLE m, log (p : ℝ) / p - ∑ p ∈ primesLE m, log (p : ℝ) ≤
      log ((m ! : ℕ) : ℝ) := by
    rw [log_factorial_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun p hp => mul_log_div_sub_le (prime_of_mem_primesLE hp) m
  have hup := log_factorial_le_mul_log m
  have : (m : ℝ) * ∑ p ∈ primesLE m, log (p : ℝ) / p < m * (log m + 3 / 2) := by
    nlinarith
  exact lt_of_mul_lt_mul_left this hm0.le

/-- Primes in `(m, n]`: `∑_{m < p ≤ n} (log p)/p = A(n) - A(m)`. -/
theorem sum_Ioc_eq_sub {m n : ℕ} (hmn : m ≤ n) :
    ∑ p ∈ (Ioc m n).filter Nat.Prime, log (p : ℝ) / p =
      ∑ p ∈ primesLE n, log (p : ℝ) / p - ∑ p ∈ primesLE m, log (p : ℝ) / p := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_filter_add_sum_filter_not (primesLE n) (fun p => m < p)]
  congr 2
  · ext p
    by_cases hp : p.Prime <;> simp only [mem_filter, mem_Ioc, mem_primesLE, hp, and_true,
      and_false, false_and]
    omega
  · ext p
    by_cases hp : p.Prime <;> simp only [mem_filter, mem_primesLE, not_lt, hp, and_true,
      and_false, false_and]
    omega

/-- The weight of the primes in `(m, n]`: `∑_{m < p ≤ n} (log p)/p > log n - log m - 23/6`,
for `1 ≤ m ≤ n`. This is the form Lemma 3 of the companion uses with `m = q⁴`, `n = q⁵`. -/
theorem log_sub_log_sub_lt_sum_Ioc {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    log (n : ℝ) - log (m : ℝ) - 23 / 6 < ∑ p ∈ (Ioc m n).filter Nat.Prime, log (p : ℝ) / p := by
  rw [sum_Ioc_eq_sub hmn]
  linarith [log_sub_lt_sum_log_div (hm.trans hmn), sum_log_div_lt_log_add hm]

/-- A sub-sum of `A(n)` over a set of primes at most `n` (for instance the inert primes) is
below `log n + 3/2`, for `n ≥ 1`. -/
theorem sum_log_div_lt_log_add_of_subset {s : Finset ℕ} {n : ℕ} (hs : s ⊆ primesLE n)
    (hn : 1 ≤ n) : ∑ p ∈ s, log (p : ℝ) / p < log (n : ℝ) + 3 / 2 :=
  (sum_le_sum_of_subset_of_nonneg hs fun p _ _ =>
    div_nonneg (log_natCast_nonneg p) p.cast_nonneg).trans_lt (sum_log_div_lt_log_add hn)

end ELEM.Primes
