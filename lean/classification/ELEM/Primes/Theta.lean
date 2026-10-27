import Mathlib.NumberTheory.Chebyshev
import ELEM.Primes.Numerics

/-!
# Chebyshev's bound in the form `θ(x) < (3/2) x`

Mathlib proves `θ x ≤ log 4 * x` (`Chebyshev.theta_le_log4_mul_x`, from the primorial bound
`primorial_le_four_pow`). With `log 4 < 3/2` this gives the strict bound used by the
elementary companion (twinheterodox/tenth-discriminant, companions/elementary, commit
64694aae), Lemma 2.
-/

namespace ELEM.Primes

open Real Finset

/-- Chebyshev's bound with the companion's constant: `θ(x) < (3/2) x` for `x > 0`. -/
theorem theta_lt_three_halves_mul {x : ℝ} (hx : 0 < x) : Chebyshev.theta x < 3 / 2 * x :=
  (Chebyshev.theta_le_log4_mul_x hx.le).trans_lt
    (mul_lt_mul_of_pos_right log_four_lt_three_halves hx)

/-- A sum of `log p` over a set of primes at most `n` is at most `θ(n)`. -/
theorem sum_log_le_theta {s : Finset ℕ} {n : ℕ} (hs : s ⊆ Nat.primesLE n) :
    ∑ p ∈ s, log (p : ℝ) ≤ Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  exact sum_le_sum_of_subset_of_nonneg hs fun p _ _ => log_natCast_nonneg p

/-- A sum of `log p` over a set of primes at most `n`, `n ≥ 1`, is below `(3/2) n`. -/
theorem sum_log_lt_three_halves_mul {s : Finset ℕ} {n : ℕ} (hs : s ⊆ Nat.primesLE n)
    (hn : 0 < n) : ∑ p ∈ s, log (p : ℝ) < 3 / 2 * n :=
  (sum_log_le_theta hs).trans_lt (theta_lt_three_halves_mul (by exact_mod_cast hn))

end ELEM.Primes
