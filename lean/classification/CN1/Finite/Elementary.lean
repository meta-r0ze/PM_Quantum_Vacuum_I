import Mathlib

/-!
# CN1.Finite.Elementary: the representation bound for the principal form

`Q(x, y) = x² + t·x·y + c·y²` with `d = 4c - t² > 0`. Then `4·Q(x, y) = (2x + t·y)² + d·y²`, so for
`y ≠ 0` we get `4·Q ≥ d`, with equality only when `2x + t·y = 0` and `y = ±1`. For `t = 1` that is
impossible by parity, so `4·Q ≥ d + 1` (the case `b = 1`). For `t = 0` equality means `x = 0`,
`y = ±1`, `Q = c = d/4` (`b = 0`, the ramified `p = d/4`).

Hence (step 6 of the argument): a prime `p` with `4p ≤ d`, `p ≠ c` is not represented by `Q`.
All pure integer arithmetic, no number field.
-/

namespace CN1.Finite

theorem four_mul_form (t c x y : ℤ) :
    4 * (x ^ 2 + t * x * y + c * y ^ 2) = (2 * x + t * y) ^ 2 + (4 * c - t ^ 2) * y ^ 2 := by
  ring

theorem form_nonneg {t c : ℤ} (hd : 0 ≤ 4 * c - t ^ 2) (x y : ℤ) :
    0 ≤ x ^ 2 + t * x * y + c * y ^ 2 := by
  have h := four_mul_form t c x y
  nlinarith [sq_nonneg (2 * x + t * y), mul_nonneg hd (sq_nonneg y)]

/-- A prime is not a perfect square. -/
theorem not_prime_eq_sq {p : ℕ} (hp : p.Prime) (x : ℤ) : (p : ℤ) ≠ x ^ 2 := by
  intro h
  have h' : p = x.natAbs ^ 2 := by
    have : (p : ℤ) = (x.natAbs : ℤ) ^ 2 := by rw [Int.natAbs_sq]; exact h
    exact_mod_cast this
  have hdvd : x.natAbs ∣ p := ⟨x.natAbs, by rw [h']; ring⟩
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · rw [h1] at h'; exact hp.one_lt.ne' (by simpa using h')
  · rw [h1] at h'
    have := hp.two_le
    nlinarith

/-- **The representation bound.** If `t ∈ {0, 1}`, `p` is prime, `4p ≤ d = 4c - t²` and `p ≠ c`,
then `Q(x, y) = x² + t·x·y + c·y² ≠ p` for all integers `x, y`. -/
theorem not_form_eq_prime {t c : ℤ} (ht : t = 0 ∨ t = 1) {p : ℕ} (hp : p.Prime)
    (hb : 4 * (p : ℤ) ≤ 4 * c - t ^ 2) (hpc : (p : ℤ) ≠ c) (x y : ℤ)
    (h : x ^ 2 + t * x * y + c * y ^ 2 = p) : False := by
  have h4 := four_mul_form t c x y
  rw [h] at h4
  have hp0 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    exact not_prime_eq_sq hp x (by linarith)
  · have hy1 : 1 ≤ y ^ 2 := by
      have := Int.one_le_abs hy
      nlinarith [sq_abs y]
    have hd0 : 0 ≤ 4 * c - t ^ 2 := by linarith
    -- 4p = (2x + ty)² + d·y² ≥ d ≥ 4p forces (2x + ty)² = 0 and d·(y² - 1) = 0
    have hsq : (2 * x + t * y) ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * x + t * y), mul_nonneg hd0 (sub_nonneg.mpr hy1)]
    have hy2 : y ^ 2 = 1 := by
      have hdpos : 0 < 4 * c - t ^ 2 := by linarith
      have : (4 * c - t ^ 2) * (y ^ 2 - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hdpos.ne'
      · linarith
    have hlin : 2 * x + t * y = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq
    have hy' : y = 1 ∨ y = -1 :=
      Int.eq_one_or_neg_one_of_mul_eq_one (by rw [← sq]; exact hy2)
    rcases ht with rfl | rfl
    · -- t = 0: x = 0 and p = c·y² = c
      have hx : x = 0 := by linarith
      subst hx
      rw [hy2] at h
      apply hpc
      linarith
    · -- t = 1: 2x + y = 0 with y = ±1 is a parity contradiction
      rcases hy' with rfl | rfl <;> omega

end CN1.Finite
