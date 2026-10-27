import ELEM.Hypotheses
import ELEM.Divisibility.Count
import ELEM.Primes.Theta
import ELEM.Primes.SumLogDivSq

/-!
# ELEM.Divisibility.Main: `ELEM.DivisibilityBound`, the companion's (14)

The elementary companion (twinheterodox/tenth-discriminant, companions/elementary,
commit 64694aae), section 4.3, eq. (14), after Green (hexagon 2610.00311v2, Lemma 5.1).

For a nonzero maximal minor `D₀` of `M q R`, `Δ = N(D₀)` is a positive integer
(`norm_pos_of_ne_zero`), and for every inert prime `p ≤ R` it is divisible by `p^{2 ∑ h_{r,s}}`
(`ELEM.Divisibility.pow_two_mul_dvd_norm_minor`, the companion's (12)). These prime powers are
pairwise coprime, so their product divides `Δ`, and

  `log Δ ≥ ∑_{p ≤ R inert} 2 (∑_{r,s} h_{r,s}) log p`.

By (13) (`ELEM.Divisibility.two_mul_sum_hgt_ge`) the right side is at least
`S R² I - S R θ_I - (R³/3) B_I - (R²/2) I`, with `I = ∑ log p / p`, `θ_I = ∑ log p` and
`B_I = ∑ log p / p²` over the inert `p ≤ R`. Lemma 2 (`θ_I < (3/2) R`, `B_I < 2/3`) and
`R ≤ 13 S` (as `R ≥ 144`) give `S R θ_I ≤ (3/2) R² S` and `(R³/3) B_I ≤ (2/9) R³ ≤ (26/9) R² S`,
so `log Δ ≥ R² S (I - I/(2S) - 79/18)`, with the companion's constant `79/18 = 3/2 + 26/9`.
-/

set_option autoImplicit false

open Finset Real

namespace ELEM.Divisibility

/-- The norm `x² + x y + c y²` of a nonzero element of `ℤ[ω]` is positive (`c ≥ 1`). -/
theorem norm_pos_of_ne_zero {c : ℕ} (hc : 1 ≤ c) {z : OK c} (hz : z ≠ 0) :
    0 < QuadraticAlgebra.norm z := by
  rw [QuadraticAlgebra.norm_def]
  have hc' : (1 : ℤ) ≤ c := by exact_mod_cast hc
  rcases eq_or_ne z.im 0 with him | him
  · have hre : z.re ≠ 0 := by
      intro hre
      exact hz (QuadraticAlgebra.ext hre him)
    rw [him]
    simp only [mul_zero, sub_zero, add_zero]
    exact mul_self_pos.mpr hre
  · have h1 : 0 < z.im * z.im := mul_self_pos.mpr him
    nlinarith [sq_nonneg (2 * z.re + z.im)]

variable (q R : ℕ)

/-- **(14) for any set `P` of inert primes `p ≤ R`.** -/
theorem divisibility_of_subset (hq : AnalyticSetting q) (hq4 : q ^ 4 < R)
    (f : Row R → Col q R) (hf : minor q R f ≠ 0) (P : Finset ℕ) (hPR : P ⊆ Nat.primesLE R)
    (hPi : ∀ p ∈ P, IsInert (cq q) p) :
    (∑ p ∈ P, Real.log p / p) - (∑ p ∈ P, Real.log p / p) / (2 * Sof R) - 79 / 18 ≤
      Real.log (Delta q R f) / ((R : ℝ) ^ 2 * Sof R) := by
  classical
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesLE (hPR hp)
  -- the sizes: `R ≥ 144`, so `0 < S` and `R ≤ 13 S`
  have hR : 144 ≤ R := by
    have h1 : 32768 ≤ q := hq.large
    have : 144 ≤ q ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left h1 4)
    omega
  have hS0 : 0 < Sof R := by unfold Sof; omega
  have hS13 : R ≤ 13 * Sof R := by unfold Sof; omega
  set S := Sof R with hSdef
  set H : ℕ → ℕ := fun p => ∑ i : Row R, hgt p (Sof R) i.1 i.2 with hH
  -- `Δ` is a positive integer divisible by `∏_{p ∈ P} p^{2 H_p}`
  set N := QuadraticAlgebra.norm (minor q R f) with hN
  have hc : 1 ≤ cq q := by unfold cq; have := hq.large; omega
  have hNpos : 0 < N := norm_pos_of_ne_zero hc hf
  have hdvd : ∏ p ∈ P, (p : ℤ) ^ (2 * H p) ∣ N := by
    refine Finset.prod_dvd_of_coprime ?_ fun p hp => pow_two_mul_dvd_norm_minor q R (hPp p hp)
      (hPi p hp) f
    intro p hp p' hp' hne
    exact (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hPp p hp) (hPp p' hp')).mpr hne)).pow
  have hle : ∏ p ∈ P, (p : ℤ) ^ (2 * H p) ≤ N := Int.le_of_dvd hNpos hdvd
  have hpow : ∀ p ∈ P, (0 : ℝ) < (p : ℝ) ^ (2 * H p) := fun p hp =>
    pow_pos (by exact_mod_cast (hPp p hp).pos) _
  have hlog : ∑ p ∈ P, 2 * (H p : ℝ) * Real.log p ≤ Real.log (Delta q R f) := by
    have e : ∑ p ∈ P, 2 * (H p : ℝ) * Real.log p = Real.log (∏ p ∈ P, (p : ℝ) ^ (2 * H p)) := by
      rw [Real.log_prod (fun p hp => (hpow p hp).ne')]
      refine sum_congr rfl fun p _ => ?_
      rw [Real.log_pow]
      push_cast
      ring
    rw [e, Delta]
    refine Real.log_le_log (prod_pos hpow) ?_
    rw [← hN]
    exact_mod_cast hle
  -- (13) for each `p ∈ P`, weighted by `log p`
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS0
  have hterm : ∀ p ∈ P,
      (S : ℝ) * R ^ 2 * (Real.log p / p) - S * R * Real.log p - (R : ℝ) ^ 3 / 3 * (Real.log p / p ^ 2)
        - (R : ℝ) ^ 2 / 2 * (Real.log p / p) ≤ 2 * (H p : ℝ) * Real.log p := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPp p hp).pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (hPp p hp).one_lt.le)
    have h13 := two_mul_sum_hgt_ge p R S (hPp p hp).pos
    have hHc : (H p : ℝ) = ∑ i : Fin R × Fin S, (hgt p S i.1 i.2 : ℝ) := by
      rw [hH]
      push_cast
      rfl
    rw [← hHc] at h13
    have e : (S : ℝ) * R ^ 2 * (Real.log p / p) - S * R * Real.log p -
        (R : ℝ) ^ 3 / 3 * (Real.log p / p ^ 2) - (R : ℝ) ^ 2 / 2 * (Real.log p / p) =
        ((S : ℝ) * R * (R - p) / p - (R : ℝ) ^ 3 / (3 * p ^ 2) - (R : ℝ) ^ 2 / (2 * p)) *
          Real.log p := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h13 hlogp
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    ← mul_sum] at hsum
  -- Lemma 2
  have hθ : ∑ p ∈ P, Real.log p < 3 / 2 * R :=
    ELEM.Primes.sum_log_lt_three_halves_mul hPR (by omega)
  have hB : ∑ p ∈ P, Real.log p / (p : ℝ) ^ 2 < 2 / 3 :=
    ELEM.Primes.sum_log_div_sq_lt_two_thirds hPp
  have hI : 0 ≤ ∑ p ∈ P, Real.log p / p := sum_nonneg fun p hp =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hPp p hp).one_lt.le)) (Nat.cast_nonneg _)
  set I := ∑ p ∈ P, Real.log p / p
  set θ := ∑ p ∈ P, Real.log p
  set B := ∑ p ∈ P, Real.log p / (p : ℝ) ^ 2
  have t1 : (S : ℝ) * R * θ ≤ S * R * (3 / 2 * R) :=
    mul_le_mul_of_nonneg_left hθ.le (by positivity)
  have t2 : (R : ℝ) ^ 3 / 3 * B ≤ (R : ℝ) ^ 3 / 3 * (2 / 3) :=
    mul_le_mul_of_nonneg_left hB.le (by positivity)
  have t3 : (R : ℝ) ^ 3 ≤ (R : ℝ) ^ 2 * (13 * S) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hS13) (by positivity)
  rw [le_div_iff₀ (by positivity)]
  have e : (I - I / (2 * S) - 79 / 18) * ((R : ℝ) ^ 2 * S) =
      S * R ^ 2 * I - (R : ℝ) ^ 2 / 2 * I - 79 / 18 * R ^ 2 * S := by
    field_simp
  rw [e]
  nlinarith

end ELEM.Divisibility

namespace ELEM

/-- **`ELEM.DivisibilityBound`** (companion (14)). For every nonzero `N × N`
minor of `M q R`, `log Δ / (R² S) ≥ I - I/(2S) - 79/18`, `I = Iinert q R`. -/
theorem divisibilityBound : DivisibilityBound := by
  classical
  intro q R hq _ _ hq4 _ f hf
  unfold Iinert
  exact Divisibility.divisibility_of_subset q R hq hq4 f hf _ (filter_subset _ _)
    fun p hp => (mem_filter.mp hp).2

end ELEM
