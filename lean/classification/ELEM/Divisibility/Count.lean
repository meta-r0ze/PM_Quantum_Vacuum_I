import ELEM.Divisibility.Rows
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field

/-!
# ELEM.Divisibility.Count: the lower bound for `∑_{r,s} h_{r,s}` (companion (13))

The elementary companion (twinheterodox/tenth-discriminant,
companions/elementary, commit 64694aae), section 4.3, p. 5. With `h_{r,s} = min(⌊r/p⌋, S-1-s)`:

* `∑_{s<S} min(k, S-1-s) = ∑_{j<S} min(k, j) ≥ S k - k(k+1)/2` (also when `k ≥ S`);
* `∑_{r<R} ⌊r/p⌋ ≥ R(R-p)/(2p)`;
* `⌊r/p⌋ (⌊r/p⌋ + 1) ≤ (r/p)² + r/p`, `∑_{r<R} r² ≤ R³/3`, `∑_{r<R} r ≤ R²/2`.

Together (`two_mul_sum_hgt_ge`):
`2 ∑_{r,s} h_{r,s} ≥ S R (R - p)/p - R³/(3p²) - R²/(2p)`.
Divided by `R² S` this is the companion's (13) after its own last step `(R-1)(2R-1)/6 ≤ R³/3`
and `R(R-1)/2 ≤ R²/2`, which we take at once.
-/

set_option autoImplicit false

open Finset

namespace ELEM.Divisibility

theorem two_mul_sum_range_id_real (n : ℕ) : 2 * ∑ j ∈ range n, (j : ℝ) = n * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- `2 ∑_{j<S} min(k, j) ≥ 2 S k - k² - k`. -/
theorem two_mul_sum_min_ge (k S : ℕ) :
    2 * (S : ℝ) * k - (k : ℝ) ^ 2 - k ≤ 2 * ∑ j ∈ range S, ((min k j : ℕ) : ℝ) := by
  rcases le_total S k with hSk | hkS
  · have : ∑ j ∈ range S, ((min k j : ℕ) : ℝ) = ∑ j ∈ range S, (j : ℝ) :=
      sum_congr rfl fun j hj => by
        rw [min_eq_right (by have := mem_range.mp hj; omega)]
    rw [this, two_mul_sum_range_id_real]
    have : (S : ℝ) ≤ k := by exact_mod_cast hSk
    nlinarith
  · rw [← sum_range_add_sum_Ico _ hkS]
    have h1 : ∑ j ∈ range k, ((min k j : ℕ) : ℝ) = ∑ j ∈ range k, (j : ℝ) :=
      sum_congr rfl fun j hj => by
        rw [min_eq_right (by have := mem_range.mp hj; omega)]
    have h2 : ∑ j ∈ Ico k S, ((min k j : ℕ) : ℝ) = ∑ j ∈ Ico k S, (k : ℝ) :=
      sum_congr rfl fun j hj => by
        rw [min_eq_left (mem_Ico.mp hj).1]
    rw [h1, h2, mul_add, two_mul_sum_range_id_real, sum_const, Nat.card_Ico, nsmul_eq_mul,
      Nat.cast_sub hkS]
    ring_nf
    exact le_refl _

/-- `2 p ∑_{r<R} ⌊r/p⌋ ≥ R (R - p)` (strong induction, in steps of `p`). -/
theorem floor_sum_ge (p : ℕ) (hp : 0 < p) (R : ℕ) :
    (R : ℝ) * ((R : ℝ) - p) ≤ 2 * p * ∑ r ∈ range R, ((r / p : ℕ) : ℝ) := by
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    rcases lt_or_ge R p with hRp | hRp
    · have h0 : 0 ≤ ∑ r ∈ range R, ((r / p : ℕ) : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
      have : ((R : ℝ) - p) < 0 := by
        have : (R : ℝ) < p := by exact_mod_cast hRp
        linarith
      have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      nlinarith
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hRp
      have hm : m < p + m := by omega
      have ihm := ih m hm
      rw [sum_range_add]
      have hzero : ∑ x ∈ range p, ((x / p : ℕ) : ℝ) = 0 :=
        sum_eq_zero fun x hx => by rw [Nat.div_eq_of_lt (mem_range.mp hx), Nat.cast_zero]
      have hstep : ∀ x : ℕ, (((p + x) / p : ℕ) : ℝ) = ((x / p : ℕ) : ℝ) + 1 := fun x => by
        rw [add_comm p x, Nat.add_div_right x hp, Nat.cast_add, Nat.cast_one]
      rw [hzero, sum_congr rfl fun x _ => hstep x, sum_add_distrib, sum_const, card_range,
        nsmul_eq_mul, mul_one, Nat.cast_add]
      nlinarith

theorem sum_range_sq_le (R : ℕ) : ∑ r ∈ range R, ((r : ℝ)) ^ 2 ≤ (R : ℝ) ^ 3 / 3 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ]
    push_cast
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    nlinarith

theorem sum_range_le (R : ℕ) : ∑ r ∈ range R, (r : ℝ) ≤ (R : ℝ) ^ 2 / 2 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ]
    push_cast
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    nlinarith

/-- **(13), before dividing by `R² S`.**
`2 ∑_{r<R, s<S} h_{r,s} ≥ S R (R - p)/p - R³/(3p²) - R²/(2p)`. -/
theorem two_mul_sum_hgt_ge (p R S : ℕ) (hp : 0 < p) :
    (S : ℝ) * R * (R - p) / p - (R : ℝ) ^ 3 / (3 * p ^ 2) - (R : ℝ) ^ 2 / (2 * p) ≤
      2 * ∑ i : Fin R × Fin S, (hgt p S i.1 i.2 : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hrow : ∀ r : Fin R, ∑ s : Fin S, (hgt p S r s : ℝ) =
      ((∑ j ∈ range S, min ((r : ℕ) / p) j : ℕ) : ℝ) := by
    intro r
    rw [← Nat.cast_sum]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun s => hgt p S r s) S]
    exact sum_range_reflect (fun j => min ((r : ℕ) / p) j) S
  have hper : ∀ r : ℕ, 2 * (S : ℝ) * ((r / p : ℕ) : ℝ) - ((r : ℝ) / p) ^ 2 - (r : ℝ) / p ≤
      2 * ((∑ j ∈ range S, min (r / p) j : ℕ) : ℝ) := by
    intro r
    have hk0 : (0 : ℝ) ≤ ((r / p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hk : ((r / p : ℕ) : ℝ) ≤ (r : ℝ) / p := Nat.cast_div_le
    generalize r / p = k at hk hk0 ⊢
    have h1 := two_mul_sum_min_ge k S
    rw [Nat.cast_sum]
    nlinarith
  rw [Fintype.sum_prod_type]
  simp_rw [hrow]
  rw [Fin.sum_univ_eq_sum_range (fun r => ((∑ j ∈ range S, min (r / p) j : ℕ) : ℝ)) R]
  have hfl : (R : ℝ) * (R - p) ≤ 2 * p * ∑ r ∈ range R, ((r / p : ℕ) : ℝ) :=
    floor_sum_ge p hp R
  have hsum := sum_le_sum fun r (_ : r ∈ range R) => hper r
  rw [← mul_sum] at hsum
  have e1 : ∑ r ∈ range R, (2 * (S : ℝ) * ((r / p : ℕ) : ℝ) - ((r : ℝ) / p) ^ 2 - (r : ℝ) / p) =
      2 * S * ∑ r ∈ range R, ((r / p : ℕ) : ℝ) - (∑ r ∈ range R, (r : ℝ) ^ 2) / p ^ 2 -
        (∑ r ∈ range R, (r : ℝ)) / p := by
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_div, sum_div]
    simp only [div_pow]
  rw [e1] at hsum
  have a1 : (S : ℝ) * R * (R - p) / p ≤ 2 * S * ∑ r ∈ range R, ((r / p : ℕ) : ℝ) := by
    rw [div_le_iff₀ hp']
    have : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    nlinarith
  have a2 : (∑ r ∈ range R, (r : ℝ) ^ 2) / p ^ 2 ≤ (R : ℝ) ^ 3 / (3 * p ^ 2) := by
    rw [show (R : ℝ) ^ 3 / (3 * p ^ 2) = (R : ℝ) ^ 3 / 3 / p ^ 2 by ring]
    exact div_le_div_of_nonneg_right (sum_range_sq_le R) (by positivity)
  have a3 : (∑ r ∈ range R, (r : ℝ)) / p ≤ (R : ℝ) ^ 2 / (2 * p) := by
    rw [show (R : ℝ) ^ 2 / (2 * p) = (R : ℝ) ^ 2 / 2 / p by ring]
    exact div_le_div_of_nonneg_right (sum_range_le R) hp'.le
  linarith

end ELEM.Divisibility
