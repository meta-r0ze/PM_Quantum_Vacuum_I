import ELEM.Frobenius
import ELEM.Divisibility.Det
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Sum

/-!
# ELEM.Divisibility.Rows: Green's row replacement and the `p`-power dividing a minor

Companion section 4.3 (twinheterodox/tenth-discriminant, companions/elementary,
commit 64694aae), after Green (hexagon 2610.00311v2, Lemma 5.1; stated there for odd `p` in
`ℤ[√d]` with a Gram determinant; the `ℤ[ω]` setting, the single maximal minor and `p = 2` are the
companion's extensions).

Fix a prime `p`. Row `(r, s)` of `M q R` is the derivative data at the nodes of `z^r w^s`; put
`h = h_{r,s} = min(⌊r/p⌋, S - 1 - s)` and replace it by the row of
`z^{r - p h} (z^p - w)^h w^s = ∑_{i ≤ h} (-1)^i C(h,i) z^{r - p i} w^{s + i}`.
The rows `(r - p i, s + i)`, `1 ≤ i ≤ h`, exist (`r - p i ≥ 0`, `s + i < S`) and have strictly
smaller `r`, so the replacement is `U * M` with `U` unitriangular in `r` (`Umat`), and every maximal
minor is unchanged (`ELEM.Divisibility.det_submatrix_mul_of_fst_unitriangular`).

If `p` is inert, Frobenius gives `p ∣ z^p - z̄` at every node (`ELEM.frobenius_dvd`, `p = 2`
included). The `z`-derivative of `z^p - w` is `p z^{p-1}`, so every `z`-derivative of
`G · (z^p - w)^h`, evaluated at `(z, z̄)`, is divisible by `p^h`
(`pow_dvd_eval_iterate_derivative`). Hence row `(r, s)` of `U * M` is divisible by `p^{h_{r,s}}`,
every maximal minor `D₀` by `p^{∑ h}`, and `N(D₀)` by `p^{2 ∑ h}` (`pow_two_mul_dvd_norm_minor`),
which is the companion's (12).

Here the second variable `w` is the constant `t = z̄` of the polynomial ring in `z`; `M q R` is
`(∂_z^k (z^r · t^s))(z)` with `t = z̄`, which is the entry of `ELEM.M`.
-/

set_option autoImplicit false

open Polynomial QuadraticAlgebra Finset

namespace ELEM.Divisibility

/-! ## Polynomial facts in one variable over a commutative ring -/

section poly

variable {K : Type*} [CommRing K]

theorem iterate_derivative_add' (k : ℕ) (a b : K[X]) :
    derivative^[k] (a + b) = derivative^[k] a + derivative^[k] b := by
  simp_rw [← Module.End.pow_apply, map_add]

/-- **The `p^h` divisibility.** If `p ∣ z^p - t`, then for every `G` and `k`,
`p^h ∣ (∂^k (G · (X^p - t)^h))(z)`: each derivative either lowers the power of `X^p - t` by one
at the cost of a factor `p` (from `∂(X^p - t) = p X^{p-1}`), or falls on the cofactor. -/
theorem pow_dvd_eval_iterate_derivative (p : ℕ) {z t : K} (hz : (p : K) ∣ z ^ p - t) :
    ∀ (h k : ℕ) (G : K[X]), (p : K) ^ h ∣ (derivative^[k] (G * (X ^ p - C t) ^ h)).eval z := by
  intro h
  induction h with
  | zero => intro k G; simp
  | succ h ih =>
    intro k
    induction k with
    | zero =>
      intro G
      simp only [Function.iterate_zero, id_eq, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hz _) _
    | succ k ihk =>
      intro G
      have hd : derivative (G * (X ^ p - C t) ^ (h + 1)) =
          derivative G * (X ^ p - C t) ^ (h + 1) +
            C (p : K) * ((G * C ((h + 1 : ℕ) : K) * X ^ (p - 1)) * (X ^ p - C t) ^ h) := by
        rw [derivative_mul, derivative_pow, derivative_sub, derivative_X_pow, derivative_C,
          Nat.add_one_sub_one]
        ring
      rw [Function.iterate_succ_apply, hd, iterate_derivative_add', iterate_derivative_C_mul,
        eval_add, eval_mul, eval_C]
      exact dvd_add (ihk _) (by rw [pow_succ']; exact mul_dvd_mul_left _ (ih k _))

/-- **The binomial expansion of the replaced row.** For `p h ≤ r`,
`t^s X^{r - p h} (X^p - t)^h = ∑_{i ≤ h} (-1)^i C(h,i) t^{s+i} X^{r - p i}`. -/
theorem expand_row (p r s h : ℕ) (hph : p * h ≤ r) (t : K) :
    C (t ^ s) * X ^ (r - p * h) * (X ^ p - C t) ^ h =
      ∑ i ∈ range (h + 1), C ((-1) ^ i * (h.choose i : K) * t ^ (s + i)) * X ^ (r - p * i) := by
  rw [show (X ^ p - C t : K[X]) = -C t + X ^ p by ring, add_pow, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hih : i ≤ h := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hpi : p * i ≤ p * h := Nat.mul_le_mul_left p hih
  have hsplit : r - p * i = (r - p * h) + p * (h - i) := by
    rw [Nat.mul_sub]
    generalize p * i = a at *
    generalize p * h = b at *
    omega
  rw [hsplit]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, pow_add, pow_mul]
  ring

/-- The `k`-th derivative of the replaced row, evaluated at `z`. -/
theorem eval_iterate_derivative_row (p r s h k : ℕ) (hph : p * h ≤ r) (z t : K) :
    (derivative^[k] (C (t ^ s) * X ^ (r - p * h) * (X ^ p - C t) ^ h)).eval z =
      ∑ i ∈ range (h + 1), (-1) ^ i * (h.choose i : K) *
        (((r - p * i).descFactorial k : ℕ) * z ^ (r - p * i - k) * t ^ (s + i)) := by
  rw [expand_row p r s h hph, iterate_derivative_sum, eval_finsetSum]
  refine sum_congr rfl fun i _ => ?_
  rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_natCast_mul, eval_mul, eval_C,
    eval_mul, eval_natCast, eval_pow, eval_X]
  ring

end poly

/-! ## The row replacement as a matrix -/

/-- `h_{r,s} = min(⌊r/p⌋, S - 1 - s)` (Green's exponent; companion (12)). -/
def hgt (p S r s : ℕ) : ℕ := min (r / p) (S - 1 - s)

theorem mul_hgt_le (p S r s : ℕ) : p * hgt p S r s ≤ r :=
  (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le r p)

/-- **Green's transformation matrix** `U`: row `(r, s)` has the coefficient `(-1)^i C(h,i)` of
`z^{r - p i} w^{s + i}` in `z^{r - p h} (z^p - w)^h w^s`, at column `(r - p i, s + i)`, `i ≤ h`. -/
def Umat (K : Type*) [CommRing K] (R S p : ℕ) : Matrix (Fin R × Fin S) (Fin R × Fin S) K :=
  fun a b =>
    if (a.2 : ℕ) ≤ b.2 ∧ (b.2 : ℕ) - a.2 ≤ hgt p S a.1 a.2 ∧ (b.1 : ℕ) + p * ((b.2 : ℕ) - a.2) = a.1
    then (-1) ^ ((b.2 : ℕ) - a.2) * ((hgt p S a.1 a.2).choose ((b.2 : ℕ) - a.2) : K) else 0

theorem Umat_diag (K : Type*) [CommRing K] (R S p : ℕ) (a : Fin R × Fin S) :
    Umat K R S p a a = 1 := by
  simp [Umat]

theorem Umat_low (K : Type*) [CommRing K] (R S p : ℕ) (hp : 0 < p) (a b : Fin R × Fin S)
    (hab : a ≠ b) (hlt : ¬ (b.1 < a.1)) : Umat K R S p a b = 0 := by
  unfold Umat
  rw [if_neg]
  rintro ⟨h1, -, h3⟩
  rcases Nat.eq_zero_or_pos ((b.2 : ℕ) - a.2) with h0 | h0
  · apply hab
    rw [h0, mul_zero, add_zero] at h3
    exact Prod.ext (Fin.ext h3.symm) (Fin.ext (by omega))
  · apply hlt
    have : 0 < p * ((b.2 : ℕ) - a.2) := Nat.mul_pos hp h0
    show (b.1 : ℕ) < a.1
    omega

variable (q R : ℕ)

/-- **The replaced matrix** `M̃ = U M` (for a prime `p`): row `(r, s)` is the derivative data of
`z^{r - p h} (z^p - w)^h w^s` at `(z, z̄)`, `h = h_{r,s}`. -/
noncomputable def Mtil (p : ℕ) : Matrix (Row R) (Col q R) (OK (cq q)) := fun rs zk =>
  (derivative^[zk.2] (C (star (node q R zk.1) ^ (rs.2 : ℕ)) *
      X ^ ((rs.1 : ℕ) - p * hgt p (Sof R) rs.1 rs.2) *
      (X ^ p - C (star (node q R zk.1))) ^ hgt p (Sof R) rs.1 rs.2)).eval (node q R zk.1)

/-- One inner sum of `U * M`: for a fixed target `s'`, at most one `r'` contributes. -/
theorem sum_fst_Umat_mul (p : ℕ) (rs : Row R) (zk : Col q R) (y : Fin (Sof R)) :
    ∑ x : Fin R, Umat (OK (cq q)) R (Sof R) p rs (x, y) * M q R (x, y) zk =
      if (rs.2 : ℕ) ≤ y ∧ (y : ℕ) - rs.2 ≤ hgt p (Sof R) rs.1 rs.2 then
        (-1) ^ ((y : ℕ) - rs.2) * ((hgt p (Sof R) rs.1 rs.2).choose ((y : ℕ) - rs.2) : OK (cq q)) *
          ((((rs.1 : ℕ) - p * ((y : ℕ) - rs.2)).descFactorial zk.2 : ℕ) *
            node q R zk.1 ^ ((rs.1 : ℕ) - p * ((y : ℕ) - rs.2) - zk.2) *
            star (node q R zk.1) ^ (y : ℕ))
      else 0 := by
  obtain ⟨r, s⟩ := rs
  set h := hgt p (Sof R) r s
  split_ifs with hc
  · have hle : p * ((y : ℕ) - s) ≤ r :=
      (Nat.mul_le_mul_left p hc.2).trans (mul_hgt_le p (Sof R) r s)
    have hlt : (r : ℕ) - p * ((y : ℕ) - s) < R := by omega
    rw [sum_eq_single ⟨(r : ℕ) - p * ((y : ℕ) - s), hlt⟩]
    · rw [Umat, if_pos ⟨hc.1, hc.2, by simp only; omega⟩]
      rfl
    · intro x _ hx
      rw [Umat, if_neg, zero_mul]
      rintro ⟨-, -, h3⟩
      apply hx
      ext
      simp only at h3 ⊢
      omega
    · simp
  · refine sum_eq_zero fun x _ => ?_
    rw [Umat, if_neg (fun h' => hc ⟨h'.1, h'.2.1⟩), zero_mul]

/-- **Green's row replacement is `U * M`.** -/
theorem Umat_mul_M (p : ℕ) : Umat (OK (cq q)) R (Sof R) p * M q R = Mtil q R p := by
  refine Matrix.ext fun rs zk => ?_
  obtain ⟨r, s⟩ := rs
  set h := hgt p (Sof R) r s with hh
  rw [Matrix.mul_apply, Fintype.sum_prod_type, sum_comm]
  simp_rw [sum_fst_Umat_mul q R p (r, s) zk]
  rw [Mtil, eval_iterate_derivative_row p r s h zk.2 (mul_hgt_le p (Sof R) r s)]
  -- the outer sum over `s' : Fin S`, as a sum over `s' ∈ [s, s + h]`
  set F : ℕ → OK (cq q) := fun y =>
    if (s : ℕ) ≤ y ∧ y - s ≤ h then
      (-1) ^ (y - s) * (h.choose (y - s) : OK (cq q)) *
        ((((r : ℕ) - p * (y - s)).descFactorial zk.2 : ℕ) *
          node q R zk.1 ^ ((r : ℕ) - p * (y - s) - zk.2) * star (node q R zk.1) ^ y)
    else 0 with hF
  have hS : (s : ℕ) + (h + 1) ≤ Sof R := by
    have : h ≤ Sof R - 1 - s := min_le_right _ _
    have := s.isLt
    omega
  refine (Fin.sum_univ_eq_sum_range F (Sof R)).trans ?_
  have hsub : Ico (s : ℕ) (s + (h + 1)) ⊆ range (Sof R) := by
    intro y hy
    simp only [mem_Ico] at hy
    simp only [mem_range]
    omega
  rw [← sum_subset hsub]
  · rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ h := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [hF]
    simp only [Nat.add_sub_cancel_left, le_add_iff_nonneg_right, zero_le, true_and, hi', if_true]
  · intro y _ hy
    simp only [mem_Ico, not_and, not_lt] at hy
    rw [hF]
    simp only
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have := hy h1
    omega

/-- Every maximal minor of `M` equals the same minor of the replaced matrix. -/
theorem minor_eq_det_Mtil {p : ℕ} (hp : 0 < p) (f : Row R → Col q R) :
    minor q R f = ((Mtil q R p).submatrix id f).det := by
  rw [minor, ← Umat_mul_M q R p, det_submatrix_mul_of_fst_unitriangular _ (Umat_diag _ _ _ p)
    (Umat_low _ _ _ p hp)]

/-- **(12), in `ℤ[ω]`.** For an inert prime `p`, every maximal minor is divisible by
`p^{∑_{r,s} h_{r,s}}`. -/
theorem pow_dvd_minor {p : ℕ} (hp : p.Prime) (hi : IsInert (cq q) p) (f : Row R → Col q R) :
    (p : OK (cq q)) ^ (∑ i : Row R, hgt p (Sof R) i.1 i.2) ∣ minor q R f := by
  classical
  rw [minor_eq_det_Mtil q R hp.pos]
  refine pow_sum_dvd_det _ _ (fun i : Row R => hgt p (Sof R) i.1 i.2) fun i j => ?_
  exact pow_dvd_eval_iterate_derivative p (frobenius_dvd hp hi _) _ _ _

/-- **(12).** For an inert prime `p`, `p^{2 ∑ h_{r,s}}` divides `N(D₀)`. -/
theorem pow_two_mul_dvd_norm_minor {p : ℕ} (hp : p.Prime) (hi : IsInert (cq q) p)
    (f : Row R → Col q R) :
    (p : ℤ) ^ (2 * ∑ i : Row R, hgt p (Sof R) i.1 i.2) ∣ QuadraticAlgebra.norm (minor q R f) := by
  obtain ⟨y, hy⟩ := pow_dvd_minor q R hp hi f
  rw [hy, map_mul, map_pow, QuadraticAlgebra.norm_natCast, ← pow_mul]
  exact dvd_mul_right _ _

end ELEM.Divisibility
