import Mathlib.LinearAlgebra.Matrix.Block

/-!
# ELEM.Divisibility.Det: two determinant facts for the Frobenius divisibility step

Green's row replacement (hexagon 2610.00311v2, Lemma 5.1, as used in the elementary
companion, twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae, section 4.3)
needs two facts about determinants over a commutative ring:

* `det_submatrix_mul_of_fst_unitriangular`: if `U` over `Fin R × Fin S` has unit diagonal and is
  zero off the diagonal unless the column's first coordinate is strictly below the row's, then every
  maximal minor of `U * M` equals the same minor of `M`. The product order on `Fin R × Fin S` is
  not linear, so we reindex to the lexicographic order.
* `pow_sum_dvd_det`: if every entry of row `i` is divisible by `x ^ e i`, then `x ^ ∑ e ∣ det`.
-/

set_option autoImplicit false

open Matrix

namespace ELEM.Divisibility

/-- A matrix over `Fin R × Fin S` with unit diagonal whose off-diagonal entries vanish unless the
column's first coordinate is strictly below the row's has determinant `1`. -/
theorem det_eq_one_of_fst_unitriangular {K : Type*} [CommRing K] {R S : ℕ}
    (U : Matrix (Fin R × Fin S) (Fin R × Fin S) K) (hdiag : ∀ i, U i i = 1)
    (hlow : ∀ i j, i ≠ j → ¬ (j.1 < i.1) → U i j = 0) : U.det = 1 := by
  classical
  let e : Fin R × Fin S ≃ Lex (Fin R × Fin S) := toLex
  rw [← det_reindex_self e U]
  have htri : (reindex e e U).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    simp only [reindex_apply, submatrix_apply]
    apply hlow
    · intro h
      exact (ne_of_lt hij') (e.symm.injective h)
    · intro h
      have h1 : (ofLex j).1 < (ofLex i).1 := h
      rcases Prod.Lex.lt_iff.mp hij' with h2 | ⟨h2, -⟩
      · exact absurd (h1.trans h2) (lt_irrefl _)
      · exact absurd (h2 ▸ h1) (lt_irrefl _)
  rw [det_of_isLowerTriangular _ htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp only [reindex_apply, submatrix_apply]
  exact hdiag _

/-- A maximal minor of `U * M` equals that of `M`, for `U` as in
`det_eq_one_of_fst_unitriangular`. -/
theorem det_submatrix_mul_of_fst_unitriangular {K : Type*} [CommRing K] {R S : ℕ} {ι : Type*}
    (U : Matrix (Fin R × Fin S) (Fin R × Fin S) K) (hdiag : ∀ i, U i i = 1)
    (hlow : ∀ i j, i ≠ j → ¬ (j.1 < i.1) → U i j = 0)
    (M : Matrix (Fin R × Fin S) ι K) (f : Fin R × Fin S → ι) :
    ((U * M).submatrix id f).det = (M.submatrix id f).det := by
  have h : (U * M).submatrix id f = U * M.submatrix id f := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul, det_eq_one_of_fst_unitriangular U hdiag hlow, one_mul]

/-- **Row divisibility.** If every entry of row `i` is divisible by `x ^ e i`, then the determinant
is divisible by `x ^ ∑ᵢ e i` (each Leibniz term picks one entry from every row). -/
theorem pow_sum_dvd_det {K : Type*} [CommRing K] {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m K) (x : K) (e : m → ℕ) (h : ∀ i j, x ^ e i ∣ A i j) :
    x ^ (∑ i, e i) ∣ A.det := by
  rw [det_apply]
  refine Finset.dvd_sum fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  apply Dvd.dvd.mul_left
  rw [← Equiv.sum_comp σ e, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => h (σ i) i

end ELEM.Divisibility
