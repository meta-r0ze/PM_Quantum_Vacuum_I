import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# ELEM.Size.Leibniz: the row-wise Leibniz bound for a complex determinant

We replace the companion's Hadamard step (companion (11);
twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae) by the cruder Leibniz bound
`|det A| ≤ N! ∏_i b_i` when every entry of row `i` has modulus at most `b_i`. Mathlib's
`Matrix.det_le` (LinearAlgebra/Matrix/AbsoluteValue.lean) is the uniform version (one bound for all
entries); the proof below follows the same route through `Matrix.det_apply`, keeping one bound per
row, and uses that a permutation meets every row exactly once.
-/

set_option autoImplicit false

open Matrix Equiv Finset

namespace ELEM.Size

/-- **Row-wise Leibniz bound.** If every entry of row `i` of a square complex matrix has norm at
most `b i`, then `‖det A‖ ≤ (card n)! * ∏ i, b i`. -/
theorem norm_det_le_factorial_mul_prod {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b : n → ℝ) (hb : ∀ i j, ‖A i j‖ ≤ b i) :
    ‖A.det‖ ≤ ((Fintype.card n).factorial : ℝ) * ∏ i, b i := by
  calc ‖A.det‖ = ‖∑ σ : Perm n, Perm.sign σ • ∏ i, A (σ i) i‖ := by rw [det_apply]
    _ ≤ ∑ σ : Perm n, ‖Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Perm n, ∏ i, ‖A (σ i) i‖ := by
        refine sum_congr rfl fun σ _ => ?_
        rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h, norm_prod]
    _ ≤ ∑ σ : Perm n, ∏ i, b (σ i) := by
        gcongr with σ _ i _
        exact hb (σ i) i
    _ = ∑ _σ : Perm n, ∏ i, b i := by
        refine sum_congr rfl fun σ _ => ?_
        exact Equiv.prod_comp σ b
    _ = ((Fintype.card n).factorial : ℝ) * ∏ i, b i := by
        simp [Fintype.card_perm]

end ELEM.Size
