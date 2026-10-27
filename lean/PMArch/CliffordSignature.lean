import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic

/-! Algebraic signature dependence, without physical metric selection. -/
noncomputable section
namespace PMArch.Clifford
open CliffordAlgebra

def form (s : Fin 4 → ℝ) : QuadraticForm ℝ (Fin 4 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ s

def axis (i : Fin 4) : Fin 4 → ℝ := Pi.single i 1

def generator (s : Fin 4 → ℝ) (i : Fin 4) : CliffordAlgebra (form s) :=
  ι (form s) (axis i)

theorem generator_square (s : Fin 4 → ℝ) (i : Fin 4) :
    generator s i * generator s i = algebraMap ℝ _ (s i) := by
  rw [generator, ι_sq_scalar]
  congr 1
  fin_cases i <;> simp [form, axis, QuadraticMap.weightedSumSquares_apply,
    Pi.single_apply]

theorem generator_anticommute (s : Fin 4 → ℝ) (i j : Fin 4) (h : i ≠ j) :
    generator s i * generator s j = -(generator s j * generator s i) := by
  apply eq_neg_of_add_eq_zero_left
  change ι (form s) (axis i) * ι (form s) (axis j) +
    ι (form s) (axis j) * ι (form s) (axis i) = 0
  rw [ι_mul_ι_add_swap]
  have hp : QuadraticMap.polar (form s) (axis i) (axis j) = 0 := by
    fin_cases i <;> fin_cases j <;>
      simp_all [QuadraticMap.polar, form, axis, QuadraticMap.weightedSumSquares_apply,
        Fin.sum_univ_succ, Pi.single_apply]
  rw [hp, map_zero]

private theorem slide {A : Type*} [Ring A] {a b : A}
    (h : a * b = -(b * a)) (x : A) : a * (b * x) = -(b * (a * x)) := by
  rw [← mul_assoc, h]
  noncomm_ring

private theorem square_slide (s : Fin 4 → ℝ) (i : Fin 4)
    (x : CliffordAlgebra (form s)) :
    generator s i * (generator s i * x) = algebraMap ℝ _ (s i) * x := by
  rw [← mul_assoc, generator_square]

def volume (s : Fin 4 → ℝ) : CliffordAlgebra (form s) :=
  generator s 0 * generator s 1 * generator s 2 * generator s 3

theorem volume_square (s : Fin 4 → ℝ) :
    volume s * volume s = algebraMap ℝ _ (s 0 * s 1 * s 2 * s 3) := by
  have h10 := generator_anticommute s 1 0 (by decide)
  have h20 := generator_anticommute s 2 0 (by decide)
  have h30 := generator_anticommute s 3 0 (by decide)
  have h21 := generator_anticommute s 2 1 (by decide)
  have h31 := generator_anticommute s 3 1 (by decide)
  have h32 := generator_anticommute s 3 2 (by decide)
  simp only [volume, mul_assoc, slide h10, slide h20, slide h30,
    slide h21, slide h31, slide h32, mul_neg, neg_neg, square_slide]
  simp only [← mul_assoc, generator_square]
  simp only [map_mul]

def signs (q : Fin 5) (i : Fin 4) : ℝ := if i.val < q.val then -1 else 1

theorem signature_product (q : Fin 5) :
    signs q 0 * signs q 1 * signs q 2 * signs q 3 = (-1 : ℝ) ^ q.val := by
  fin_cases q <;> norm_num [signs]

theorem signature_volume_square (q : Fin 5) :
    volume (signs q) * volume (signs q) =
      algebraMap ℝ _ ((-1 : ℝ) ^ q.val) := by
  rw [volume_square, signature_product]

theorem negative_square_iff (q : Fin 5) :
    (-1 : ℝ) ^ q.val = -1 ↔ q.val = 1 ∨ q.val = 3 := by
  fin_cases q <;> norm_num

end PMArch.Clifford
