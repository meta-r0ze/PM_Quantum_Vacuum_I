import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Norm parity

The binary label `p(z) = Q(z) mod 2` of an integral quadratic form, and its additivity.
Used by the evenness theorem (`OrthogonalExchange`).
-/
namespace PMArch.IntrinsicConstraints
open Matrix

/-- A binary label computed from the state and its pairing, with no external
bit or independent preparation parameter. -/
def parity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) : ZMod 2 :=
  (z ⬝ᵥ (A *ᵥ z) : ℤ)

lemma quadratic_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hs : A.IsSymm)
    (x y : Fin n → ℤ) :
    (x+y) ⬝ᵥ (A *ᵥ (x+y)) =
      x ⬝ᵥ (A *ᵥ x) + y ⬝ᵥ (A *ᵥ y) + 2*(x ⬝ᵥ (A *ᵥ y)) := by
  have hxy : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm]
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [hxy]
  ring

/-- Norm parity is additive. A nontrivial intrinsic binary label is compatible
with integral costs; conservation does not force that label to vanish. -/
theorem parity_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hs : A.IsSymm)
    (x y : Fin n → ℤ) : parity A (x+y) = parity A x + parity A y := by
  unfold parity
  rw [quadratic_add A hs]
  push_cast
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [htwo]

/-- Requiring trivial intrinsic parity is exactly evenness, rather than a new
derivation of it. -/
theorem trivial_parity_iff_even {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (∀ z, parity A z = 0) ↔ (∀ z, Even (z ⬝ᵥ (A *ᵥ z))) := by
  simp only [parity, ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
  norm_num

end PMArch.IntrinsicConstraints
