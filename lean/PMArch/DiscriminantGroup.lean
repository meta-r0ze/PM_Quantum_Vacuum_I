import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The discriminant group has `|det G|` elements

For a nondegenerate integral Gram matrix `G`, the discriminant group `ℤⁿ / Gℤⁿ` (the clock's
state set, by Postulate CM) has exactly `|det G|` elements. This turns "the clock period is the
number of clock states" into `Δ = |D|`.
-/

open Matrix

namespace PMArch.DiscriminantGroup

/-- `|ℤⁿ / Gℤⁿ| = |det G|`. -/
theorem card_discriminant_group {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.det ≠ 0) :
    Nat.card ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.toLin' G)) = G.det.natAbs := by
  have hinj : Function.Injective (Matrix.toLin' G) := by
    intro x y h
    have h1 : G *ᵥ (x - y) = 0 := by
      rw [mulVec_sub]; simpa [Matrix.toLin'_apply, sub_eq_zero] using h
    have h2 : G.det • (x - y) = 0 := by
      rw [← one_smul ℤ (x - y), ← smul_assoc, smul_eq_mul, mul_one, ← one_mulVec (x - y),
        ← smul_mulVec, ← adjugate_mul, ← mulVec_mulVec, h1, mulVec_zero]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hG
    · exact sub_eq_zero.mp h3
  let e := LinearEquiv.ofInjective (Matrix.toLin' G) hinj
  have := Submodule.natAbs_det_equiv (LinearMap.range (Matrix.toLin' G)) e.toAddEquiv
  rw [← this, ← LinearMap.det_toLin' G]
  rfl

end PMArch.DiscriminantGroup
