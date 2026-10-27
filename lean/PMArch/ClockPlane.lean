import PMArch.Clock
import PMArch.Lattices

/-!
# The clock as a substrate plane

By Closure the clock is built from the substrate: its period lattice is the rank-2 sublattice
`ℤu + ℤv` of the even substrate lattice. Its states are taken to be the discriminant group
`Λ_c*/Λ_c` (the cokernel of its Gram matrix), the finite group determined by the lattice and its
form alone; that identification is a modeling step, not proved here to be unique.

* `plane_form`: the half-norm of a plane in an even lattice is an integral binary form whose
  discriminant is `-det` of the plane's Gram matrix. Integrality, hence complex multiplication,
  is forced rather than postulated.
* `e8_clock_plane`: `E₈` contains a plane with half-norm form `x² + xy + 11y²` (`D = -43`).
* `clock_glue`: that plane's discriminant group `ℤ²/Gℤ²` is `ℤ/43`, a single cycle of
  `43 = |D|` states.
-/

namespace PMArch.ClockPlane
open Matrix PMArch.Clock

/-- The half-norm form of the plane spanned by `u, v` in an even lattice with Gram `A`. -/
def planeForm (A : Matrix (Fin 8) (Fin 8) ℤ) (u v : Fin 8 → ℤ) : Form :=
  ⟨(u ⬝ᵥ (A *ᵥ u)) / 2, u ⬝ᵥ (A *ᵥ v), (v ⬝ᵥ (A *ᵥ v)) / 2⟩

/-- **Integrality is forced.** In an even lattice with symmetric Gram matrix, the half-norm of
`x u + y v` is the integral form `planeForm`, and its discriminant is minus the determinant of
the plane's Gram matrix. -/
theorem plane_form (A : Matrix (Fin 8) (Fin 8) ℤ) (hsym : Aᵀ = A)
    (heven : ∀ z : Fin 8 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (u v : Fin 8 → ℤ) :
    (∀ x y : ℤ, ((x • u + y • v) ⬝ᵥ (A *ᵥ (x • u + y • v))) = 2 * (planeForm A u v).eval x y) ∧
    (planeForm A u v).disc = (u ⬝ᵥ (A *ᵥ v)) ^ 2 - (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) := by
  obtain ⟨p, hp⟩ := heven u
  obtain ⟨q, hq⟩ := heven v
  have hvu : v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  have hp2 : (u ⬝ᵥ (A *ᵥ u)) / 2 = p := by omega
  have hq2 : (v ⬝ᵥ (A *ᵥ v)) / 2 = q := by omega
  refine ⟨fun x y => ?_, ?_⟩
  · simp only [planeForm, Form.eval, hp2, hq2, mulVec_add, mulVec_smul, dotProduct_add,
      add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, hvu]
    rw [hp, hq]; ring
  · simp only [planeForm, Form.disc, hp2, hq2]
    rw [hp, hq]; ring

/-- A temporal-spatial clock plane inside `E₈`. -/
def cu : Fin 8 → ℤ := ![1, 0, 0, 0, 0, 0, 0, 0]
def cv : Fin 8 → ℤ := ![0, -2, -1, 1, -1, 0, 0, 0]

lemma e8_plane_gram :
    cu ⬝ᵥ (Lattices.gram *ᵥ cu) = 2 ∧ cu ⬝ᵥ (Lattices.gram *ᵥ cv) = 1 ∧
      cv ⬝ᵥ (Lattices.gram *ᵥ cv) = 22 := by decide

/-- **E₈ contains the clock.** The plane `ℤ cu + ℤ cv ⊂ E₈` has half-norm form
`x² + xy + 11y²`, of discriminant `-43`, the unique class in the window. -/
theorem e8_clock_plane :
    planeForm Lattices.gram cu cv = ⟨1, 1, 11⟩ ∧ (planeForm Lattices.gram cu cv).disc = -43 := by
  obtain ⟨h1, h2, h3⟩ := e8_plane_gram
  simp only [planeForm, h1, h2, h3, Form.disc]
  decide

/-- **The clock's states.** The discriminant group of the clock plane (Gram `[[2,1],[1,22]]`) is
`ℤ/43`: a vector `w` lies in `Gℤ²` iff `43 ∣ w₁ - 2 w₂`, and `w ↦ w₁ - 2w₂ mod 43` is onto. -/
theorem clock_glue (w : ℤ × ℤ) :
    (∃ s t : ℤ, (2 * s + t, s + 22 * t) = w) ↔ (43 : ℤ) ∣ w.1 - 2 * w.2 := by
  constructor
  · rintro ⟨s, t, rfl⟩
    exact ⟨-t, by ring⟩
  · rintro ⟨k, hk⟩
    refine ⟨w.2 + 22 * k, -k, ?_⟩
    ext <;> simp only <;> linarith

/-- The clock steps through all `43` classes before returning. -/
theorem clock_glue_period : addOrderOf (1 : ZMod 43) = 43 := ZMod.addOrderOf_one 43

end PMArch.ClockPlane
