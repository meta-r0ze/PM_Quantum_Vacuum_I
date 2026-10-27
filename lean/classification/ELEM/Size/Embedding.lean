import ELEM.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# ELEM.Size.Embedding: the complex embedding of `ℤ[ω]`

For `c ≥ 1`, `ψ = (1 + i √(4c - 1))/2` satisfies `ψ² = ψ - c`, so `QuadraticAlgebra.lift` gives a
ring map `emb : OK c → ℂ`, `x + y ω ↦ x + y ψ`. Its squared modulus is the norm form,
`|emb z|² = x² + x y + c y² = N(z)`; in particular `|emb (star z)| = |emb z|`. This is the complex
absolute value used in the size bound (11) of the companion (twinheterodox/tenth-discriminant,
companions/elementary, commit 64694aae), where `Δ = D₀ D̄₀ = |D₀|²`.
-/

set_option autoImplicit false

open QuadraticAlgebra

namespace ELEM.Size

/-- `ψ = (1 + i √(4c - 1))/2`, a root of `X² - X + c`. -/
noncomputable def psi (c : ℕ) : ℂ := ⟨1 / 2, Real.sqrt (4 * c - 1) / 2⟩

theorem psi_mul_psi {c : ℕ} (hc : 1 ≤ c) :
    psi c * psi c = (-(c : ℤ)) • (1 : ℂ) + (1 : ℤ) • psi c := by
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hs : Real.sqrt (4 * c - 1) * Real.sqrt (4 * c - 1) = 4 * c - 1 :=
    Real.mul_self_sqrt (by linarith)
  apply Complex.ext
  · simp [psi, zsmul_eq_mul]
    linarith
  · simp [psi, zsmul_eq_mul]
    ring

/-- The complex embedding `OK c → ℂ`, `ω ↦ ψ`. -/
noncomputable def emb (c : ℕ) (hc : 1 ≤ c) : OK c →ₐ[ℤ] ℂ :=
  QuadraticAlgebra.lift ⟨psi c, psi_mul_psi hc⟩

theorem emb_apply {c : ℕ} (hc : 1 ≤ c) (z : OK c) :
    emb c hc z = (z.re : ℂ) + (z.im : ℂ) * psi c := by
  simp [emb, zsmul_eq_mul]

/-- `|emb z|² = N(z)`. -/
theorem normSq_emb {c : ℕ} (hc : 1 ≤ c) (z : OK c) :
    Complex.normSq (emb c hc z) = ((QuadraticAlgebra.norm z : ℤ) : ℝ) := by
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hs : Real.sqrt (4 * c - 1) * Real.sqrt (4 * c - 1) = 4 * c - 1 :=
    Real.mul_self_sqrt (by linarith)
  rw [emb_apply, Complex.normSq_apply, QuadraticAlgebra.norm_def]
  simp only [psi, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im]
  push_cast
  linear_combination ((z.im : ℝ) ^ 2 / 4) * hs

theorem norm_emb_sq {c : ℕ} (hc : 1 ≤ c) (z : OK c) :
    ‖emb c hc z‖ ^ 2 = ((QuadraticAlgebra.norm z : ℤ) : ℝ) := by
  rw [← normSq_emb hc z, Complex.normSq_eq_norm_sq]

theorem norm_emb_star {c : ℕ} (hc : 1 ≤ c) (z : OK c) :
    ‖emb c hc (star z)‖ = ‖emb c hc z‖ := by
  have h : ‖emb c hc (star z)‖ ^ 2 = ‖emb c hc z‖ ^ 2 := by
    rw [norm_emb_sq, norm_emb_sq, QuadraticAlgebra.norm_star]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

end ELEM.Size
