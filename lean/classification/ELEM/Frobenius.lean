import ELEM.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Algebra

/-!
# ELEM.Frobenius: at an inert prime, Frobenius is conjugation

For a prime `p` with `IsInert c p` (no root of `X² - X + c` mod `p`; `p = 2` included), and every
`z ∈ OK c = ℤ[ω]`,

  `z ^ p ≡ z̄ (mod p OK c)`        (`frobenius_dvd`).

This is the shared input of the nonvanishing step (companion 4.1, with `p = R`: `z̄ = z^R` in
`𝔽_{R²}`) and of the divisibility step (companion 4.3, for every inert `p ≤ R`).

Proof. Reduce mod `p` into `Fp2 c p = 𝔽_p[ω]`, a field by `IsInert c p` (Mathlib's
`Field (QuadraticAlgebra K a b)`). There `u = ω^p` is again a root of `X² - X + c`, so `u = ω` or
`u = 1 - ω = ω̄`. If `u = ω`, then `x ↦ x^p` fixes `ω` and `𝔽_p`, hence every element, and
`X^p - X` has the `p + 1` distinct roots `𝔽_p ∪ {ω}`, more than its degree. So `ω^p = ω̄`, and
`(x + yω)^p = x + y ω̄` by `x^p = x` on `𝔽_p`.
-/

set_option autoImplicit false

open QuadraticAlgebra Polynomial

namespace ELEM

variable {c p : ℕ}

/-! ## Reduction mod `p` -/

/-- Reduction `ℤ[ω] → 𝔽_p[ω]`, coordinatewise. -/
def redHom (c p : ℕ) : OK c →+* Fp2 c p where
  toFun z := ⟨(z.re : ZMod p), (z.im : ZMod p)⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

@[simp] theorem redHom_re (z : OK c) : (redHom c p z).re = (z.re : ZMod p) := rfl

@[simp] theorem redHom_im (z : OK c) : (redHom c p z).im = (z.im : ZMod p) := rfl

theorem redHom_star (z : OK c) : redHom c p (star z) = star (redHom c p z) := by
  ext <;> simp

/-- The kernel of the reduction is `p · OK c`. -/
theorem natCast_dvd_of_redHom_eq_zero {w : OK c} (h : redHom c p w = 0) : (p : OK c) ∣ w := by
  have hre : (w.re : ZMod p) = 0 := by simpa using congrArg QuadraticAlgebra.re h
  have him : (w.im : ZMod p) = 0 := by simpa using congrArg QuadraticAlgebra.im h
  rw [show (p : OK c) = algebraMap ℤ (OK c) (p : ℤ) by simp, algebraMap_dvd_iff]
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hre,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp him⟩

/-! ## Frobenius in `𝔽_p[ω]` -/

section field

variable [hp : Fact p.Prime] [hi : Fact (IsInert c p)]

instance : CharP (Fp2 c p) p := charP_of_injective_algebraMap algebraMap_injective p

omit hi in
theorem star_omega_eq : star (ω : Fp2 c p) = 1 - ω := by
  ext <;> simp

omit hi in
theorem omega_sq_eq : (ω : Fp2 c p) ^ 2 = algebraMap (ZMod p) (Fp2 c p) (-(c : ZMod p)) + ω := by
  ext <;> simp [pow_two]

/-- If `x ↦ x^p` fixed `ω`, then `X^p - X` would have the `p + 1` roots `𝔽_p ∪ {ω}`. -/
theorem omega_pow_ne_omega : (ω : Fp2 c p) ^ p ≠ ω := by
  intro h
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set F := Fp2 c p
  set ι := algebraMap (ZMod p) F
  have hP : (X ^ p - X : F[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hp.out.one_lt
  have hnot : (ω : F) ∉ Finset.univ.image ι := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro x hx
    have := congrArg QuadraticAlgebra.im hx
    rw [show (ι x).im = 0 from rfl, im_omega] at this
    exact zero_ne_one this
  set Z : Finset F := insert ω (Finset.univ.image ι)
  have hcard : Z.card = p + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ algebraMap_injective,
      Finset.card_univ, ZMod.card]
  have hsub : Z.val ⊆ (X ^ p - X : F[X]).roots := by
    intro z hz
    rw [mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact h
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← map_pow, ZMod.pow_card]
  have := card_le_degree_of_subset_roots hsub
  rw [hcard, FiniteField.X_pow_card_sub_X_natDegree_eq F hp.out.one_lt] at this
  omega

/-- `ω^p = ω̄` in `𝔽_p[ω]`. -/
theorem omega_pow_eq_star : (ω : Fp2 c p) ^ p = star ω := by
  set u := (ω : Fp2 c p) ^ p with hu
  have hu2 : u ^ 2 = algebraMap (ZMod p) (Fp2 c p) (-(c : ZMod p)) + u := by
    calc u ^ 2 = ((ω : Fp2 c p) ^ 2) ^ p := by rw [hu, ← pow_mul, ← pow_mul, mul_comm]
      _ = (algebraMap (ZMod p) (Fp2 c p) (-(c : ZMod p)) + ω) ^ p := by rw [omega_sq_eq]
      _ = algebraMap (ZMod p) (Fp2 c p) (-(c : ZMod p)) ^ p + (ω : Fp2 c p) ^ p :=
          add_pow_char _ _ _
      _ = _ := by rw [← map_pow, ZMod.pow_card]
  have hprod : (u - ω) * (u - star ω) = 0 := by
    rw [star_omega_eq]
    linear_combination hu2 - omega_sq_eq (c := c) (p := p)
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) omega_pow_ne_omega
  · exact sub_eq_zero.mp h

/-- **Frobenius is conjugation on `𝔽_p[ω]`** for inert `p`: `w ^ p = w̄`. -/
theorem pow_char_eq_star (w : Fp2 c p) : w ^ p = star w := by
  have hw : w = algebraMap (ZMod p) (Fp2 c p) w.re + algebraMap (ZMod p) (Fp2 c p) w.im * ω := by
    ext <;> simp
  rw [hw, add_pow_char, mul_pow, ← map_pow, ← map_pow, ZMod.pow_card, ZMod.pow_card,
    omega_pow_eq_star]
  ext <;> simp

end field

/-- **Frobenius at an inert prime is conjugation.** For a prime `p` with `IsInert c p` (including
`p = 2`) and every `z ∈ ℤ[ω]`, `p ∣ z^p - z̄`. -/
theorem frobenius_dvd (hp : p.Prime) (hi : IsInert c p) (z : OK c) :
    (p : OK c) ∣ z ^ p - star z := by
  have := Fact.mk hp
  have := Fact.mk hi
  apply natCast_dvd_of_redHom_eq_zero
  rw [map_sub, map_pow, redHom_star, pow_char_eq_star, sub_self]

end ELEM
