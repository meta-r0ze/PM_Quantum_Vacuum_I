import Mathlib

/-!
# Foundations for the imaginary quadratic field `K = ℚ(√-m)`, part 1

Pinned environment: Lean v4.34.1, Mathlib d13f23b (the openai/math `OAI` root).

Setting (the statement of `CN1Challenges.ClassNumberOne`): `K` is a number field with
`Module.finrank ℚ K = 2`, `m : ℕ` is squarefree, and `α : K` satisfies `α ^ 2 = -m`.
We write `d = disc m = |disc K|` (`m` if `m ≡ 3 (mod 4)`, else `4m`) and
`ω = omega m α` (`(1 + α)/2` if `m ≡ 3 (mod 4)`, else `α`).

This file proves:

1. `{1, α}` is a `ℚ`-basis of `K` (`qBasis`), with the trace and norm of `a + bα`
   (`trace_rat_add_rat_mul_alpha`, `norm_rat_add_rat_mul_alpha`).
2. `𝓞 K = ℤ[ω]`: `omega_isIntegral`, `exists_int_add_int_mul_omega_of_isIntegral`,
   `int_add_int_mul_omega_inj`, and the `ℤ`-basis `intBasis : Basis (Fin 2) ℤ (𝓞 K)` with
   `intBasis_zero = 1`, `intBasis_one = omegaInt`.
3. The norm form: `norm_int_add_int_mul_omega : N(x + yω) = principalForm m x y`, and the
   same for `Algebra.norm ℤ` on `𝓞 K` (`norm_int_eq_principalForm`).
4. The units: for `m ∉ {1, 3}`, every unit of `𝓞 K` is `±1` (`coe_unit_eq_one_or_neg_one`).

All of it is Mathlib-only.
-/

set_option autoImplicit false

namespace CN1.Foundations

open NumberField Module Polynomial

/-- `|disc ℚ(√-m)|` for squarefree `m ≥ 1`: `m` if `m ≡ 3 (mod 4)`, else `4m`. -/
def disc (m : ℕ) : ℕ := if m % 4 = 3 then m else 4 * m

/-- The principal binary quadratic form of discriminant `-disc m`:
`x² + xy + ((m+1)/4) y²` if `m ≡ 3 (mod 4)`, else `x² + m y²`. -/
def principalForm (m : ℕ) (x y : ℤ) : ℤ :=
  if m % 4 = 3 then x ^ 2 + x * y + ((m + 1) / 4 : ℕ) * y ^ 2 else x ^ 2 + m * y ^ 2

variable {K : Type*} [Field K] [NumberField K]

/-- The generator `ω` of the ring of integers over `ℤ`: `(1 + α)/2` if `m ≡ 3 (mod 4)`,
else `α`. -/
noncomputable def omega (m : ℕ) (α : K) : K := if m % 4 = 3 then (1 + α) / 2 else α

lemma disc_of_three_mod_four {m : ℕ} (h : m % 4 = 3) : disc m = m := by simp [disc, h]

lemma disc_of_not_three_mod_four {m : ℕ} (h : m % 4 ≠ 3) : disc m = 4 * m := by simp [disc, h]

lemma omega_of_three_mod_four {m : ℕ} (α : K) (h : m % 4 = 3) : omega m α = (1 + α) / 2 := by
  simp [omega, h]

lemma omega_of_not_three_mod_four {m : ℕ} (α : K) (h : m % 4 ≠ 3) : omega m α = α := by
  simp [omega, h]

lemma principalForm_of_three_mod_four {m : ℕ} (h : m % 4 = 3) (x y : ℤ) :
    principalForm m x y = x ^ 2 + x * y + ((m + 1) / 4 : ℕ) * y ^ 2 := by
  simp [principalForm, h]

lemma principalForm_of_not_three_mod_four {m : ℕ} (h : m % 4 ≠ 3) (x y : ℤ) :
    principalForm m x y = x ^ 2 + m * y ^ 2 := by
  simp [principalForm, h]

/-- A squarefree natural number is not divisible by `4`. -/
lemma squarefree_not_four_dvd {m : ℕ} (hm : Squarefree m) : ¬ 4 ∣ m := fun h ↦ by
  have := Nat.isUnit_iff.mp (hm 2 (by simpa using h))
  omega

lemma squarefree_mod_four_ne_zero {m : ℕ} (hm : Squarefree m) : m % 4 ≠ 0 :=
  fun h ↦ squarefree_not_four_dvd hm (Nat.dvd_of_mod_eq_zero h)

/-! ### The field model: `{1, α}` is a `ℚ`-basis of `K`. -/

section FieldModel

variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))

include hα in
lemma alpha_ne_zero (hm : m ≠ 0) : α ≠ 0 := by
  rintro rfl
  have h : (m : K) = 0 := by rw [← neg_eq_zero, ← hα]; simp
  exact hm (by exact_mod_cast h)

include hα in
lemma linearIndependent_one_alpha (hm : m ≠ 0) : LinearIndependent ℚ ![(1 : K), α] := by
  rw [linearIndependent_fin2]
  refine ⟨by simpa using alpha_ne_zero hα hm, fun a ha ↦ ?_⟩
  change a • α = 1 at ha
  have h2 : ((a : K)) ^ 2 * α ^ 2 = 1 := by rw [← mul_pow, ← Rat.smul_def, ha, one_pow]
  rw [hα] at h2
  have h3 : ((a ^ 2 * (-(m : ℚ)) : ℚ) : K) = ((1 : ℚ) : K) := by push_cast; exact h2
  have h4 : a ^ 2 * (-(m : ℚ)) = 1 := Rat.cast_injective h3
  have h5 : (0 : ℚ) ≤ a ^ 2 := sq_nonneg a
  have h6 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  nlinarith

variable (hK : finrank ℚ K = 2) (hm : m ≠ 0)
include hα hK hm

/-- The `ℚ`-basis `{1, α}` of `K`. -/
noncomputable def qBasis : Basis (Fin 2) ℚ K :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_alpha hα hm) (by simp [hK])

@[simp] lemma qBasis_zero : qBasis hα hK hm 0 = 1 := by simp [qBasis]

@[simp] lemma qBasis_one : qBasis hα hK hm 1 = α := by simp [qBasis]

lemma qBasis_repr (x : K) (c : Fin 2 → ℚ) (h : x = (c 0 : K) + (c 1 : K) * α) :
    (qBasis hα hK hm).repr x = c := by
  conv_rhs => rw [← (qBasis hα hK hm).repr_sum_self c]
  congr 1
  rw [h, Fin.sum_univ_two, qBasis_zero, qBasis_one, Rat.smul_def, Rat.smul_def, mul_one]

/-- Every element of `K` is `a + bα` with `a, b : ℚ`. -/
theorem exists_rat_add_rat_mul_alpha (x : K) : ∃ a b : ℚ, x = (a : K) + (b : K) * α := by
  refine ⟨(qBasis hα hK hm).repr x 0, (qBasis hα hK hm).repr x 1, ?_⟩
  conv_lhs => rw [← (qBasis hα hK hm).sum_repr x]
  rw [Fin.sum_univ_two, qBasis_zero, qBasis_one, Rat.smul_def, Rat.smul_def, mul_one]

/-- The coordinates in the basis `{1, α}` are unique. -/
theorem rat_add_rat_mul_alpha_inj {a b a' b' : ℚ}
    (h : (a : K) + (b : K) * α = (a' : K) + (b' : K) * α) : a = a' ∧ b = b' := by
  have h1 := qBasis_repr hα hK hm ((a : K) + (b : K) * α) ![a, b] (by simp)
  have h2 := qBasis_repr hα hK hm ((a' : K) + (b' : K) * α) ![a', b'] (by simp)
  rw [h, h2] at h1
  exact ⟨by simpa using (congrFun h1 0).symm, by simpa using (congrFun h1 1).symm⟩

lemma leftMulMatrix_rat_add_rat_mul_alpha (a b : ℚ) :
    Algebra.leftMulMatrix (qBasis hα hK hm) ((a : K) + (b : K) * α) =
      !![a, -(m : ℚ) * b; b, a] := by
  set B := qBasis hα hK hm with hB
  have h0 : B.repr (((a : K) + (b : K) * α) * B 0) = ![a, b] := by
    rw [hB, qBasis_zero, mul_one]
    exact qBasis_repr hα hK hm _ _ (by simp)
  have h1 : B.repr (((a : K) + (b : K) * α) * B 1) = ![-(m : ℚ) * b, a] := by
    rw [hB, qBasis_one]
    refine qBasis_repr hα hK hm _ _ ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    linear_combination (b : K) * hα
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Algebra.leftMulMatrix_eq_repr_mul, h0, h1]

/-- `Tr(a + bα) = 2a`. -/
theorem trace_rat_add_rat_mul_alpha (a b : ℚ) :
    Algebra.trace ℚ K ((a : K) + (b : K) * α) = 2 * a := by
  rw [Algebra.trace_eq_matrix_trace (qBasis hα hK hm),
    leftMulMatrix_rat_add_rat_mul_alpha hα hK hm, Matrix.trace_fin_two_of]
  ring

/-- `N(a + bα) = a² + m b²`. -/
theorem norm_rat_add_rat_mul_alpha (a b : ℚ) :
    Algebra.norm ℚ ((a : K) + (b : K) * α) = a ^ 2 + m * b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (qBasis hα hK hm),
    leftMulMatrix_rat_add_rat_mul_alpha hα hK hm, Matrix.det_fin_two_of]
  ring

end FieldModel

/-! ### The ring of integers is `ℤ[ω]`. -/

section RingOfIntegers

variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))

include hα in
/-- `ω` is an algebraic integer. -/
theorem omega_isIntegral : IsIntegral ℤ (omega m α) := by
  unfold omega
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℤ) ∣ (m : ℤ) + 1 := by omega
    refine ⟨X ^ 2 - X + C c, by monicity!, ?_⟩
    have hcK : (c : K) * 4 = (m : K) + 1 := by exact_mod_cast (by linarith : (c : ℤ) * 4 = m + 1)
    simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, algebraMap_int_eq,
      Int.coe_castRingHom]
    linear_combination (1 / 4 : K) * hα + (1 / 4 : K) * hcK
  · exact IsIntegral.of_pow two_pos (hα ▸ (isIntegral_natCast m).neg)

include hα in
/-- `x + yω` is an algebraic integer for `x, y : ℤ`. -/
theorem isIntegral_int_add_int_mul_omega (x y : ℤ) :
    IsIntegral ℤ ((x : K) + (y : K) * omega m α) :=
  (isIntegral_intCast x).add ((isIntegral_intCast y).mul (omega_isIntegral hα))

/-- The key rational lemma: if `m` is squarefree and `m (2b)² ∈ ℤ`, then `2b ∈ ℤ`. -/
lemma exists_int_eq_two_mul_of_sq {m : ℕ} (hm : Squarefree m) {b : ℚ} {k : ℤ}
    (h : (m : ℚ) * (2 * b) ^ 2 = k) : ∃ v : ℤ, (v : ℚ) = 2 * b := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne_zero
  have hint : IsIntegral ℤ ((m : ℚ) * (2 * b)) := by
    refine IsIntegral.of_pow two_pos ?_
    have : ((m : ℚ) * (2 * b)) ^ 2 = ((m * k : ℤ) : ℚ) := by
      push_cast; rw [← h]; ring
    rw [this]; exact isIntegral_intCast _
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at hw
  have hw2 : w ^ 2 = m * k := by
    have : ((w ^ 2 : ℤ) : ℚ) = ((m * k : ℤ) : ℚ) := by
      push_cast; rw [hw]; linear_combination (m : ℚ) * h
    exact_mod_cast this
  have hdvd : (m : ℤ) ∣ w :=
    ((Int.squarefree_natCast.mpr hm).dvd_pow_iff_dvd two_ne_zero).mp ⟨k, hw2⟩
  obtain ⟨v, hv⟩ := hdvd
  refine ⟨v, mul_left_cancel₀ hm0 ?_⟩
  rw [← hw, hv]; push_cast; ring

lemma zmod_four_three (t v : ZMod 4) (h : t ^ 2 + 3 * v ^ 2 = 0) : 2 * (t - v) = 0 := by
  revert t v; decide

lemma zmod_four_one (t v : ZMod 4) (h : t ^ 2 + v ^ 2 = 0) : 2 * t = 0 ∧ 2 * v = 0 := by
  revert t v; decide

lemma zmod_four_two (t v : ZMod 4) (h : t ^ 2 + 2 * v ^ 2 = 0) : 2 * t = 0 ∧ 2 * v = 0 := by
  revert t v; decide

variable (hK : finrank ℚ K = 2) (hm : Squarefree m)

include hα hK hm in
/-- **`𝓞 K = ℤ[ω]`**, the hard direction: every algebraic integer of `K` is `x + yω`
with `x, y : ℤ`. -/
theorem exists_int_add_int_mul_omega_of_isIntegral {x : K} (hx : IsIntegral ℤ x) :
    ∃ u v : ℤ, x = (u : K) + (v : K) * omega m α := by
  have hm0 := hm.ne_zero
  obtain ⟨a, b, rfl⟩ := exists_rat_add_rat_mul_alpha hα hK hm0 x
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := ℚ) hx)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (K := ℚ) hx)
  rw [trace_rat_add_rat_mul_alpha hα hK hm0] at ht
  rw [norm_rat_add_rat_mul_alpha hα hK hm0] at hn
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at ht hn
  obtain ⟨v, hv⟩ := exists_int_eq_two_mul_of_sq hm (b := b) (k := 4 * n - t ^ 2)
    (by push_cast; rw [hn, ht]; ring)
  have h4 : (4 : ℤ) ∣ t ^ 2 + m * v ^ 2 := by
    refine ⟨n, ?_⟩
    have : ((t ^ 2 + m * v ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
      push_cast; rw [hv, ht, hn]; ring
    exact_mod_cast this
  have h4' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr h4
  push_cast at h4'
  have ht' : (t : K) = 2 * (a : K) := by exact_mod_cast congrArg (Rat.cast (K := K)) ht
  have hv' : (v : K) = 2 * (b : K) := by exact_mod_cast congrArg (Rat.cast (K := K)) hv
  unfold omega
  split_ifs with h3
  · have hm4 : ((m : ℕ) : ZMod 4) = 3 := by
      rw [← ZMod.natCast_mod, h3]; rfl
    rw [hm4] at h4'
    have key := zmod_four_three _ _ h4'
    have h2 : (2 : ℤ) ∣ t - v := by
      have : ((2 * (t - v) : ℤ) : ZMod 4) = 0 := by push_cast; exact key
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
      omega
    obtain ⟨u, hu⟩ := h2
    refine ⟨u, v, ?_⟩
    have hu' : (t : K) - (v : K) = 2 * (u : K) := by exact_mod_cast hu
    linear_combination (-1 / 2 : K) * ht' + (-α / 2) * hv' + (1 / 2 : K) * hu'
  · have h12 : m % 4 = 1 ∨ m % 4 = 2 := by have := squarefree_mod_four_ne_zero hm; omega
    have h2 : (2 : ℤ) ∣ t ∧ (2 : ℤ) ∣ v := by
      have key : 2 * (t : ZMod 4) = 0 ∧ 2 * (v : ZMod 4) = 0 := by
        rcases h12 with h1 | h1
        · have hm4 : ((m : ℕ) : ZMod 4) = 1 := by rw [← ZMod.natCast_mod, h1]; rfl
          rw [hm4, one_mul] at h4'
          exact zmod_four_one _ _ h4'
        · have hm4 : ((m : ℕ) : ZMod 4) = 2 := by rw [← ZMod.natCast_mod, h1]; rfl
          rw [hm4] at h4'
          exact zmod_four_two _ _ h4'
      constructor
      · have : ((2 * t : ℤ) : ZMod 4) = 0 := by push_cast; exact key.1
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
        omega
      · have : ((2 * v : ℤ) : ZMod 4) = 0 := by push_cast; exact key.2
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
        omega
    obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := h2
    refine ⟨u, w, ?_⟩
    have hu' : (t : K) = 2 * (u : K) := by exact_mod_cast hu
    have hw' : (v : K) = 2 * (w : K) := by exact_mod_cast hw
    linear_combination (-1 / 2 : K) * ht' + (-α / 2) * hv' + (1 / 2 : K) * hu' + (α / 2) * hw'

include hα hK in
/-- The integer coordinates in `{1, ω}` are unique. -/
theorem int_add_int_mul_omega_inj (hm0 : m ≠ 0) {u v u' v' : ℤ}
    (h : (u : K) + (v : K) * omega m α = (u' : K) + (v' : K) * omega m α) : u = u' ∧ v = v' := by
  unfold omega at h
  split_ifs at h with h3
  · have e : ∀ x y : ℤ, (x : K) + (y : K) * ((1 + α) / 2) =
        (((x : ℚ) + (y : ℚ) / 2 : ℚ) : K) + (((y : ℚ) / 2 : ℚ) : K) * α := by
      intro x y; push_cast; ring
    rw [e, e] at h
    obtain ⟨h1, h2⟩ := rat_add_rat_mul_alpha_inj hα hK hm0 h
    have hv : v = v' := by
      have : (v : ℚ) = v' := by linarith
      exact_mod_cast this
    refine ⟨?_, hv⟩
    have : (u : ℚ) = u' := by rw [hv] at h1; linarith
    exact_mod_cast this
  · have e : ∀ x y : ℤ, (x : K) + (y : K) * α = ((x : ℚ) : K) + ((y : ℚ) : K) * α := by
      intro x y; push_cast; ring
    rw [e, e] at h
    obtain ⟨h1, h2⟩ := rat_add_rat_mul_alpha_inj hα hK hm0 h
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- `ω` as an element of `𝓞 K`. -/
noncomputable def omegaInt : 𝓞 K := ⟨omega m α, omega_isIntegral hα⟩

@[simp] lemma coe_omegaInt : (omegaInt hα : K) = omega m α := rfl

lemma coe_int_add_int_mul_omegaInt (u v : ℤ) :
    (((u : 𝓞 K) + (v : 𝓞 K) * omegaInt hα : 𝓞 K) : K) = (u : K) + (v : K) * omega m α := by
  rw [RingOfIntegers.coe_eq_algebraMap]; simp

include hα hK hm in
/-- Every element of `𝓞 K` is `u + v ω` with `u, v : ℤ`. -/
theorem exists_int_add_int_mul_omegaInt (z : 𝓞 K) :
    ∃ u v : ℤ, z = (u : 𝓞 K) + (v : 𝓞 K) * omegaInt hα := by
  obtain ⟨u, v, h⟩ := exists_int_add_int_mul_omega_of_isIntegral hα hK hm z.isIntegral_coe
  exact ⟨u, v, RingOfIntegers.ext (by rw [coe_int_add_int_mul_omegaInt]; exact h)⟩

include hα hK in
theorem int_add_int_mul_omegaInt_inj (hm0 : m ≠ 0) {u v u' v' : ℤ}
    (h : (u : 𝓞 K) + (v : 𝓞 K) * omegaInt hα = (u' : 𝓞 K) + (v' : 𝓞 K) * omegaInt hα) :
    u = u' ∧ v = v' := by
  apply int_add_int_mul_omega_inj hα hK hm0
  rw [← coe_int_add_int_mul_omegaInt hα, ← coe_int_add_int_mul_omegaInt hα, h]

/-- **The integral basis** `{1, ω}` of `𝓞 K`. -/
noncomputable def intBasis : Basis (Fin 2) ℤ (𝓞 K) :=
  Basis.mk (v := ![1, omegaInt hα])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h : (s : 𝓞 K) + (t : 𝓞 K) * omegaInt hα =
          ((0 : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * omegaInt hα := by
        simpa [zsmul_eq_mul] using hst
      exact int_add_int_mul_omegaInt_inj hα hK hm.ne_zero h)
    (by
      rintro z -
      rw [Submodule.mem_span_range_iff_exists_fun]
      obtain ⟨u, v, huv⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
      refine ⟨![u, v], ?_⟩
      rw [huv, Fin.sum_univ_two]
      simp [zsmul_eq_mul])

@[simp] lemma intBasis_zero : intBasis hα hK hm 0 = 1 := by simp [intBasis]

@[simp] lemma intBasis_one : intBasis hα hK hm 1 = omegaInt hα := by simp [intBasis]

end RingOfIntegers

/-! ### The norm form. -/

section NormForm

variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : finrank ℚ K = 2) (hm0 : m ≠ 0)

include hα hK hm0 in
/-- **The norm form**: `N(x + yω) = Q(x, y)`, `Q` the principal form. -/
theorem norm_int_add_int_mul_omega (x y : ℤ) :
    Algebra.norm ℚ ((x : K) + (y : K) * omega m α) = (principalForm m x y : ℚ) := by
  unfold omega principalForm
  split_ifs with h3
  · have e : (x : K) + (y : K) * ((1 + α) / 2) =
        (((x : ℚ) + (y : ℚ) / 2 : ℚ) : K) + (((y : ℚ) / 2 : ℚ) : K) * α := by push_cast; ring
    rw [e, norm_rat_add_rat_mul_alpha hα hK hm0]
    obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    push_cast
    have hcq : (m : ℚ) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination ((y : ℚ) ^ 2 / 4) * hcq
  · have e : (x : K) + (y : K) * α = ((x : ℚ) : K) + ((y : ℚ) : K) * α := by push_cast; ring
    rw [e, norm_rat_add_rat_mul_alpha hα hK hm0]
    push_cast; ring

include hα hK hm0 in
/-- The trace of `x + yω`: `2x + y` if `m ≡ 3 (mod 4)`, else `2x`. -/
theorem trace_int_add_int_mul_omega (x y : ℤ) :
    Algebra.trace ℚ K ((x : K) + (y : K) * omega m α) =
      if m % 4 = 3 then (2 * x + y : ℚ) else (2 * x : ℚ) := by
  unfold omega
  split_ifs with h3
  · have e : (x : K) + (y : K) * ((1 + α) / 2) =
        (((x : ℚ) + (y : ℚ) / 2 : ℚ) : K) + (((y : ℚ) / 2 : ℚ) : K) * α := by push_cast; ring
    rw [e, trace_rat_add_rat_mul_alpha hα hK hm0]; ring
  · have e : (x : K) + (y : K) * α = ((x : ℚ) : K) + ((y : ℚ) : K) * α := by push_cast; ring
    rw [e, trace_rat_add_rat_mul_alpha hα hK hm0]

include hα hK hm0 in
/-- The norm form on `𝓞 K`: `Algebra.norm ℤ (x + yω) = Q(x, y)`. -/
theorem norm_int_eq_principalForm {z : 𝓞 K} {x y : ℤ}
    (h : z = (x : 𝓞 K) + (y : 𝓞 K) * omegaInt hα) :
    Algebra.norm ℤ z = principalForm m x y := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int, h, coe_int_add_int_mul_omegaInt, norm_int_add_int_mul_omega hα hK hm0]

/-- The principal form is positive semidefinite. -/
theorem principalForm_nonneg (m : ℕ) (x y : ℤ) : 0 ≤ principalForm m x y := by
  unfold principalForm
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    have hc1 : (1 : ℤ) ≤ c := by omega
    nlinarith [sq_nonneg (2 * x + y), sq_nonneg y]
  · positivity

/-- `Q(x, y) = 1` forces `y = 0` and `x = ±1`, for squarefree `m ∉ {1, 3}`. -/
theorem principalForm_eq_one {m : ℕ} (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) {x y : ℤ}
    (h : principalForm m x y = 1) : y = 0 ∧ (x = 1 ∨ x = -1) := by
  have hm0 := hm.ne_zero
  unfold principalForm at h
  split_ifs at h with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc'] at h
    have hm7 : (7 : ℤ) ≤ m := by omega
    have hcz : (m : ℤ) + 1 = 4 * c := by exact_mod_cast hc
    have hy : y = 0 := by
      by_contra hy
      have h1 : 0 < y ^ 2 := by positivity
      have h2 : (1 : ℤ) ≤ y ^ 2 := by omega
      nlinarith [sq_nonneg (2 * x + y)]
    subst hy
    refine ⟨rfl, Int.eq_one_or_neg_one_of_mul_eq_one (v := x) ?_⟩
    nlinarith
  · have hm2 : (2 : ℤ) ≤ m := by omega
    have hy : y = 0 := by
      by_contra hy
      have h1 : 0 < y ^ 2 := by positivity
      have h2 : (1 : ℤ) ≤ y ^ 2 := by omega
      nlinarith
    subst hy
    refine ⟨rfl, Int.eq_one_or_neg_one_of_mul_eq_one (v := x) ?_⟩
    nlinarith

end NormForm

/-! ### The units are `±1`. -/

section Units

variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : finrank ℚ K = 2) (hm : Squarefree m)

include hα hK hm in
/-- **The unit group**: for squarefree `m ∉ {1, 3}`, every unit of `𝓞 K` is `1` or `-1`. -/
theorem coe_unit_eq_one_or_neg_one (hm1 : m ≠ 1) (hm3 : m ≠ 3) (ε : (𝓞 K)ˣ) :
    (ε : 𝓞 K) = 1 ∨ (ε : 𝓞 K) = -1 := by
  obtain ⟨u, v, huv⟩ := exists_int_add_int_mul_omegaInt hα hK hm (ε : 𝓞 K)
  have hN : IsUnit (Algebra.norm ℤ (ε : 𝓞 K)) := ε.isUnit.map (Algebra.norm ℤ)
  rw [norm_int_eq_principalForm hα hK hm.ne_zero huv] at hN
  have hQ : principalForm m u v = 1 := by
    rcases Int.isUnit_iff.mp hN with h | h
    · exact h
    · have := principalForm_nonneg m u v; omega
  obtain ⟨rfl, hu⟩ := principalForm_eq_one hm hm1 hm3 hQ
  rw [huv]
  rcases hu with rfl | rfl
  · left; simp
  · right; simp

include hα hK hm in
/-- Equivalently: the only `x + yω` of norm `1` are `±1`. -/
theorem eq_one_or_neg_one_of_norm_eq_one (hm1 : m ≠ 1) (hm3 : m ≠ 3) {z : 𝓞 K}
    (h : Algebra.norm ℤ z = 1) : z = 1 ∨ z = -1 := by
  obtain ⟨u, v, huv⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
  rw [norm_int_eq_principalForm hα hK hm.ne_zero huv] at h
  obtain ⟨rfl, hu⟩ := principalForm_eq_one hm hm1 hm3 h
  rw [huv]
  rcases hu with rfl | rfl
  · left; simp
  · right; simp

end Units

end CN1.Foundations
