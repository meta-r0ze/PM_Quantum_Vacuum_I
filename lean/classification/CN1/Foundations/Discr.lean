import CN1.Foundations.Basic

/-!
# The discriminant of `K = ℚ(√-m)` is `-d`

Pinned environment: Lean v4.34.1, Mathlib d13f23b.

From the integral basis `{1, ω}` (Basic.lean) and the trace formula, `NumberField.discr K = -disc m`
(`discr_eq`): `-m` if `m ≡ 3 (mod 4)`, else `-4m`. This is the input to Mathlib's Minkowski-bound
criteria (`NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`,
`…_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`) that `CN1.Finite.Converse` uses for the nine
fields with class number one.

Mathlib-only.
-/

set_option autoImplicit false

namespace CN1.Foundations

open NumberField Module

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : finrank ℚ K = 2)

include hα hK in
/-- The trace over `ℤ` of `x + yω ∈ 𝓞 K`. -/
theorem trace_int_eq (hm0 : m ≠ 0) {z : 𝓞 K} {x y : ℤ}
    (h : z = (x : 𝓞 K) + (y : 𝓞 K) * omegaInt hα) :
    Algebra.trace ℤ (𝓞 K) z = if m % 4 = 3 then 2 * x + y else 2 * x := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_trace_int, h, coe_int_add_int_mul_omegaInt, trace_int_add_int_mul_omega hα hK hm0]
  split_ifs <;> push_cast <;> ring

include hα in
/-- `ω² = -c + bω` with `(b, c) = (1, (m+1)/4)` if `m ≡ 3 (mod 4)`, else `(0, m)`. -/
theorem omegaInt_sq :
    omegaInt hα ^ 2 = ((if m % 4 = 3 then -(((m + 1) / 4 : ℕ) : ℤ) else -(m : ℤ) : ℤ) : 𝓞 K) +
      ((if m % 4 = 3 then 1 else 0 : ℤ) : 𝓞 K) * omegaInt hα := by
  apply RingOfIntegers.ext
  rw [coe_int_add_int_mul_omegaInt, RingOfIntegers.coe_eq_algebraMap, map_pow,
    ← RingOfIntegers.coe_eq_algebraMap, coe_omegaInt]
  unfold omega
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    push_cast
    have hcK : (m : K) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination (1 / 4 : K) * hα + (-1 / 4 : K) * hcK
  · push_cast
    linear_combination hα

include hα hK in
/-- **The discriminant**: `discr K = -d`, i.e. `-m` if `m ≡ 3 (mod 4)` and `-4m` otherwise. -/
theorem discr_eq (hm : Squarefree m) : NumberField.discr K = -(disc m : ℤ) := by
  have hm0 := hm.ne_zero
  rw [← NumberField.discr_eq_discr K (intBasis hα hK hm), Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, intBasis_zero, intBasis_one,
    one_mul, mul_one]
  have h1 : Algebra.trace ℤ (𝓞 K) (1 : 𝓞 K) = if m % 4 = 3 then 2 * 1 + 0 else 2 * 1 :=
    trace_int_eq hα hK hm0 (x := 1) (y := 0) (by simp)
  have h2 : Algebra.trace ℤ (𝓞 K) (omegaInt hα) = if m % 4 = 3 then 2 * 0 + 1 else 2 * 0 :=
    trace_int_eq hα hK hm0 (x := 0) (y := 1) (by simp)
  have h3 : Algebra.trace ℤ (𝓞 K) (omegaInt hα * omegaInt hα) =
      if m % 4 = 3 then 2 * (if m % 4 = 3 then -(((m + 1) / 4 : ℕ) : ℤ) else -(m : ℤ)) +
        (if m % 4 = 3 then 1 else 0) else
        2 * (if m % 4 = 3 then -(((m + 1) / 4 : ℕ) : ℤ) else -(m : ℤ)) :=
    trace_int_eq hα hK hm0 (by rw [← sq, omegaInt_sq hα])
  rw [h1, h2, h3]
  unfold disc
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    have : (m : ℤ) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination this
  · push_cast; ring

end CN1.Foundations
