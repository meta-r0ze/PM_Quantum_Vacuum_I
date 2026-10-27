import Mathlib
import CN1.Finite.Params

/-!
# CN1.Finite.Converse: the nine fields have class number one

For `K` quadratic with a root of `-m`, `m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}`, and
`|disc K| ≤ d = dOf m`, we prove `classNumber K = 1` via Mathlib's Minkowski criterion
`RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime` (ClassNumber.lean:116):
every nonzero prime `P` of norm `≤ M K` must be principal.

* `M K = (4/π)^{r₂}·(2!/2²)·√|disc K| ≤ (2/3)·√d` (using only `r₂ ≤ 1`, `π > 3`).
* For a maximal `P` of `𝓞 K` (degree 2) with residue characteristic `q`: `absNorm P = q`, or
  `absNorm P = q²` and `P = (q)` (`absNorm_maximal_cases`). The second case is principal.
* `absNorm P = q` is impossible when `θ² = t·θ - c` has no root mod `q`, because `𝓞 K/P ≅ ZMod q`
  (`not_absNorm_eq_of_no_root`); the finitely many `(m, q)` pairs are checked by `decide`.

For `m ≡ 3 (mod 4)` the element `θ = (1 + √-m)/2` is constructed here (`exists_theta`); its
integrality needs no knowledge of `𝓞 K`. The hypothesis `|disc K| ≤ dOf m` is the only
input from `CN1.Foundations` (discharged by `discr_eq` in `CN1.Finite.Bridge`).
-/

open NumberField NumberField.InfinitePlace Ideal Module Real Nat

namespace CN1.Finite

variable {K : Type*} [Field K] [NumberField K]

/-- The Minkowski bound of a quadratic field with `|disc K| ≤ d` is at most `(2/3)·√d`.
The left side is written exactly as Mathlib's local notation `M K` expands. -/
theorem le_two_thirds_sqrt_of_le_minkowski (hK : finrank ℚ K = 2) {d : ℕ}
    (hdisc : |discr K| ≤ (d : ℤ)) {N : ℕ}
    (hle : (N : ℝ) ≤ (4 / π) ^ nrComplexPlaces K *
      ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|(discr K : ℝ)|)) :
    (N : ℝ) ≤ 2 / 3 * √(d : ℝ) := by
  have hr2 : nrComplexPlaces K ≤ 1 := by
    have := card_add_two_mul_card_eq_rank K
    omega
  have h1 : (1 : ℝ) ≤ 4 / π := by
    rw [le_div_iff₀ pi_pos]; linarith [pi_le_four]
  have hpi : (4 / π : ℝ) ≤ 4 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) pi_gt_three.le
  have hpow : (4 / π : ℝ) ^ nrComplexPlaces K ≤ 4 / 3 :=
    (pow_le_pow_right₀ h1 hr2).trans (by rw [pow_one]; exact hpi)
  have hsqrt : √|(discr K : ℝ)| ≤ √(d : ℝ) := by
    apply Real.sqrt_le_sqrt
    rw [← Int.cast_abs]
    exact_mod_cast hdisc
  have hM : (4 / π : ℝ) ^ nrComplexPlaces K *
      ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|(discr K : ℝ)|) ≤ 2 / 3 * √(d : ℝ) := by
    rw [hK]
    have key := mul_le_mul hpow hsqrt (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 4 / 3)
    norm_num [Nat.factorial]
    nlinarith [key]
  exact hle.trans hM

/-- From `N ≤ (2/3)·√d` and `4d < 9B²` conclude `N < B`. -/
theorem nat_lt_of_le_two_thirds_sqrt {N d B : ℕ} (hN : (N : ℝ) ≤ 2 / 3 * √(d : ℝ))
    (hB : 4 * d < 9 * B ^ 2) : N < B := by
  have hB0 : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp at hB
    · exact h
  have hB0' : (0 : ℝ) < 3 * B / 2 := by positivity
  have hs : √(d : ℝ) < 3 * B / 2 := by
    rw [Real.sqrt_lt' hB0']
    have : (4 * d : ℝ) < 9 * (B : ℝ) ^ 2 := by exact_mod_cast hB
    nlinarith
  have : (N : ℝ) < B := by nlinarith
  exact_mod_cast this

/-- In a quadratic field, a maximal ideal `P` with residue characteristic `q` has `absNorm P = q`,
or `absNorm P = q²` and `P = (q)`. -/
theorem absNorm_maximal_cases (hK : finrank ℚ K = 2) (P : Ideal (𝓞 K)) [hP : P.IsMaximal] :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ P ∧
      (absNorm P = q ∨ (absNorm P = q ^ 2 ∧ P = span {(q : 𝓞 K)})) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  obtain ⟨q, hq⟩ := CharP.exists (𝓞 K ⧸ P)
  obtain ⟨n, hqprime, hcard⟩ := FiniteField.card (𝓞 K ⧸ P) q
  have hN : absNorm P = q ^ (n : ℕ) := by
    rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  have hqmem : (q : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ q
  have hle : span {(q : 𝓞 K)} ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqmem)
  have hspan : absNorm (span {(q : 𝓞 K)}) = q ^ 2 := by
    rw [absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap,
      RingOfIntegers.rank, hK, Int.natAbs_pow, Int.natAbs_natCast]
  have hdvd := absNorm_dvd_absNorm_of_le hle
  rw [hN, hspan, Nat.pow_dvd_pow_iff_le_right hqprime.one_lt] at hdvd
  refine ⟨q, hqprime, hqmem, ?_⟩
  rcases (show (n : ℕ) = 1 ∨ (n : ℕ) = 2 by have := n.pos; omega) with h | h
  · left; rw [hN, h, pow_one]
  · right
    refine ⟨by rw [hN, h], ?_⟩
    obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
    have hmul := congrArg absNorm hC
    rw [map_mul, hspan, hN, h] at hmul
    have hC1 : absNorm C = 1 := by
      have hq0 : 0 < q ^ 2 := pow_pos hqprime.pos 2
      have : q ^ 2 * absNorm C = q ^ 2 * 1 := by rw [mul_one]; exact hmul.symm
      exact Nat.eq_of_mul_eq_mul_left hq0 this
    rw [absNorm_eq_one_iff] at hC1
    rw [hC, hC1, mul_top]

/-- If `θ ∈ 𝓞 K` satisfies `θ² = t·θ - c` and the polynomial `z² - t·z + c` has no root in
`ZMod q`, then no maximal ideal of `𝓞 K` has norm `q` (such an ideal would have residue field
`ZMod q` containing the image of `θ`). -/
theorem not_absNorm_eq_of_no_root (θ : 𝓞 K) (t c : ℤ)
    (hθ : θ ^ 2 = (t : 𝓞 K) * θ - (c : 𝓞 K))
    (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (q : ℕ) (hq : q.Prime) (hN : absNorm P = q)
    (hroot : ∀ z : ZMod q, z ^ 2 - (t : ZMod q) * z + (c : ZMod q) ≠ 0) : False := by
  haveI := Fact.mk hq
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ P) = q := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← absNorm_apply, hN]
  haveI : CharP (𝓞 K ⧸ P) q := charP_of_card_eq_prime hcard
  let f : ZMod q →+* 𝓞 K ⧸ P := ZMod.castHom dvd_rfl _
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by rw [ZMod.card, hcard]⟩
  obtain ⟨z, hz⟩ := hf.2 (Ideal.Quotient.mk P θ)
  apply hroot z
  apply f.injective
  have hθ' := congrArg (Ideal.Quotient.mk P) hθ
  simp only [map_pow, map_sub, map_mul, map_intCast] at hθ'
  rw [map_add, map_sub, map_mul, map_pow, map_zero, hz, map_intCast, map_intCast, hθ']
  ring

/-- For `m ≡ 3 (mod 4)`, the element `θ = (1 + α)/2 ∈ 𝓞 K` satisfies `θ² = t·θ - c` with
`t = tOf m = 1`, `c = cOf m = (m+1)/4`. Its integrality is proved directly from the monic
polynomial `X² - X + c`, with no knowledge of `𝓞 K`. -/
theorem exists_theta {m : ℕ} (hm3 : m % 4 = 3) (α : K) (hα : α ^ 2 = -(m : K)) :
    ∃ θ : 𝓞 K, θ ^ 2 = ((tOf m : ℤ) : 𝓞 K) * θ - ((cOf m : ℤ) : 𝓞 K) := by
  have ht : tOf m = 1 := tOf_of_mod m hm3
  have hc : 4 * cOf m = m + 1 := four_mul_cOf_of_mod m hm3
  have hcK : (4 : K) * (cOf m : K) = (m : K) + 1 := by exact_mod_cast hc
  set ω : K := (1 + α) / 2 with hω
  have hω2 : ω ^ 2 = ω - (cOf m : K) := by
    have key : (4 : K) * ω ^ 2 = 4 * (ω - (cOf m : K)) := by
      simp only [hω]
      linear_combination hα + hcK
    exact mul_left_cancel₀ (by norm_num : (4 : K) ≠ 0) key
  have hint : IsIntegral ℤ ω := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (cOf m : ℤ), by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast]
    rw [hω2]; ring
  refine ⟨IsIntegralClosure.mk' (𝓞 K) ω hint, ?_⟩
  apply IsIntegralClosure.algebraMap_injective (𝓞 K) ℤ K
  simp only [map_pow, map_sub, map_mul, map_intCast, IsIntegralClosure.algebraMap_mk']
  rw [ht]
  push_cast
  rw [hω2]; ring

/-- **The converse direction.** A quadratic field containing `√-m` for one of the nine radicands,
with `|disc K| ≤ dOf m`, has class number one. -/
theorem classNumber_eq_one_of_mem_nine (hK : finrank ℚ K = 2) (m : ℕ)
    (hm : m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ))
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hdisc : |discr K| ≤ (dOf m : ℤ)) :
    classNumber K = 1 := by
  obtain ⟨α, hα⟩ := hsq
  rw [classNumber_eq_one_iff]
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    fun I hI hle ↦ ?_
  have hI0 : (I : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  haveI hmax : (I : Ideal (𝓞 K)).IsMaximal := hI.isMaximal hI0
  have hbound := le_two_thirds_sqrt_of_le_minkowski hK hdisc hle
  obtain ⟨q, hq, -, hcase⟩ := absNorm_maximal_cases hK (I : Ideal (𝓞 K))
  rcases hcase with hN | ⟨-, hspan⟩
  · exfalso
    rw [hN] at hbound
    have h2 := hq.two_le
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have := nat_lt_of_le_two_thirds_sqrt hbound (B := 2) (by norm_num [dOf]); omega
    · have := nat_lt_of_le_two_thirds_sqrt hbound (B := 2) (by norm_num [dOf]); omega
    · have := nat_lt_of_le_two_thirds_sqrt hbound (B := 2) (by norm_num [dOf]); omega
    · have := nat_lt_of_le_two_thirds_sqrt hbound (B := 2) (by norm_num [dOf]); omega
    · obtain ⟨θ, hθ⟩ := exists_theta (by norm_num) α hα
      have := nat_lt_of_le_two_thirds_sqrt hbound (B := 3) (by norm_num [dOf])
      interval_cases q <;>
        first
        | exact not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN (by decide)
        | norm_num at hq
    · obtain ⟨θ, hθ⟩ := exists_theta (by norm_num) α hα
      have := nat_lt_of_le_two_thirds_sqrt hbound (B := 3) (by norm_num [dOf])
      interval_cases q <;>
        first
        | exact not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN (by decide)
        | norm_num at hq
    · obtain ⟨θ, hθ⟩ := exists_theta (by norm_num) α hα
      have := nat_lt_of_le_two_thirds_sqrt hbound (B := 5) (by norm_num [dOf])
      interval_cases q <;>
        first
        | exact not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN (by decide)
        | norm_num at hq
    · obtain ⟨θ, hθ⟩ := exists_theta (by norm_num) α hα
      have := nat_lt_of_le_two_thirds_sqrt hbound (B := 6) (by norm_num [dOf])
      interval_cases q <;>
        first
        | exact not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN (by decide)
        | norm_num at hq
    · obtain ⟨θ, hθ⟩ := exists_theta (by norm_num) α hα
      have := nat_lt_of_le_two_thirds_sqrt hbound (B := 9) (by norm_num [dOf])
      interval_cases q <;>
        first
        | exact not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN (by decide)
        | norm_num at hq
  · rw [hspan]
    exact ⟨⟨_, rfl⟩⟩

end CN1.Finite
