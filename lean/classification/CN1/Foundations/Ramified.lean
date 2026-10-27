import CN1.Foundations.Splitting

/-!
# The ramified primes `p ∣ d`

Pinned environment: Lean v4.34.1, Mathlib d13f23b.

For a prime `p ∣ d = disc m`: `χ_{-d}(p) = 0` (`kroneckerChar_eq_zero_of_dvd_disc`), and `p`
**ramifies**: `minpoly ω = X² + bX + c ≡ (X - r)²` mod `p` (the discriminant `b² - 4c = -d` vanishes
mod `p`), so by Kummer–Dedekind there is exactly one prime over `p`, of inertia degree `1` and
ramification index `2` (`ramified_of_dvd_disc`); in particular it has absolute norm `p`
(`exists_prime_absNorm_eq_of_dvd_disc`). This is the Euler factor input at `p ∣ d` for
`CN1.Epstein.Factorization`.

Mathlib-only.
-/

set_option autoImplicit false

namespace CN1.Foundations

open NumberField Polynomial Ideal

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (p : ℕ) [hp : Fact p.Prime]

/-- `χ_{-d}(p) = 0` for `p ∣ d` (a non-unit of `ZMod d`). -/
theorem kroneckerChar_eq_zero_of_dvd_disc (hpd : p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = 0 :=
  MulChar.map_nonunit _ ((ZMod.isUnit_prime_iff_not_dvd hp.out).not.mpr (not_not.mpr hpd))

/-- The double root of `X² + bX + c` mod `p ∣ d`: `-b/2` for odd `p`, `c` for `p = 2`. -/
noncomputable def doubleRoot (m p : ℕ) : ZMod p :=
  if p = 2 then (cInt m : ZMod p) else -(bInt m : ZMod p) * 2⁻¹

lemma zmod_two_aux₁ : ∀ c : ZMod 2, 2 * c + 0 = 0 := by decide

lemma zmod_two_aux₂ : ∀ c : ZMod 2, c ^ 2 + 0 * c + c = 0 := by decide

lemma two_mul_doubleRoot_add (hpd : p ∣ disc m) :
    2 * doubleRoot m p + (bInt m : ZMod p) = 0 := by
  unfold doubleRoot
  split_ifs with h2
  · subst h2
    have h3 : m % 4 ≠ 3 := fun h3 ↦ by
      rw [disc_of_three_mod_four h3] at hpd; omega
    have hb : bInt m = 0 := by simp [bInt, h3]
    rw [hb, Int.cast_zero]
    exact zmod_two_aux₁ _
  · have hi : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ (two_ne_zero_of_ne_two p h2)
    linear_combination (-(bInt m : ZMod p)) * hi

lemma doubleRoot_isRoot (hpd : p ∣ disc m) :
    doubleRoot m p ^ 2 + (bInt m : ZMod p) * doubleRoot m p + cInt m = 0 := by
  have hdisc : (bInt m : ZMod p) ^ 2 - 4 * (cInt m : ZMod p) = -(disc m : ZMod p) := by
    exact_mod_cast congrArg (Int.cast (R := ZMod p)) (bInt_sq_sub_four_mul_cInt m)
  have hd0 : (disc m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
  unfold doubleRoot
  split_ifs with h2
  · subst h2
    have h3 : m % 4 ≠ 3 := fun h3 ↦ by
      rw [disc_of_three_mod_four h3] at hpd; omega
    have hb : bInt m = 0 := by simp [bInt, h3]
    rw [hb, Int.cast_zero]
    exact zmod_two_aux₂ _
  · have h2' := two_ne_zero_of_ne_two p h2
    have hi : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2'
    have h4 : (4 : ZMod p) ≠ 0 := by
      have : (4 : ZMod p) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2' h2'
    have key : (4 : ZMod p) * ((-(bInt m : ZMod p) * 2⁻¹) ^ 2 +
        (bInt m : ZMod p) * (-(bInt m : ZMod p) * 2⁻¹) + cInt m) = 0 := by
      linear_combination ((bInt m : ZMod p) ^ 2 * (2 * 2⁻¹ + 1)) * hi
        + (-2 * (bInt m : ZMod p) ^ 2) * hi + (-1 : ZMod p) * hdisc + hd0
    exact (mul_eq_zero.mp key).resolve_left h4

include hα hK hm in
/-- For `p ∣ d`, `minpoly ω ≡ (X - r)²` mod `p`. -/
theorem minpoly_omegaInt_map_of_dvd_disc (hpd : p ∣ disc m) :
    (minpoly ℤ (omegaInt hα)).map (Int.castRingHom (ZMod p)) =
      (X - C (doubleRoot m p)) ^ 2 := by
  have hr : -(bInt m : ZMod p) - doubleRoot m p = doubleRoot m p := by
    linear_combination (-1 : ZMod p) * two_mul_doubleRoot_add p hpd
  rw [minpoly_omegaInt_map hα p hm.ne_zero, quad_eq_mul_of_root p _ _ _ (doubleRoot_isRoot p hpd),
    hr, sq]

include hα hK hm in
/-- For `p ∣ d`, the Kummer–Dedekind factor set is `{X - r}`. -/
theorem monicFactorsMod_of_dvd_disc (hpd : p ∣ disc m) :
    RingOfIntegers.monicFactorsMod (omegaInt hα) p = {X - C (doubleRoot m p)} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [minpoly_omegaInt_map_of_dvd_disc hα hK hm p hpd, sq,
    UniqueFactorizationMonoid.normalizedFactors_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    (monic_X_sub_C _).normalize_eq_self, Multiset.singleton_add, Multiset.toFinset_cons,
    Multiset.toFinset_singleton, Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]

include hα hK hm in
/-- **Ramified primes.** For `p ∣ d` there is exactly one prime of `𝓞 K` over `p`, with inertia
degree `1` and ramification index `2`. -/
theorem ramified_of_dvd_disc (hpd : p ∣ disc m) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 ∧ P.ramificationIdx ℤ = 2 := by
  have hF := monicFactorsMod_of_dvd_disc hα hK hm p hpd
  refine ⟨by rw [ncard_primesOver_eq_card_monicFactorsMod hα hK hm p, hF, Finset.card_singleton],
    fun P hP ↦ ?_⟩
  set e := Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p)
  have hmem := (Finset.ext_iff.mp hF _).mp (e ⟨P, hP⟩).2
  rw [Finset.mem_singleton] at hmem
  constructor
  · rw [inertiaDeg_eq_natDegree hα hK hm p hP, hmem, natDegree_X_sub_C]
  · have := Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
      (not_dvd_exponent_omegaInt hα hK hm p) (e ⟨P, hP⟩).2
    rw [Subtype.coe_eta, e.symm_apply_apply, hmem,
      minpoly_omegaInt_map_of_dvd_disc hα hK hm p hpd,
      multiplicity_pow_self (X_sub_C_ne_zero _) (not_isUnit_X_sub_C _)] at this
    exact this

include hα hK hm in
/-- For `p ∣ d`, some prime ideal of `𝓞 K` has absolute norm `p`. -/
theorem exists_prime_absNorm_eq_of_dvd_disc (hpd : p ∣ disc m) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ absNorm P = p := by
  obtain ⟨hcard, hdeg⟩ := ramified_of_dvd_disc hα hK hm p hpd
  obtain ⟨P, hP⟩ := Set.nonempty_of_ncard_ne_zero (s := primesOver (span {(p : ℤ)}) (𝓞 K))
    (by rw [hcard]; norm_num)
  have := hP.1
  have := hP.2
  exact ⟨P, hP.1, by rw [← Ideal.pow_inertiaDeg p P, (hdeg P hP).1, pow_one]⟩

end CN1.Foundations
