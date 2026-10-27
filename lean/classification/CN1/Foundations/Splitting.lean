import CN1.Foundations.Character

/-!
# The splitting of rational primes in `K = ℚ(√-m)` and the character `χ_{-d}`

Pinned environment: Lean v4.34.1, Mathlib d13f23b.

With `θ = ω ∈ 𝓞 K` and `𝓞 K = ℤ[ω]` (Basic.lean), the exponent of `θ` is `1`
(`exponent_omegaInt_eq_one`), so Mathlib's Kummer–Dedekind criterion
(`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`) applies at **every** prime `p`: the primes
of `𝓞 K` over `p` correspond to the monic irreducible factors of `minpoly ℤ ω` modulo `p`, with
inertia degree the degree of the factor. Here `minpoly ℤ ω = X² + bX + c` with
`(b, c) = (-1, (m+1)/4)` if `m ≡ 3 (mod 4)` and `(0, m)` otherwise (`minpoly_int_omegaInt`), and
`b² - 4c = -d` (`bInt_sq_sub_four_mul_cInt`).

For a prime `p ∤ d` we show (`kroneckerChar_eq_one_iff_exists_root`) that `χ_{-d}(p) = 1` iff
`X² + bX + c` has a root mod `p`, and then:

* if `χ(p) = 1`, `p` **splits**: exactly two primes over `p`, both of inertia degree `1`
  (`ncard_primesOver_eq_two_of_kroneckerChar_eq_one`), so there is a prime of norm `p`
  (`exists_prime_absNorm_eq_of_kroneckerChar_eq_one`, the input to the Rabinowitsch step in
  `CN1.Finite`);
* if `χ(p) = -1`, `p` is **inert**: one prime over `p`, of inertia degree `2`
  (`ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one`).

The ramified primes `p ∣ d` (`χ(p) = 0`) are treated in `Ramified.lean`.

Mathlib-only.
-/

set_option autoImplicit false

namespace CN1.Foundations

open NumberField Polynomial Ideal

/-! ### The coefficients of `minpoly ω = X² + bX + c`. -/

/-- The linear coefficient `b` of `minpoly ω`: `-1` if `m ≡ 3 (mod 4)`, else `0`. -/
def bInt (m : ℕ) : ℤ := if m % 4 = 3 then -1 else 0

/-- The constant coefficient `c` of `minpoly ω`: `(m+1)/4` if `m ≡ 3 (mod 4)`, else `m`. -/
def cInt (m : ℕ) : ℤ := if m % 4 = 3 then ((m + 1) / 4 : ℕ) else m

/-- The discriminant of `X² + bX + c` is `-d`. -/
theorem bInt_sq_sub_four_mul_cInt (m : ℕ) : bInt m ^ 2 - 4 * cInt m = -(disc m : ℤ) := by
  unfold bInt cInt disc
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    have : (m : ℤ) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination this
  · push_cast; ring

section Setup

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : Module.finrank ℚ K = 2) (hm : Squarefree m)

/-! ### `ℤ[ω] = 𝓞 K`, so the exponent of `ω` is `1`. -/

include hα hK hm in
theorem adjoin_omegaInt_eq_top : Algebra.adjoin ℤ {omegaInt hα} = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
  exact Subalgebra.add_mem _ (Subalgebra.intCast_mem _ u)
    (Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ v) (Algebra.self_mem_adjoin_singleton ℤ _))

include hα hK hm in
/-- The Kummer–Dedekind exponent of `ω` is `1`: the criterion applies at every prime. -/
theorem exponent_omegaInt_eq_one : RingOfIntegers.exponent (omegaInt hα) = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr (adjoin_omegaInt_eq_top hα hK hm)

include hα hK hm in
theorem not_dvd_exponent_omegaInt (p : ℕ) [hp : Fact p.Prime] :
    ¬ p ∣ RingOfIntegers.exponent (omegaInt hα) := by
  rw [exponent_omegaInt_eq_one hα hK hm]; exact hp.out.not_dvd_one

/-! ### The minimal polynomial of `ω`. -/

include hα in
/-- `minpoly ℚ ω = X² + bX + c`. -/
theorem minpoly_rat_omega (hm0 : m ≠ 0) :
    minpoly ℚ (omega m α) = X ^ 2 + C (bInt m : ℚ) * X + C (cInt m : ℚ) := by
  have hmpos : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply irreducible_of_degree_le_three_of_not_isRoot
    · have hdeg : (X ^ 2 + C (bInt m : ℚ) * X + C (cInt m : ℚ)).natDegree = 2 := by
        compute_degree!
      rw [hdeg]; decide
    · intro x hx
      rw [IsRoot.def, eval_add, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_C] at hx
      unfold bInt cInt at hx
      split_ifs at hx with h3
      · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
        have hc' : ((m + 1) / 4 : ℕ) = c := by omega
        rw [hc'] at hx
        push_cast at hx
        have hcq : (m : ℚ) + 1 = 4 * c := by exact_mod_cast hc
        nlinarith [sq_nonneg (2 * x - 1)]
      · push_cast at hx
        nlinarith [sq_nonneg x]
  · rw [map_add, map_add, map_mul, map_pow, aeval_X, aeval_C, aeval_C, eq_ratCast, eq_ratCast]
    unfold omega bInt cInt
    split_ifs with h3
    · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
      have hc' : ((m + 1) / 4 : ℕ) = c := by omega
      rw [hc']
      push_cast
      have hcK : (m : K) + 1 = 4 * c := by exact_mod_cast hc
      linear_combination (1 / 4 : K) * hα + (-1 / 4 : K) * hcK
    · push_cast
      linear_combination hα
  · monicity!

include hα in
/-- **`minpoly ℤ ω = X² + bX + c`** with `(b, c) = (-1, (m+1)/4)` or `(0, m)`. -/
theorem minpoly_int_omegaInt (hm0 : m ≠ 0) :
    minpoly ℤ (omegaInt hα) = X ^ 2 + C (bInt m) * X + C (cInt m) := by
  rw [← RingOfIntegers.minpoly_coe, coe_omegaInt]
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← algebraMap_int_eq, ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (omega_isIntegral hα),
    minpoly_rat_omega hα hm0]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

include hα hK in
/-- The same, in case-split shape: `X² - X + (m+1)/4` if `m ≡ 3 (mod 4)`, else `X² + m`. `hK` is
unused and kept for the argument order. -/
theorem minpoly_omegaInt (hm0 : m ≠ 0) :
    minpoly ℤ (omegaInt hα) =
      if m % 4 = 3 then X ^ 2 - X + C (((m + 1) / 4 : ℕ) : ℤ) else X ^ 2 + C (m : ℤ) := by
  rw [minpoly_int_omegaInt hα hm0]
  unfold bInt cInt
  split_ifs <;> simp <;> ring

/-! ### Reduction mod `p` and the Kummer–Dedekind factor set. -/

section Prime

variable (p : ℕ) [hp : Fact p.Prime]

include hα in
theorem minpoly_omegaInt_map (hm0 : m ≠ 0) :
    (minpoly ℤ (omegaInt hα)).map (Int.castRingHom (ZMod p)) =
      X ^ 2 + C (bInt m : ZMod p) * X + C (cInt m : ZMod p) := by
  rw [minpoly_int_omegaInt hα hm0]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

/-- A monic quadratic with a root `r` factors as `(X - r)(X - (-b - r))`. -/
lemma quad_eq_mul_of_root (b c r : ZMod p) (hr : r ^ 2 + b * r + c = 0) :
    X ^ 2 + C b * X + C c = (X - C r) * (X - C (-b - r)) := by
  have hc : c = -(r ^ 2) - b * r := by linear_combination hr
  rw [hc]
  simp only [map_sub, map_neg, map_mul, map_pow]
  ring

lemma natDegree_quad (b c : ZMod p) : (X ^ 2 + C b * X + C c).natDegree = 2 := by
  compute_degree!

lemma monic_quad (b c : ZMod p) : (X ^ 2 + C b * X + C c).Monic := by
  monicity!

/-- A monic quadratic without roots is irreducible. -/
lemma irreducible_quad_of_no_root (b c : ZMod p) (h : ∀ x : ZMod p, x ^ 2 + b * x + c ≠ 0) :
    Irreducible (X ^ 2 + C b * X + C c) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_quad]; decide
  · intro x hx
    apply h x
    rw [IsRoot.def, eval_add, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_C] at hx
    exact hx

include hα hK hm in
/-- If `X² + bX + c` has a root `r` mod `p`, the Kummer–Dedekind factor set is
`{X - r, X - (-b - r)}`. -/
theorem monicFactorsMod_of_root {r : ZMod p} (hr : r ^ 2 + (bInt m : ZMod p) * r + cInt m = 0) :
    RingOfIntegers.monicFactorsMod (omegaInt hα) p =
      {X - C r, X - C (-(bInt m : ZMod p) - r)} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [minpoly_omegaInt_map hα p hm.ne_zero, quad_eq_mul_of_root p _ _ r hr,
    UniqueFactorizationMonoid.normalizedFactors_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    (monic_X_sub_C _).normalize_eq_self, (monic_X_sub_C _).normalize_eq_self,
    Multiset.singleton_add, Multiset.toFinset_cons, Multiset.toFinset_singleton]

include hα hK hm in
/-- If `X² + bX + c` has no root mod `p`, the Kummer–Dedekind factor set is `{X² + bX + c}`. -/
theorem monicFactorsMod_of_no_root
    (h : ∀ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m ≠ 0) :
    RingOfIntegers.monicFactorsMod (omegaInt hα) p =
      {X ^ 2 + C (bInt m : ZMod p) * X + C (cInt m : ZMod p)} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [minpoly_omegaInt_map hα p hm.ne_zero,
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_quad_of_no_root p _ _ h),
    (monic_quad p _ _).normalize_eq_self, Multiset.toFinset_singleton]

include hα hK hm in
/-- The number of primes over `p` is the number of monic irreducible factors of `minpoly ω`
mod `p` (Kummer–Dedekind). -/
theorem ncard_primesOver_eq_card_monicFactorsMod :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard =
      (RingOfIntegers.monicFactorsMod (omegaInt hα) p).card := by
  rw [← Nat.card_coe_set_eq,
    Nat.card_congr (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p)),
    Nat.card_eq_finsetCard]

include hα hK hm in
/-- The inertia degree of a prime over `p` is the degree of its Kummer–Dedekind factor. -/
theorem inertiaDeg_eq_natDegree {P : Ideal (𝓞 K)} (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) :
    P.inertiaDeg ℤ =
      ((Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p) ⟨P, hP⟩ :
        (ZMod p)[X])).natDegree := by
  set e := Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p)
  have := Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (not_dvd_exponent_omegaInt hα hK hm p) (e ⟨P, hP⟩).2
  rwa [Subtype.coe_eta, e.symm_apply_apply] at this

/-! ### `p ∤ d`: the root criterion matches `χ_{-d}(p)`. -/

/-- The two roots `r` and `-b - r` are distinct when `p ∤ d`. -/
lemma root_ne_other_root (hpd : ¬ p ∣ disc m) {r : ZMod p}
    (hr : r ^ 2 + (bInt m : ZMod p) * r + cInt m = 0) : r ≠ -(bInt m : ZMod p) - r := by
  intro heq
  apply hpd
  rw [← ZMod.natCast_eq_zero_iff]
  have hdisc : (bInt m : ZMod p) ^ 2 - 4 * (cInt m : ZMod p) = -(disc m : ZMod p) := by
    exact_mod_cast congrArg (Int.cast (R := ZMod p)) (bInt_sq_sub_four_mul_cInt m)
  linear_combination hdisc + (-(2 * r + (bInt m : ZMod p))) * heq + 4 * hr

lemma two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

/-- For an odd prime `p`, `X² + bX + c` has a root mod `p` iff `-m` is a square mod `p`. -/
theorem exists_root_iff_isSquare (hp2 : p ≠ 2) :
    (∃ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m = 0) ↔ IsSquare (-(m : ZMod p)) := by
  have h2 := two_ne_zero_of_ne_two p hp2
  unfold bInt cInt
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    push_cast
    have hc4 : (m : ZMod p) + 1 = 4 * c := by
      have := congrArg (Nat.cast (R := ZMod p)) hc
      push_cast at this
      exact this
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨2 * x - 1, by linear_combination (-4 : ZMod p) * hx + (-1 : ZMod p) * hc4⟩
    · rintro ⟨y, hy⟩
      refine ⟨(y + 1) * 2⁻¹, ?_⟩
      have hi : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      have h4 : (4 : ZMod p) ≠ 0 := by
        have : (4 : ZMod p) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      have key : (4 : ZMod p) * (((y + 1) * 2⁻¹) ^ 2 + -1 * ((y + 1) * 2⁻¹) + c) = 0 := by
        linear_combination ((y + 1) ^ 2 * (2 * 2⁻¹ + 1)) * hi + (-2 * (y + 1)) * hi
          + (-1 : ZMod p) * hy + (-1 : ZMod p) * hc4
      exact (mul_eq_zero.mp key).resolve_left h4
  · push_cast
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by linear_combination -hx⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by linear_combination -hy⟩

/-- For `p = 2` (so `m ≡ 3 (mod 4)`), `X² + bX + c` has a root mod `2` iff `m ≡ 7 (mod 8)`. -/
theorem exists_root_two_iff (h3 : m % 4 = 3) :
    (∃ x : ZMod 2, x ^ 2 + (bInt m : ZMod 2) * x + cInt m = 0) ↔ m % 8 = 7 := by
  unfold bInt cInt
  rw [if_pos h3, if_pos h3]
  obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
  have hc' : ((m + 1) / 4 : ℕ) = c := by omega
  rw [hc']
  have key : ∀ c' : ZMod 2, (∃ x : ZMod 2, x ^ 2 + ((-1 : ℤ) : ZMod 2) * x + ((c' : ZMod 2)) = 0) ↔
      c' = 0 := by decide
  rw [show ((c : ℤ) : ZMod 2) = ((c : ℕ) : ZMod 2) from Int.cast_natCast c, key,
    ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  omega

include hm in
/-- **The root criterion**: for a prime `p ∤ d`, `χ_{-d}(p) = 1` iff `minpoly ω` has a root mod `p`
(iff `p` splits, see below). -/
theorem kroneckerChar_eq_one_iff_exists_root (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = 1 ↔
      ∃ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m = 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h3 : m % 4 = 3 := by
      by_contra h3
      exact hpd (by rw [disc_of_not_three_mod_four h3]; exact ⟨2 * m, by ring⟩)
    rw [exists_root_two_iff h3, show ((2 : ℕ) : ZMod (disc m)) = 2 from Nat.cast_ofNat,
      kroneckerChar_apply_two h3, ZMod.χ₈_nat_eq_if_mod_eight]
    have h8 : m % 8 = 3 ∨ m % 8 = 7 := by omega
    rcases h8 with h | h
    · rw [if_neg (by omega), if_neg (by omega)]
      norm_num
      omega
    · rw [if_neg (by omega), if_pos (by omega)]
      norm_num
      exact h
  · rw [kroneckerChar_apply_prime_eq_one_iff hm hp2 hpd, exists_root_iff_isSquare p hp2]

/-- For a prime `p ∤ d`, `χ_{-d}(p) = ±1`. -/
theorem kroneckerChar_eq_one_or_neg_one (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = 1 ∨ kroneckerChar m (p : ZMod (disc m)) = -1 := by
  have hcop : IsCoprime (p : ℤ) (disc m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpd)
  have hne : kroneckerChar m (p : ZMod (disc m)) ≠ 0 := by
    rw [← Int.cast_natCast (R := ZMod (disc m))]
    exact (DirichletCharacter.apply_ne_zero_iff _ _).mpr hcop
  rcases kroneckerChar_isQuadratic m (p : ZMod (disc m)) with h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr h

/-! ### The splitting theorems. -/

include hα hK hm in
/-- **Split primes.** If `p ∤ d` and `χ_{-d}(p) = 1`, there are exactly two primes of `𝓞 K` over
`p`, each of inertia degree `1`. -/
theorem ncard_primesOver_eq_two_of_kroneckerChar_eq_one (hpd : ¬ p ∣ disc m)
    (h1 : kroneckerChar m (p : ZMod (disc m)) = 1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 := by
  obtain ⟨r, hr⟩ := (kroneckerChar_eq_one_iff_exists_root hm p hpd).mp h1
  have hF := monicFactorsMod_of_root hα hK hm p hr
  have hne : X - C r ≠ X - C (-(bInt m : ZMod p) - r) := by
    intro h
    exact root_ne_other_root p hpd hr (C_inj.mp (sub_right_injective h))
  constructor
  · rw [ncard_primesOver_eq_card_monicFactorsMod hα hK hm p, hF]
    exact Finset.card_pair_eq_two_iff.mpr hne
  · intro P hP
    rw [inertiaDeg_eq_natDegree hα hK hm p hP]
    have hmem := (Finset.ext_iff.mp hF _).mp
      (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p) ⟨P, hP⟩).2
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h <;> rw [h, natDegree_X_sub_C]

include hα hK hm in
/-- **Inert primes.** If `p ∤ d` and `χ_{-d}(p) = -1`, there is exactly one prime of `𝓞 K` over
`p`, of inertia degree `2`. -/
theorem ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one (hpd : ¬ p ∣ disc m)
    (h1 : kroneckerChar m (p : ZMod (disc m)) = -1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 := by
  have hno : ∀ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m ≠ 0 := by
    intro x hx
    have := (kroneckerChar_eq_one_iff_exists_root hm p hpd).mpr ⟨x, hx⟩
    rw [h1] at this
    norm_num at this
  have hF := monicFactorsMod_of_no_root hα hK hm p hno
  constructor
  · rw [ncard_primesOver_eq_card_monicFactorsMod hα hK hm p, hF, Finset.card_singleton]
  · intro P hP
    rw [inertiaDeg_eq_natDegree hα hK hm p hP]
    have hmem := (Finset.ext_iff.mp hF _).mp
      (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p) ⟨P, hP⟩).2
    rw [Finset.mem_singleton] at hmem
    rw [hmem, natDegree_quad]

include hα hK hm in
theorem ncard_primesOver_eq_two_iff (hpd : ¬ p ∣ disc m) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ↔ kroneckerChar m (p : ZMod (disc m)) = 1 := by
  rcases kroneckerChar_eq_one_or_neg_one p hpd with h | h
  · simp only [h, iff_true]
    exact (ncard_primesOver_eq_two_of_kroneckerChar_eq_one hα hK hm p hpd h).1
  · rw [h, (ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one hα hK hm p hpd h).1]
    norm_num

include hα hK hm in
theorem ncard_primesOver_eq_one_iff (hpd : ¬ p ∣ disc m) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 ↔ kroneckerChar m (p : ZMod (disc m)) = -1 := by
  rcases kroneckerChar_eq_one_or_neg_one p hpd with h | h
  · rw [h, (ncard_primesOver_eq_two_of_kroneckerChar_eq_one hα hK hm p hpd h).1]
    norm_num
  · simp only [h, iff_true]
    exact (ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one hα hK hm p hpd h).1

include hα hK hm in
/-- **A prime of norm `p`.** If `p ∤ d` and `χ_{-d}(p) = 1`, some prime ideal of `𝓞 K` has absolute
norm `p`. (If `𝓞 K` were a PID this prime would be `(x + yω)` with `Q(x, y) = p`; that is the
Rabinowitsch step in `CN1.Finite`.) -/
theorem exists_prime_absNorm_eq_of_kroneckerChar_eq_one (hpd : ¬ p ∣ disc m)
    (h1 : kroneckerChar m (p : ZMod (disc m)) = 1) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ absNorm P = p := by
  obtain ⟨hcard, hdeg⟩ := ncard_primesOver_eq_two_of_kroneckerChar_eq_one hα hK hm p hpd h1
  obtain ⟨P, hP⟩ := Set.nonempty_of_ncard_ne_zero (s := primesOver (span {(p : ℤ)}) (𝓞 K))
    (by rw [hcard]; norm_num)
  have := hP.1
  have := hP.2
  refine ⟨P, hP.1, ?_⟩
  rw [← Ideal.pow_inertiaDeg p P, hdeg P hP, pow_one]

end Prime

end Setup

end CN1.Foundations
