import ELEM.Hypotheses
import CN1.Finite.Bridge

/-!
# ELEM.Glue: the class number one theorem from the hypotheses of `ELEM.Hypotheses`

The top-level assembly, in the pattern of CN-1's `disc_le_652_of_CS`: the challenge statement
`CN1.classNumber_eq_one_iff` (CN1Challenges/ClassNumberOne.lean) is proved with the eight
statements of `ELEM.Hypotheses` as explicit arguments.

Both halves are over the same quantity `q = |disc K| = dOf m` (CN-1's `dOf`), and the two ranges
`q < 2^15` and `q ≥ 2^15` come from one `lt_or_ge`:

* **finite side** (`classNumber_ne_one_of_lt`): `m ≢ 3 (mod 4)` and `m ≡ 7 (mod 8)` are excluded by
  the prime `2` (ramified, resp. split), uniformly; `m ≡ 3 (mod 8)` by `ELEM.Sieve`. Each case is an
  instance of CN-1's `classNumber_ne_one_of_isWitness`.
* **analytic side** (`analyticSetting_of_classNumber_eq_one`, `false_of_analyticSetting`): from
  `classNumber K = 1` and `q ≥ 2^15`, CN-1's witness lemma and the Kummer–Dedekind representation give
  `AnalyticSetting q`; then Lemma 3, the minor, (11), (14), Lemma 2, (8) and the decomposition
  `A(R) = I + S₊(R) + (log q)/q` feed `ELEM.Endpoint`.
-/

set_option autoImplicit false

open NumberField Module Polynomial Ideal CN1.Finite CN1.Foundations

namespace ELEM

/-! ## Roots mod `p` and `IsInert` -/

/-- A root of `y² - y + c` mod `p`, as an integer, rules out inertness. -/
theorem not_isInert_of_dvd {c p : ℕ} {y : ℤ} (hy : (p : ℤ) ∣ y ^ 2 - y + c) : ¬ IsInert c p := by
  intro h
  apply h (y : ZMod p)
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hy
  push_cast at this
  linear_combination this

/-- A non-inert prime has an integer root of `y² - y + c` mod `p`. -/
theorem exists_dvd_of_not_isInert {c p : ℕ} (hp : p.Prime) (h : ¬ IsInert c p) :
    ∃ y : ℤ, (p : ℤ) ∣ y ^ 2 - y + c := by
  have : NeZero p := ⟨hp.ne_zero⟩
  simp only [IsInert, not_forall, not_not] at h
  obtain ⟨r, hr⟩ := h
  refine ⟨(r.val : ℤ), (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  linear_combination hr

/-- An odd prime `p ∣ q`, `q ≡ 3 (mod 4)`, is not inert for `c = (q+1)/4` (it ramifies): `y = (p+1)/2`
is a root, since `4 (y² - y + c) = p² + q`. -/
theorem not_isInert_of_dvd_q {p q : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) (hq : q % 4 = 3)
    (hpq : p ∣ q) : ¬ IsInert (cq q) p := by
  set y : ℤ := (((p + 1) / 2 : ℕ) : ℤ) with hy
  have h2 : 2 * y = p + 1 := by
    have : 2 * ((p + 1) / 2) = p + 1 := by omega
    rw [hy]; exact_mod_cast this
  have h4 : 4 * (cq q : ℤ) = q + 1 := by
    have : 4 * cq q = q + 1 := by unfold cq; omega
    exact_mod_cast this
  have hid : 4 * (y ^ 2 - y + cq q) = (p : ℤ) ^ 2 + q := by
    linear_combination (2 * y + (p : ℤ) + 1) * h2 - 2 * h2 + h4
  have hdvd4 : (p : ℤ) ∣ 4 * (y ^ 2 - y + cq q) := by
    rw [hid]
    exact dvd_add (dvd_pow_self _ two_ne_zero) (Int.natCast_dvd_natCast.mpr hpq)
  have hcop : IsCoprime (p : ℤ) 4 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime p 4 := by
      have h2' : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
      simpa using Nat.Coprime.pow_right 2 h2'
    simpa [Int.gcd] using this
  exact not_isInert_of_dvd (hcop.dvd_of_dvd_mul_left hdvd4)

/-! ## The representation of a degree-one prime in a PID (Kummer–Dedekind)

This is the first half of CN-1's `classNumber_ne_one_of_witness` (CN1/Finite/SplitPrime.lean),
stopped before the contradiction: in a PID, a prime with a root of the minimal polynomial mod `p` is
a value of the norm form. -/

variable {K : Type*} [Field K] [NumberField K]

theorem exists_form_eq_of_root {t c : ℤ} (D : QuadInt K t c) (hd0 : 0 ≤ 4 * c - t ^ 2)
    (p : ℕ) (hp : p.Prime) (y : ℤ) (hy : (p : ℤ) ∣ y ^ 2 - t * y + c) (h1 : classNumber K = 1) :
    ∃ x y' : ℤ, x ^ 2 + t * x * y' + c * y' ^ 2 = p := by
  have := Fact.mk hp
  have hpid : IsPrincipalIdealRing (𝓞 K) := classNumber_eq_one_iff.mp h1
  have hexp : ¬ p ∣ RingOfIntegers.exponent D.θ := by
    rw [RingOfIntegers.exponent_eq_one_iff.mpr D.adjoin_eq_top]
    exact hp.not_dvd_one
  have hmap0 : (minpoly ℤ D.θ).map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic D.θ.isIntegral)
  have hQ : (X - C y).map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod D.θ p := by
    rw [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset,
      Polynomial.mem_normalizedFactors_iff hmap0, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, ?_⟩
    rw [dvd_iff_isRoot, D.minpoly_eq]
    have hy' : ((y ^ 2 - t * y + c : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hy
    simp only [IsRoot.def, eval_map, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_C]
    simp only [eq_intCast]
    push_cast at hy'
    linear_combination hy'
  set P : Ideal (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩ : Ideal (𝓞 K)) with hPdef
  have hPmem : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩).prop
  have hPprime : P.IsPrime := hPmem.1
  have hPlies : P.LiesOver (span {(p : ℤ)}) := hPmem.2
  have hdeg1 : P.inertiaDeg ℤ = 1 := by
    rw [hPdef, Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hexp hQ,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, natDegree_X_sub_C]
  have hPnorm : absNorm P = p := by rw [← Ideal.pow_inertiaDeg p P, hdeg1, pow_one]
  obtain ⟨β, hβ⟩ := Submodule.IsPrincipal.principal P
  rw [hβ, Ideal.submodule_span_eq, absNorm_span_singleton] at hPnorm
  obtain ⟨x, y', hxy⟩ := D.exists_eq_add_mul β
  rw [hxy, D.norm_eq] at hPnorm
  have hQnn := form_nonneg hd0 x y'
  refine ⟨x, y', ?_⟩
  rcases Int.natAbs_eq_iff.mp hPnorm with h | h
  · exact h
  · have : (0 : ℤ) < p := by exact_mod_cast hp.pos
    linarith

/-! ## The prime `2` -/

/-- `m ≢ 3 (mod 4)`, `m ≥ 3`: `2` ramifies (`d = 4m`), witness `y = m mod 2`. -/
theorem isWitness_two_of_not_mod_four {m : ℕ} (h : m % 4 ≠ 3) (h3 : 3 ≤ m) :
    IsWitness m 2 (m % 2) := by
  simp only [IsWitness, tOf, cOf, dOf, h, ite_false, zero_mul, Nat.sub_zero]
  refine ⟨Nat.prime_two, Nat.zero_le _, ?_, by omega, by omega⟩
  rcases Nat.mod_two_eq_zero_or_one m with h2 | h2 <;> rw [h2] <;> omega

/-- `m ≡ 7 (mod 8)`, `m ≥ 15`: `2` splits (`c = (m+1)/4` even), witness `y = 0`. -/
theorem isWitness_two_of_mod_eight {m : ℕ} (h : m % 8 = 7) (h15 : 15 ≤ m) : IsWitness m 2 0 := by
  have h4 : m % 4 = 3 := by omega
  simp only [IsWitness, tOf, cOf, dOf, h4, ite_true]
  refine ⟨Nat.prime_two, by simp, ?_, by omega, by omega⟩
  simp only [mul_zero, Nat.sub_zero]
  omega

/-! ## The finite side: `q < 2^15` -/

theorem classNumber_ne_one_of_lt (hS : Sieve) (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hd : dOf m < 32768)
    (hnine : m ∉ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)) : classNumber K ≠ 1 := by
  obtain ⟨α, hα⟩ := hsq
  have D := quadIntOfFoundations hK hm hα
  have hm0 : m ≠ 0 := hm.ne_zero
  have hm1 : m ≠ 1 := fun h => hnine (by simp [h])
  have hm2 : m ≠ 2 := fun h => hnine (by simp [h])
  have hm3 : m ≠ 3 := fun h => hnine (by simp [h])
  have hm7 : m ≠ 7 := fun h => hnine (by simp [h])
  by_cases h4 : m % 4 = 3
  · by_cases h8 : m % 8 = 7
    · exact classNumber_ne_one_of_isWitness D (isWitness_two_of_mod_eight h8 (by omega))
    · -- `m ≡ 3 (mod 8)`, `m = 8k + 3`, `11 ≤ m < 2^15`: the residue sieve
      have h83 : m % 8 = 3 := by omega
      have hdm : dOf m = m := dOf_of_mod m h4
      have hk : m / 8 < 4096 := by omega
      have hmk : 8 * (m / 8) + 3 = m := by omega
      rcases hS (m / 8) hk (by omega) with hmem | ⟨p, hpL, hp4, y, hyp, hroot⟩
      · exact absurd (by rw [hmk] at hmem; simp at hmem ⊢; omega) hnine
      · rw [hmk] at hp4 hroot
        have hp : p.Prime := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpL
          rcases hpL with h | h | h | h | h | h | h | h | h | h <;> subst h <;> norm_num
        have hp1 : 1 ≤ p := hp.one_lt.le
        have hyy : y ≤ y ^ 2 := by
          rcases Nat.eq_zero_or_pos y with h0 | h0
          · simp [h0]
          · calc y = y ^ 1 := (pow_one y).symm
              _ ≤ y ^ 2 := Nat.pow_le_pow_right h0 (by norm_num)
        have hpy : y ≤ p * y := Nat.le_mul_of_pos_left y hp1
        have hsub : (p - 1) * y = p * y - y := by rw [Nat.sub_one_mul]
        have hc : cOf m = (m + 1) / 4 := by simp [cOf, h4]
        have ht : tOf m = 1 := tOf_of_mod m h4
        refine classNumber_ne_one_of_isWitness D (p := p) (y := y) ⟨hp, ?_, ?_, ?_, ?_⟩
        · rw [ht, one_mul]; omega
        · rw [ht, one_mul, hc]
          have hdvd : p ∣ y ^ 2 + (p - 1) * y + (m + 1) / 4 := Nat.dvd_of_mod_eq_zero hroot
          have hdvd' := Nat.dvd_sub hdvd (Dvd.intro y rfl : p ∣ p * y)
          rw [hsub] at hdvd'
          generalize y ^ 2 = Y2 at hdvd' hyy ⊢
          generalize p * y = PY at hdvd' hpy ⊢
          have : Y2 + (PY - y) + (m + 1) / 4 - PY = Y2 + (m + 1) / 4 - y := by omega
          rwa [this] at hdvd'
        · rw [hdm]; omega
        · rw [hc]; omega
  · exact classNumber_ne_one_of_isWitness D (isWitness_two_of_not_mod_four h4 (by omega))

/-! ## The analytic side: `q ≥ 2^15` -/

/-- **From `h = 1` to the analytic setting.** If `classNumber K = 1` and `dOf m ≥ 2^15`, then
`AnalyticSetting (dOf m)`, and `cq (dOf m) = cOf m`. -/
theorem analyticSetting_of_classNumber_eq_one (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hge : 32768 ≤ dOf m) (h1 : classNumber K = 1) :
    AnalyticSetting (dOf m) := by
  obtain ⟨α, hα⟩ := hsq
  have D := quadIntOfFoundations hK hm hα
  -- `m ≡ 3 (mod 4)`: otherwise `2` ramifies
  have h4 : m % 4 = 3 := by
    by_contra h4
    have : 3 ≤ m := by simp only [dOf, h4, ite_false] at hge; omega
    exact classNumber_ne_one_of_isWitness D (isWitness_two_of_not_mod_four h4 this) h1
  have hdm : dOf m = m := dOf_of_mod m h4
  rw [hdm] at hge ⊢
  -- `m ≡ 3 (mod 8)`: otherwise `2` splits
  have h8 : m % 8 = 3 := by
    by_contra h8
    exact classNumber_ne_one_of_isWitness D (isWitness_two_of_mod_eight (by omega) (by omega)) h1
  have ht : (tOf m : ℤ) = 1 := by rw [tOf_of_mod m h4]; rfl
  have hc : (cOf m : ℤ) = (cq m : ℤ) := by simp [cOf, cq, h4]
  have h4c : 4 * (cq m : ℤ) = m + 1 := by
    have : 4 * cq m = m + 1 := by unfold cq; omega
    exact_mod_cast this
  -- (1): a non-inert prime `p` with `4p < m` contradicts `h = 1`
  have hinert : ∀ p : ℕ, p.Prime → 4 * p < m → IsInert (cq m) p := by
    intro p hp hp4
    by_contra hni
    obtain ⟨y, hy⟩ := exists_dvd_of_not_isInert hp hni
    refine classNumber_ne_one_of_witness D (tOf_eq_zero_or_one m |>.imp
      (fun h => by exact_mod_cast h) (fun h => by exact_mod_cast h)) p hp y ?_ ?_ ?_ h1
    · rw [ht, hc]; simpa using hy
    · rw [ht, hc, h4c]; push_cast; omega
    · rw [hc]
      have : p < cq m := by unfold cq; omega
      exact_mod_cast this.ne
  refine ⟨hge, ?_, h8, hinert, ?_⟩
  · -- `m` is prime: a proper least prime factor `p` has `p² ≤ m`, hence `4p < m`, and ramifies
    by_contra hnp
    have hm1 : m ≠ 1 := by omega
    have hpp : (Nat.minFac m).Prime := Nat.minFac_prime hm1
    have hsq' : Nat.minFac m ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
    have hp2 : Nat.minFac m % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h | h
      · have : 2 ∣ m := h ▸ Nat.minFac_dvd m
        omega
      · exact h
    have hp4 : 4 * Nat.minFac m < m := by
      have := hpp.two_le
      nlinarith
    exact not_isInert_of_dvd_q hpp hp2 h4 (Nat.minFac_dvd m) (hinert _ hpp hp4)
  · -- every non-inert prime is a norm
    intro p hp hni
    obtain ⟨y, hy⟩ := exists_dvd_of_not_isInert hp hni
    have hd0 : 0 ≤ 4 * (cOf m : ℤ) - (tOf m : ℤ) ^ 2 := by rw [ht, hc, h4c]; push_cast; omega
    obtain ⟨x, y', hxy⟩ := exists_form_eq_of_root D hd0 p hp y (by rw [ht, hc]; simpa using hy) h1
    exact ⟨x, y', by rw [ht, hc] at hxy; linear_combination hxy⟩

/-- The decomposition `A(R) = I + S₊(R) + (log q)/q` for prime `q ≤ R`, `q ≡ 3 (mod 4)`: the primes
`p ≤ R` are inert, split, or `p = q` (which is not inert). -/
theorem A_eq_decomp {q R : ℕ} (hq : q.Prime) (hq4 : q % 4 = 3) (hqR : q ≤ R) :
    A R = Iinert q R + Splus q R + Real.log q / q := by
  classical
  have hq2 : q % 2 = 1 := by omega
  have hqni : ¬ IsInert (cq q) q := not_isInert_of_dvd_q hq hq2 hq4 dvd_rfl
  unfold A Iinert Splus
  rw [Nat.floor_natCast]
  set P := Nat.primesLE R
  set g : ℕ → ℝ := fun p => Real.log p / p
  rw [← Finset.sum_filter_add_sum_filter_not P (fun p => IsInert (cq q) p) g,
    ← Finset.sum_filter_add_sum_filter_not (P.filter fun p => ¬ IsInert (cq q) p) (fun p => p ≠ q) g]
  have hs : (P.filter fun p => ¬ IsInert (cq q) p).filter (fun p => p ≠ q) =
      P.filter (fun p => IsSplit q p) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, IsSplit, and_assoc]
  have hr : (P.filter fun p => ¬ IsInert (cq q) p).filter (fun p => ¬ p ≠ q) = {q} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton, ne_eq, not_not]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨⟨by simp [P, Nat.primesLE, Nat.primesBelow, hq]; omega, hqni⟩, rfl⟩
  rw [hs, hr, Finset.sum_singleton, add_assoc]

theorem Splus_nonneg (q : ℕ) (X : ℝ) : 0 ≤ Splus q X := by
  unfold Splus
  exact Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- **The analytic contradiction.** No `q` satisfies `AnalyticSetting q`, given the statements of the
analytic steps. -/
theorem false_of_analyticSetting (hA : LemmaTwoA) (h8 : SplitBound) (hL3 : AuxPrime)
    (hNV : Nonvanishing) (h11 : SizeBound) (h14 : DivisibilityBound) (hE : Endpoint)
    {q : ℕ} (hset : AnalyticSetting q) : False := by
  obtain ⟨R, hRp, hRi, hR4, hR5⟩ := hL3 q hset
  obtain ⟨f, hf⟩ := hNV q R hset hRp hRi hR4 hR5
  have hY1 := h11 q R hset hRp hRi hR4 hR5 f hf
  have hY2 := h14 q R hset hRp hRi hR4 hR5 f hf
  have hq0 : 32768 ≤ q := hset.large
  have hqq4 : q ≤ q ^ 4 := Nat.le_self_pow (by norm_num) q
  have hRbig : 156 ≤ R := by omega
  have hqR : q ≤ R := by omega
  have hAR := hA R (by omega)
  have hSp := h8 q hset (R : ℝ) (by
    have : (q : ℝ) ≤ R := by exact_mod_cast hqR
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith)
  have hdec := A_eq_decomp hset.prime (by have := hset.mod_eight; omega) hqR
  have hS13 : (R : ℝ) / 13 ≤ (Sof R : ℝ) := by
    have : R ≤ 13 * Sof R := by unfold Sof; omega
    have : (R : ℝ) ≤ 13 * (Sof R : ℝ) := by exact_mod_cast this
    linarith
  have hS0 : (0 : ℝ) < (Sof R : ℝ) := by
    have : 0 < Sof R := by unfold Sof; omega
    exact_mod_cast this
  exact hE q R (Sof R) (A R) (Iinert q R) (Splus q R)
    (Real.log (Delta q R f) / ((R : ℝ) ^ 2 * Sof R))
    (by exact_mod_cast hq0) (by exact_mod_cast hR4) (by exact_mod_cast hR5) hS13 hS0
    (Splus_nonneg q R) hdec hAR.1 hAR.2 hSp hY1 hY2

/-- Unused; not in the closure of `CN1.classNumber_eq_one_iff`. **The analytic bound.** `classNumber K = 1` implies `dOf m < 2^15`. -/
theorem dOf_lt_of_classNumber_eq_one (hA : LemmaTwoA) (h8 : SplitBound) (hL3 : AuxPrime)
    (hNV : Nonvanishing) (h11 : SizeBound) (h14 : DivisibilityBound) (hE : Endpoint)
    (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (h1 : classNumber K = 1) : dOf m < 32768 := by
  by_contra hge
  exact false_of_analyticSetting hA h8 hL3 hNV h11 h14 hE
    (analyticSetting_of_classNumber_eq_one hK hm hsq (by omega) h1)

/-! ## The assembly -/

/-- **The class number one theorem, from the eight statements.** This is the statement of the
Comparator challenge `CN1.classNumber_eq_one_iff` (CN1Challenges/ClassNumberOne.lean, md5 c162eee6)
with the eight statements of `ELEM.Hypotheses` as explicit arguments. The two ranges of
`q = dOf m` come from one `lt_or_ge` at `2^15`. -/
theorem classNumber_eq_one_iff_of_hyps (hA : LemmaTwoA) (h8 : SplitBound) (hL3 : AuxPrime)
    (hNV : Nonvanishing) (h11 : SizeBound) (h14 : DivisibilityBound) (hE : Endpoint)
    (hS : Sieve)
    (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ) := by
  refine ⟨fun h1 => ?_, classNumber_eq_one_of_foundations hK hm hsq⟩
  by_contra hnine
  rcases lt_or_ge (dOf m) 32768 with hlt | hge
  · exact classNumber_ne_one_of_lt hS hK hm hsq hlt hnine h1
  · exact false_of_analyticSetting hA h8 hL3 hNV h11 h14 hE
      (analyticSetting_of_classNumber_eq_one hK hm hsq hge h1)

end ELEM
