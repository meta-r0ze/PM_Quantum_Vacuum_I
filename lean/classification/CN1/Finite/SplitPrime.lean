import Mathlib
import CN1.Finite.Params
import CN1.Finite.Elementary

/-!
# CN1.Finite.SplitPrime: a small prime with a degree-one prime above it forces `h ≠ 1`

Step 6 of the argument (Rabinowitsch). Let `𝓞 K = ℤ[θ]` with `minpoly θ = X² - t·X + c`, norm form
`N(x + y·θ) = x² + t·x·y + c·y²`, and `d = 4c - t²`. If `p` is a prime with
`y² - t·y + c ≡ 0 (mod p)` for some integer `y`, then by Kummer–Dedekind
(`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`, Mathlib) the ideal `P = (p, θ - y)` is a
prime of residue degree one, so `absNorm P = p`. If `𝓞 K` were a PID, `P = (β)` and
`|N(β)| = p`, i.e. `Q(x, y) = p` for some integers, which `CN1.Finite.not_form_eq_prime` rules out
when `4p ≤ d` and `p ≠ c`. Hence `classNumber K ≠ 1`.

The hypothesis `p ≠ c` is what makes this the *split* (or at least non-`d/4`) case: for `t = 0`
the ramified prime `p = c = d/4` IS represented, `Q(0, 1) = c` (as for `d = 8`, `m = 2`). For a split
prime `χ(p) = 1` we have `p ∤ d`, hence `p ≠ c`. The hypotheses are weaker than "split": any
degree-one prime below the bound other than `d/4` works (with the per-case
bound). A split witness gives `y` with `y² - t·y + c ≡ 0` because the discriminant
`t² - 4c = -d` is a square mod `p`.

The algebraic input (`QuadInt`: `θ`, `ℤ[θ] = 𝓞 K`, the minimal polynomial and the norm form) is a
structure of hypotheses here; `CN1.Finite.Bridge` supplies it from `CN1.Foundations`.
-/

open NumberField Ideal Module Polynomial

namespace CN1.Finite

variable {K : Type*} [Field K] [NumberField K]

/-- The algebraic data of a quadratic ring of integers `𝓞 K = ℤ[θ]`, `θ² = t·θ - c`.
This is the interface to `CN1.Foundations`; every field is a hypothesis here. -/
structure QuadInt (K : Type*) [Field K] [NumberField K] (t c : ℤ) where
  /-- a generator of the ring of integers -/
  θ : 𝓞 K
  /-- `𝓞 K = ℤ[θ]`; equivalently `RingOfIntegers.exponent θ = 1` -/
  adjoin_eq_top : Algebra.adjoin ℤ {θ} = ⊤
  /-- the minimal polynomial of `θ` over `ℤ` -/
  minpoly_eq : minpoly ℤ θ = X ^ 2 - C t * X + C c
  /-- the norm form -/
  norm_eq : ∀ x y : ℤ, Algebra.norm ℤ ((x : 𝓞 K) + (y : 𝓞 K) * θ) = x ^ 2 + t * x * y + c * y ^ 2

/-- Every element of `𝓞 K = ℤ[θ]` with `deg (minpoly θ) = 2` is `x + y·θ`, `x, y ∈ ℤ`. -/
theorem QuadInt.exists_eq_add_mul {t c : ℤ} (D : QuadInt K t c) (β : 𝓞 K) :
    ∃ x y : ℤ, β = (x : 𝓞 K) + (y : 𝓞 K) * D.θ := by
  have hβmem : β ∈ Algebra.adjoin ℤ {D.θ} := by rw [D.adjoin_eq_top]; exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hβmem
  obtain ⟨f, hf⟩ := hβmem
  set g := minpoly ℤ D.θ with hg
  have hgm : g.Monic := minpoly.monic D.θ.isIntegral
  have h2 : g.natDegree = 2 := by rw [hg, D.minpoly_eq]; compute_degree!
  have hg1 : g ≠ 1 := by intro h; rw [h] at h2; simp at h2
  have hdeg : (f %ₘ g).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt f hgm hg1
    omega
  obtain ⟨a, b, hr⟩ : ∃ a b : ℤ, f %ₘ g = C b * X + C a :=
    ⟨_, _, eq_X_add_C_of_natDegree_le_one hdeg⟩
  refine ⟨a, b, ?_⟩
  change (aeval D.θ) f = β at hf
  have hg0 : aeval D.θ g = 0 := by rw [hg]; exact minpoly.aeval ℤ D.θ
  rw [← hf]
  conv_lhs => rw [← modByMonic_add_div f g]
  rw [map_add, map_mul, hg0, zero_mul, add_zero, hr]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  simp only [algebraMap_int_eq, eq_intCast]
  ring

/-- **The finite-part lemma.** If `y² - t·y + c ≡ 0 (mod p)`, `4p ≤ d = 4c - t²` and `p ≠ c`,
then `classNumber K ≠ 1`. -/
theorem classNumber_ne_one_of_witness {t c : ℤ} (D : QuadInt K t c) (ht : t = 0 ∨ t = 1)
    (p : ℕ) (hp : p.Prime) (y : ℤ) (hy : (p : ℤ) ∣ y ^ 2 - t * y + c)
    (hb : 4 * (p : ℤ) ≤ 4 * c - t ^ 2) (hpc : (p : ℤ) ≠ c) : classNumber K ≠ 1 := by
  intro h1
  haveI := Fact.mk hp
  haveI hpid : IsPrincipalIdealRing (𝓞 K) := classNumber_eq_one_iff.mp h1
  -- Kummer–Dedekind applies: `p ∤ exponent θ = 1`
  have hexp : ¬ p ∣ RingOfIntegers.exponent D.θ := by
    rw [RingOfIntegers.exponent_eq_one_iff.mpr D.adjoin_eq_top]
    exact hp.not_dvd_one
  have hmap0 : (minpoly ℤ D.θ).map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic D.θ.isIntegral)
  -- `X - y` is a monic irreducible factor of `minpoly θ` mod `p`
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
  -- the corresponding prime `P` has residue degree one, so `absNorm P = p`
  set P : Ideal (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩ : Ideal (𝓞 K)) with hPdef
  have hPmem : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩).prop
  haveI hPprime : P.IsPrime := hPmem.1
  haveI hPlies : P.LiesOver (span {(p : ℤ)}) := hPmem.2
  have hdeg1 : P.inertiaDeg ℤ = 1 := by
    rw [hPdef, Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hexp hQ,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, natDegree_X_sub_C]
  have hPnorm : absNorm P = p := by rw [← Ideal.pow_inertiaDeg p P, hdeg1, pow_one]
  -- in a PID, `P = (β)` with `|N β| = p`, and `β = x + y·θ`
  obtain ⟨β, hβ⟩ := Submodule.IsPrincipal.principal P
  rw [hβ, Ideal.submodule_span_eq, absNorm_span_singleton] at hPnorm
  obtain ⟨x, y', hxy⟩ := D.exists_eq_add_mul β
  rw [hxy, D.norm_eq] at hPnorm
  have hd0 : 0 ≤ 4 * c - t ^ 2 := by
    have : (0 : ℤ) ≤ p := by positivity
    linarith
  have hQnn := form_nonneg hd0 x y'
  have hform : x ^ 2 + t * x * y' + c * y' ^ 2 = p := by
    rcases Int.natAbs_eq_iff.mp hPnorm with h | h
    · exact h
    · have : (0 : ℤ) < p := by exact_mod_cast hp.pos
      linarith
  exact not_form_eq_prime ht hp hb hpc x y' hform

/-! ## The witness predicate for the 190 instances (pure `ℕ`, `decide`-able) -/

/-- `IsWitness m p y`: `p` is prime, `p ∣ y² - t·y + c` (written without truncated subtraction
issues), `4p ≤ d`, and `p ≠ c`, with `t, c, d` the principal-form data of the radicand `m`. -/
def IsWitness (m p y : ℕ) : Prop :=
  p.Prime ∧ tOf m * y ≤ y ^ 2 + cOf m ∧ p ∣ y ^ 2 + cOf m - tOf m * y ∧ 4 * p ≤ dOf m ∧
    p ≠ cOf m

theorem classNumber_ne_one_of_isWitness {m p y : ℕ} (D : QuadInt K (tOf m) (cOf m))
    (hw : IsWitness m p y) : classNumber K ≠ 1 := by
  obtain ⟨hp, hle, hdvd, hb, hpc⟩ := hw
  have h4 : (4 * cOf m : ℤ) = dOf m + (tOf m : ℤ) ^ 2 := by exact_mod_cast four_mul_cOf m
  have hb' : (4 * p : ℤ) ≤ dOf m := by exact_mod_cast hb
  refine classNumber_ne_one_of_witness D ?_ p hp y ?_ (by linarith) (by exact_mod_cast hpc)
  · rcases tOf_eq_zero_or_one m with h | h <;> simp [h]
  · have := Int.natCast_dvd_natCast.mpr hdvd
    rw [Nat.cast_sub hle] at this
    push_cast at this
    convert this using 1
    ring

/-- `Squarefree m` implies no `k² ∣ m` for `2 ≤ k ≤ 26` (`26² = 676 > 652`). -/
def SqfBelow (m : ℕ) : Prop := ∀ k ∈ Finset.Icc 2 26, ¬ k * k ∣ m

instance : DecidablePred SqfBelow := fun m =>
  inferInstanceAs (Decidable (∀ k ∈ Finset.Icc 2 26, ¬ k * k ∣ m))

theorem sqfBelow_of_squarefree {m : ℕ} (hm : Squarefree m) : SqfBelow m := by
  intro k hk h
  have := Nat.isUnit_iff.mp (hm k h)
  rw [Finset.mem_Icc] at hk
  omega

end CN1.Finite
