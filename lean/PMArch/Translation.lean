import PMArch.ThetaE8

/-!
# Exact translations of the lattice postulates

The lattice postulates are characterized by conditions stated directly in terms of the state
sum `θ(τ) = ∑_{z} exp(π i τ Q(z))` of an integral positive-definite lattice.

* `even_iff_T_invariant`: Postulate E (all norms even) holds iff `θ` is invariant under
  `τ ↦ τ + 1`.
-/

noncomputable section
open Complex Matrix ModularForm Function
open UpperHalfPlane hiding I
open scoped Real

namespace PMArch.Translation
open PMArch.RankEight PMArch.ThetaE8

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

/-- The norm of an integral vector as a natural number. -/
def qn (z : Fin n → ℤ) : ℕ := (z ⬝ᵥ (A *ᵥ z)).toNat

variable {A}

lemma norm_nonneg' (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) (z : Fin n → ℤ) :
    0 ≤ z ⬝ᵥ (A *ᵥ z) := by
  have := qf_nonneg hpos (vcast z)
  rw [qf_cast] at this
  exact_mod_cast this

lemma norm_eq_qn (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) (z : Fin n → ℤ) :
    z ⬝ᵥ (A *ᵥ z) = (qn A z : ℤ) := by
  simp [qn, Int.toNat_of_nonneg (norm_nonneg' hpos z)]

lemma thetaH_vadd_two (τ : ℍ) : thetaH A ((2 : ℝ) +ᵥ τ) = thetaH A τ := by
  simp only [thetaH, Function.comp_apply, thetaFun, theta, coe_vadd]
  refine tsum_congr fun z => ?_
  rw [qf_cast]
  push_cast
  have : -(π : ℂ) * (-I * (2 + (τ : ℂ))) * (z ⬝ᵥ (A *ᵥ z) : ℤ)
      = -π * (-I * τ) * (z ⬝ᵥ (A *ᵥ z) : ℤ) + (z ⬝ᵥ (A *ᵥ z) : ℤ) * (2 * π * I) := by ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma qParam_two_vadd_one (τ : ℍ) :
    Periodic.qParam 2 ((1 : ℝ) +ᵥ τ : ℍ) = -Periodic.qParam 2 τ := by
  simp only [Periodic.qParam, coe_vadd]
  have : 2 * (π : ℂ) * I * ((1 : ℝ) + (τ : ℂ)) / (2 : ℝ) = π * I + 2 * π * I * τ / 2 := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_pi_mul_I]
  push_cast; ring

lemma hasSum_q2 (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) (τ : ℍ) :
    HasSum (fun m : ℕ => (Nat.card (qn A ⁻¹' {m}) : ℂ) • Periodic.qParam 2 τ ^ m)
      (thetaH A τ) := by
  set G := A.map (Int.cast : ℤ → ℝ)
  have hterm : ∀ z : Fin n → ℤ, cexp (-π * (-I * (τ : ℂ)) * (qf G (vcast z) : ℂ))
      = Periodic.qParam 2 τ ^ qn A z := by
    intro z
    rw [qf_cast, norm_eq_qn hpos z, Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring_nf
  have hsum : Summable (fun z : Fin n → ℤ =>
      cexp (-π * (-I * (τ : ℂ)) * (qf G (vcast z) : ℂ))) := by
    refine Summable.of_norm ?_
    simp only [norm_theta_term, UpperHalfPlane.coe_im]
    simpa only [sub_zero] using summable_qf G hpos (mul_pos Real.pi_pos τ.im_pos) 0
  have h := hsum.hasSum.tsum_fiberwise (qn A)
  simp only [hterm] at h
  have hθ : thetaH A τ = ∑' z : Fin n → ℤ, Periodic.qParam 2 (τ : ℂ) ^ qn A z := by
    simp only [thetaH, Function.comp_apply, thetaFun, theta]
    exact tsum_congr hterm
  rw [hθ]
  convert h using 2 with m
  have hc : ∀ b : qn A ⁻¹' {m},
      Periodic.qParam 2 (τ : ℂ) ^ qn A b = Periodic.qParam 2 τ ^ m :=
    fun b => by rw [show qn A b = m from b.2]
  rw [tsum_congr hc, tsum_const, nsmul_eq_mul, smul_eq_mul]

lemma fiber_finite (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) (m : ℕ) :
    (qn A ⁻¹' {m}).Finite := by
  set G := A.map (Int.cast : ℤ → ℝ)
  by_contra hinf
  have hinf' : Infinite (qn A ⁻¹' {m}) := Set.infinite_coe_iff.mpr hinf
  have hsum : Summable (fun z : Fin n → ℤ => Real.exp (-(π * 1) * qf G (vcast z))) := by
    simpa only [sub_zero] using summable_qf G hpos (mul_pos Real.pi_pos one_pos) 0
  have hsub := hsum.comp_injective (Subtype.val_injective (p := fun z => z ∈ qn A ⁻¹' {m}))
  have hconst : (fun z : qn A ⁻¹' {m} => Real.exp (-(π * 1) * qf G (vcast z.1)))
      = fun _ => Real.exp (-(π * 1) * m) := by
    funext z
    rw [qf_cast, norm_eq_qn hpos, show qn A z.1 = m from z.2]
    norm_cast
  have h2 : Summable (fun _ : qn A ⁻¹' {m} => Real.exp (-(π * 1) * m)) := by
    rw [← hconst]; exact hsub
  rw [summable_const_iff] at h2
  exact (Real.exp_pos _).ne' h2

/-- **Postulate E as an invariance property.** For an integral positive-definite lattice, all
norms are even iff the theta series is invariant under `τ ↦ τ + 1` (equivalently
`s ↦ s - i` with `s = -iτ`). -/
theorem even_iff_T_invariant (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) :
    (∀ z : Fin n → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) ↔
      ∀ s : ℂ, 0 < s.re → theta (A.map (Int.cast : ℤ → ℝ)) (s - I)
        = theta (A.map (Int.cast : ℤ → ℝ)) s := by
  constructor
  · intro he s _
    exact theta_shift A he s
  · intro hT z
    have hper : Periodic (thetaH A ∘ ofComplex) 2 :=
      UpperHalfPlane.periodic_comp_ofComplex (fun τ => thetaH_vadd_two τ)
    have han := analyticAt_cuspFunction_zero two_pos hper (mdiff_thetaH A hpos)
      (isBoundedAtImInfty_thetaH A hpos)
    have hshift : ∀ τ : ℍ, thetaH A ((1 : ℝ) +ᵥ τ) = thetaH A τ := by
      intro τ
      simp only [thetaH, Function.comp_apply, thetaFun, coe_vadd]
      have := hT (-I * (τ : ℂ)) (by simpa using τ.im_pos)
      rw [← this]
      congr 1
      push_cast; ring
    have hs2 : ∀ τ : ℍ, HasSum (fun m : ℕ =>
        ((-1) ^ m * (Nat.card (qn A ⁻¹' {m}) : ℂ)) • Periodic.qParam 2 τ ^ m) (thetaH A τ) := by
      intro τ
      have h := hasSum_q2 hpos ((1 : ℝ) +ᵥ τ)
      rw [hshift, qParam_two_vadd_one] at h
      have hfun : (fun m : ℕ => ((-1) ^ m * (Nat.card (qn A ⁻¹' {m}) : ℂ))
            • Periodic.qParam 2 (τ : ℂ) ^ m)
          = fun m : ℕ => (Nat.card (qn A ⁻¹' {m}) : ℂ) • (-Periodic.qParam 2 (τ : ℂ)) ^ m := by
        funext m
        rw [smul_eq_mul, smul_eq_mul, neg_pow (Periodic.qParam 2 (τ : ℂ)) m]
        ring
      rw [hfun]; exact h
    obtain ⟨m, hm⟩ : ∃ m, m = qn A z := ⟨_, rfl⟩
    have p1 := (hasFPowerSeriesOnBall_cuspFunction (f := thetaH A)
      (c := fun m : ℕ => (Nat.card (qn A ⁻¹' {m}) : ℂ)) two_pos han (hasSum_q2 hpos)).hasFPowerSeriesAt
    have p2 := (hasFPowerSeriesOnBall_cuspFunction (f := thetaH A)
      (c := fun m : ℕ => (-1) ^ m * (Nat.card (qn A ⁻¹' {m}) : ℂ)) two_pos han hs2).hasFPowerSeriesAt
    have c2 : (-1) ^ m * (Nat.card (qn A ⁻¹' {m}) : ℂ) = (Nat.card (qn A ⁻¹' {m}) : ℂ) := by
      simpa using congr_arg (FormalMultilinearSeries.coeff · m) (p2.eq_formalMultilinearSeries p1)
    by_contra hne
    have hodd : Odd m := by
      rw [← Int.odd_coe_nat, hm, ← norm_eq_qn hpos z]
      exact Int.not_even_iff_odd.mp hne
    rw [hodd.neg_one_pow] at c2
    have h0 : (Nat.card (qn A ⁻¹' {m}) : ℂ) = 0 := by linear_combination -c2 / 2
    have hfin := fiber_finite hpos m
    have : Nat.card (qn A ⁻¹' {m}) ≠ 0 := by
      have : Finite (qn A ⁻¹' {m}) := hfin
      have : Nonempty (qn A ⁻¹' {m}) := ⟨⟨z, hm.symm⟩⟩
      exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    exact this (by exact_mod_cast h0)

/-! ### Postulate Q and finiteness -/

lemma qf_vcast_smul (G : Matrix (Fin n) (Fin n) ℝ) (k : ℤ) (z : Fin n → ℤ) :
    qf G (vcast (k • z)) = (k : ℝ) ^ 2 * qf G (vcast z) := by
  have : vcast (k • z) = (k : ℝ) • vcast z := by ext i; simp [vcast]
  rw [this, qf_smul]

/-- A nonzero integral vector of nonpositive norm gives infinitely many such vectors. -/
lemma infinite_of_nonpos {z : Fin n → ℤ} (hz : z ≠ 0) (hq : z ⬝ᵥ (A *ᵥ z) ≤ 0) :
    ¬ ({w : Fin n → ℤ | w ⬝ᵥ (A *ᵥ w) ≤ 0}).Finite := by
  intro hfin
  have hinj : Function.Injective (fun k : ℕ => ((k : ℤ) • z : Fin n → ℤ)) := by
    intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h; push Not at h; exact hz (funext h)
    have := congrFun hab i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact_mod_cast mul_right_cancel₀ hi this
  refine Set.infinite_range_of_injective hinj (hfin.subset ?_)
  rintro _ ⟨k, rfl⟩
  simp only [Set.mem_ofPred_eq, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have h := mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg ((k : ℕ) : ℤ)) hq
  linarith [show ((k : ℕ) : ℤ) * (((k : ℕ) : ℤ) * (z ⬝ᵥ (A *ᵥ z)))
    = ((k : ℤ) * k) * (z ⬝ᵥ (A *ᵥ z)) by ring]

/-- Positive semidefinite with a nonzero isotropic vector forces that vector into the kernel. -/
lemma mulVec_eq_zero_of_isotropic {G : Matrix (Fin n) (Fin n) ℝ} (hs : G.IsSymm)
    (hpsd : ∀ y, 0 ≤ qf G y) {x : Fin n → ℝ} (hx : qf G x = 0) : G *ᵥ x = 0 := by
  have hb : ∀ y, y ⬝ᵥ (G *ᵥ x) = 0 := by
    intro y
    have hq : 0 ≤ y ⬝ᵥ (G *ᵥ y) := hpsd y
    have hsym : x ⬝ᵥ (G *ᵥ y) = y ⬝ᵥ (G *ᵥ x) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hs.eq, dotProduct_comm]
    have hx' : x ⬝ᵥ (G *ᵥ x) = 0 := hx
    have key : ∀ t : ℝ, 0 ≤ 2 * t * (y ⬝ᵥ (G *ᵥ x)) + t ^ 2 * (y ⬝ᵥ (G *ᵥ y)) := by
      intro t
      have := hpsd (x + t • y)
      simp only [qf, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul] at this
      rw [hsym, hx'] at this
      nlinarith [this]
    generalize y ⬝ᵥ (G *ᵥ x) = b at key ⊢
    generalize y ⬝ᵥ (G *ᵥ y) = q at key hq
    have := key (-b / (q + 1))
    have hq1 : 0 < q + 1 := by linarith
    by_contra hb0
    have hb2 : 0 < b ^ 2 := by positivity
    have e : 2 * (-b / (q + 1)) * b + (-b / (q + 1)) ^ 2 * q
        = -(b ^ 2 * (q + 2) / (q + 1) ^ 2) := by field_simp; ring
    rw [e] at this
    have : 0 < b ^ 2 * (q + 2) / (q + 1) ^ 2 := by positivity
    linarith
  ext i
  have := hb (Pi.single i 1)
  simpa [single_dotProduct] using this

/-- **Postulate Q as finiteness.** A symmetric integral quadratic form is positive-definite iff
every cost level `{z | Q(z) ≤ c}` contains only finitely many lattice vectors. -/
theorem posDef_iff_finite_levels (hs : A.IsSymm) :
    (A.map (Int.cast : ℤ → ℝ)).PosDef ↔
      ∀ c : ℤ, ({z : Fin n → ℤ | z ⬝ᵥ (A *ᵥ z) ≤ c}).Finite := by
  set G := A.map (Int.cast : ℤ → ℝ) with hG
  have hGs : G.IsSymm := by
    rw [hG, IsSymm, ← transpose_map, hs.eq]
  constructor
  · intro hpos c
    obtain ⟨l, hl, hb⟩ := exists_lower G hpos
    set R : ℤ := ⌈(c : ℝ) / l⌉ with hR
    refine (Set.Finite.pi (t := fun _ : Fin n => Set.Icc (-R) R)
      (fun _ => Set.finite_Icc (-R) R)).subset fun z hz => ?_
    simp only [Set.mem_ofPred_eq] at hz
    have h1 := hb (vcast z)
    rw [qf_cast] at h1
    have hzc : ((z ⬝ᵥ (A *ᵥ z) : ℤ) : ℝ) ≤ c := by exact_mod_cast hz
    have hsq : vcast z ⬝ᵥ vcast z ≤ (c : ℝ) / l := by
      rw [le_div_iff₀ hl]; linarith
    have hRge : (c : ℝ) / l ≤ R := Int.le_ceil _
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    · have hi : ((z i : ℝ)) ^ 2 ≤ vcast z ⬝ᵥ vcast z := by
        have := Finset.single_le_sum (f := fun j => vcast z j * vcast z j)
          (fun j _ => mul_self_nonneg (vcast z j)) (Finset.mem_univ i)
        simpa [vcast, sq, dotProduct] using this
      have : ((z i : ℤ) : ℝ) ^ 2 ≤ (R : ℝ) := by linarith
      have h2 : (z i) ^ 2 ≤ R := by exact_mod_cast this
      constructor <;> nlinarith [sq_nonneg (z i - 1), sq_nonneg (z i + 1)]
  · intro hfin
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hGs.eq
    · simp only [star_trivial]
      by_contra hle
      push Not at hle
      -- either some vector has negative cost, or the form is singular
      by_cases hneg : ∃ y, qf G y < 0
      · obtain ⟨y, hy⟩ := hneg
        have hcont : ContinuousAt (qf G) y := (continuous_qf G).continuousAt
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
          (isOpen_lt (continuous_qf G) continuous_const) y hy
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
        set z : Fin n → ℤ := fun i => ⌊y i * (N + 1)⌋ with hz
        have hN1 : (0 : ℝ) < N + 1 := by positivity
        have hclose : dist (((N : ℝ) + 1)⁻¹ • vcast z) y < ε := by
          refine lt_of_le_of_lt ?_ hN
          rw [dist_pi_le_iff (by positivity)]
          intro i
          simp only [Pi.smul_apply, smul_eq_mul, vcast, hz, Real.dist_eq]
          have f1 := Int.floor_le (y i * (N + 1))
          have f2 := Int.lt_floor_add_one (y i * (N + 1))
          have e : ((N : ℝ) + 1)⁻¹ * (⌊y i * (N + 1)⌋ : ℝ) - y i
              = ((⌊y i * (N + 1)⌋ : ℝ) - y i * (N + 1)) / (N + 1) := by
            field_simp
          rw [e, abs_div, abs_of_pos hN1, div_le_div_iff_of_pos_right hN1, abs_le]
          constructor <;> linarith
        have hneg' : qf G (((N : ℝ) + 1)⁻¹ • vcast z) < 0 := hball hclose
        rw [qf_smul] at hneg'
        have hqz : qf G (vcast z) < 0 := by
          by_contra h; push Not at h
          have : 0 ≤ (((N : ℝ) + 1)⁻¹) ^ 2 * qf G (vcast z) := by positivity
          linarith
        rw [qf_cast] at hqz
        have hz0 : z ≠ 0 := by
          rintro h0; rw [h0] at hqz; simp at hqz
        exact infinite_of_nonpos hz0 (by exact_mod_cast hqz.le) (hfin 0)
      · push Not at hneg
        have hx0 : qf G x = 0 := le_antisymm (by simpa [qf] using hle) (hneg x)
        have hker := mulVec_eq_zero_of_isotropic hGs hneg hx0
        have hdetG : G.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hker⟩
        have hdetA : A.det = 0 := by
          have : ((A.det : ℤ) : ℝ) = G.det := by
            rw [hG]; exact RingHom.map_det (Int.castRingHom ℝ) A
          exact_mod_cast this.trans hdetG
        obtain ⟨z, hz0, hzA⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetA
        exact infinite_of_nonpos hz0 (by rw [hzA]; simp) (hfin 0)

end PMArch.Translation
