import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import PMArch.RankEight

/-!
# The theta series of a rank-eight even unimodular lattice is `E₄`

For a positive-definite even unimodular integral Gram matrix of size 8, the theta series
`θ(τ) = ∑_z exp(π i τ zᵀAz)` is a level-one modular form of weight 4. The space of such forms
is one-dimensional, so `θ = E₄`, and comparing `q`-expansion coefficients shows that the lattice
has exactly 240 vectors of norm 2.
-/

noncomputable section
open Complex Matrix ModularForm SlashInvariantForm
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold

namespace PMArch.ThetaE8
open PMArch.RankEight

/-- The theta series as a function of `w` in the upper half-plane (`s = -i w`). -/
def thetaFun {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (w : ℂ) : ℂ :=
  theta (A.map (Int.cast : ℤ → ℝ)) (-I * w)

/-- The theta series on `ℍ`. -/
def thetaH {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℍ → ℂ := thetaFun A ∘ (↑)

lemma qf_nonneg {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (x : Fin n → ℝ) :
    0 ≤ qf G x := by
  by_cases hx : x = 0
  · subst hx; simp [qf]
  · exact (qf_pos hG hx).le

lemma norm_theta_term (w : ℂ) (q : ℝ) :
    ‖cexp (-π * (-I * w) * (q : ℂ))‖ = Real.exp (-(π * w.im) * q) := by
  rw [Complex.norm_exp]; congr 1; simp [mul_re]

lemma differentiableOn_thetaFun {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) {y : ℝ} (hy : 0 < y) :
    DifferentiableOn ℂ (thetaFun A) {w : ℂ | y < w.im} := by
  set G := A.map (Int.cast : ℤ → ℝ)
  refine differentiableOn_tsum_of_summable_norm
    (u := fun z => Real.exp (-(π * y) * qf G (vcast z))) ?_ ?_ ?_ ?_
  · simpa only [sub_zero] using summable_qf G hpos (mul_pos Real.pi_pos hy) 0
  · intro z; fun_prop
  · exact isOpen_lt continuous_const Complex.continuous_im
  · intro z w hw
    rw [norm_theta_term]
    apply Real.exp_le_exp.mpr
    have hq : 0 ≤ qf (A.map (Int.cast : ℤ → ℝ)) (vcast z) := qf_nonneg hpos (vcast z)
    have hw' : y < w.im := hw
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hw'.le)) hq]

lemma mdiff_thetaH {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) : MDiff (thetaH A) := by
  intro τ
  have hy : 0 < τ.im / 2 := by linarith [τ.im_pos]
  have hmem : {w : ℂ | τ.im / 2 < w.im} ∈ nhds (τ : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (by show τ.im / 2 < (τ : ℂ).im; simp; linarith [τ.im_pos])
  exact ((differentiableOn_thetaFun A hpos hy).differentiableAt hmem).mdifferentiableAt.comp
    τ τ.mdifferentiable_coe

lemma isBoundedAtImInfty_thetaH {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) : IsBoundedAtImInfty (thetaH A) := by
  set G := A.map (Int.cast : ℤ → ℝ)
  have hsum : Summable (fun z : Fin n → ℤ => Real.exp (-(π * 1) * qf G (vcast z))) := by
    simpa only [sub_zero] using summable_qf G hpos (mul_pos Real.pi_pos one_pos) 0
  rw [isBoundedAtImInfty_iff]
  refine ⟨∑' z : Fin n → ℤ, Real.exp (-(π * 1) * qf G (vcast z)), 1, fun τ hτ => ?_⟩
  have hle : ∀ z : Fin n → ℤ, ‖cexp (-π * (-I * (τ : ℂ)) * (qf G (vcast z) : ℂ))‖
      ≤ Real.exp (-(π * 1) * qf G (vcast z)) := by
    intro z
    rw [norm_theta_term]
    apply Real.exp_le_exp.mpr
    have hq : 0 ≤ qf (A.map (Int.cast : ℤ → ℝ)) (vcast z) := qf_nonneg hpos (vcast z)
    have : (1 : ℝ) ≤ (τ : ℂ).im := by simpa using hτ
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr this)) hq]
  have hsn : Summable (fun z : Fin n → ℤ =>
      ‖cexp (-π * (-I * (τ : ℂ)) * (qf G (vcast z) : ℂ))‖) :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  calc ‖thetaH A τ‖ ≤ ∑' z : Fin n → ℤ, ‖cexp (-π * (-I * (τ : ℂ)) * (qf G (vcast z) : ℂ))‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ _ := hsn.tsum_le_tsum hle hsum

set_option backward.isDefEq.respectTransparency false in
lemma thetaH_T {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (heven : ∀ z : Fin n → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (k : ℤ) :
    (thetaH A ∣[k] ModularGroup.T) = thetaH A := by
  ext z
  have hd : denom (ModularGroup.T : SL(2, ℤ)) z = 1 := by
    simp [ModularGroup.denom_apply, ModularGroup.T]
  rw [SL_slash_apply, hd, modular_T_smul, _root_.one_zpow, mul_one]
  simp only [thetaH, Function.comp_apply, thetaFun, coe_vadd]
  have h := theta_shift A heven (-I * (z : ℂ))
  rw [← h]
  congr 1
  push_cast
  ring

lemma thetaH_S (A : Matrix (Fin 8) (Fin 8) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) (hdet : IsUnit A.det) :
    (thetaH A ∣[(4 : ℤ)] ModularGroup.S) = thetaH A := by
  ext z
  rw [slash_S_apply]
  simp only [thetaH, Function.comp_apply, thetaFun]
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hre : 0 < (-I * (z : ℂ)).re := by simpa using z.im_pos
  have hinv := theta_inversion A hpos hdet (-I * (z : ℂ)) hre
  have h4 : ((-I * (z : ℂ)) ^ (1 / 2 : ℂ)) ^ 8 = (z : ℂ) ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, sq_half]
    ring_nf
    rw [Complex.I_pow_four, one_mul]
  have he : (-I * (z : ℂ))⁻¹ = -I * -(z : ℂ)⁻¹ := by
    field_simp
    rw [I_sq]
  rw [h4, he] at hinv
  rw [hinv, ← neg_inv, _root_.zpow_neg, mul_comm]
  norm_cast

/-- The theta series of a rank-eight even unimodular lattice as a level-one modular form
of weight 4. -/
def thetaMF (A : Matrix (Fin 8) (Fin 8) ℤ) (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin 8 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (hdet : IsUnit A.det) :
    ModularForm 𝒮ℒ 4 where
  toFun := thetaH A
  slash_action_eq' γ hγ := by
    obtain ⟨γ, rfl⟩ := hγ
    exact slash_action_generators_SL2Z (thetaH_S A hpos hdet) (thetaH_T A heven 4) γ
  holo' := mdiff_thetaH A hpos
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z (thetaH_S A hpos hdet) (thetaH_T A heven 4)]
    exact isBoundedAtImInfty_thetaH A hpos

/-- Half the norm, as a natural number. -/
def halfNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) : ℕ :=
  ((z ⬝ᵥ (A *ᵥ z)) / 2).toNat

lemma norm_eq_two_halfNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin n → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (z : Fin n → ℤ) :
    z ⬝ᵥ (A *ᵥ z) = 2 * (halfNorm A z : ℤ) := by
  obtain ⟨k, hk⟩ := heven z
  have hnn : (0 : ℝ) ≤ ((z ⬝ᵥ (A *ᵥ z) : ℤ) : ℝ) := by
    rw [← qf_cast]; exact qf_nonneg hpos _
  have hk0 : 0 ≤ k := by
    have : (0 : ℤ) ≤ z ⬝ᵥ (A *ᵥ z) := by exact_mod_cast hnn
    omega
  simp only [halfNorm, hk]
  omega

lemma hasSum_thetaH_q {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin n → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (τ : ℍ) :
    HasSum (fun m : ℕ => (Nat.card (halfNorm A ⁻¹' {m}) : ℂ) • Function.Periodic.qParam 1 τ ^ m)
      (thetaH A τ) := by
  set G := A.map (Int.cast : ℤ → ℝ)
  have hterm : ∀ z : Fin n → ℤ, cexp (-π * (-I * (τ : ℂ)) * (qf G (vcast z) : ℂ))
      = Function.Periodic.qParam 1 τ ^ halfNorm A z := by
    intro z
    rw [qf_cast, norm_eq_two_halfNorm A hpos heven z, Function.Periodic.qParam,
      ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring_nf
  have hsum : Summable (fun z : Fin n → ℤ => cexp (-π * (-I * (τ : ℂ)) * (qf G (vcast z) : ℂ))) := by
    refine Summable.of_norm ?_
    simp only [norm_theta_term, UpperHalfPlane.coe_im]
    simpa only [sub_zero] using summable_qf G hpos (mul_pos Real.pi_pos τ.im_pos) 0
  have h := hsum.hasSum.tsum_fiberwise (halfNorm A)
  simp only [hterm] at h
  have hθ : thetaH A τ = ∑' z : Fin n → ℤ, Function.Periodic.qParam 1 (τ : ℂ) ^ halfNorm A z := by
    simp only [thetaH, Function.comp_apply, thetaFun, theta]
    exact tsum_congr hterm
  rw [hθ]
  convert h using 2 with m
  have hc : ∀ b : halfNorm A ⁻¹' {m},
      Function.Periodic.qParam 1 (τ : ℂ) ^ halfNorm A b = Function.Periodic.qParam 1 τ ^ m :=
    fun b => by rw [show halfNorm A b = m from b.2]
  rw [tsum_congr hc, tsum_const, nsmul_eq_mul, smul_eq_mul]

/-- The `q`-expansion coefficients of the theta series count lattice vectors by norm. -/
lemma thetaMF_coeff (A : Matrix (Fin 8) (Fin 8) ℤ) (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin 8 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (hdet : IsUnit A.det) (m : ℕ) :
    (qExpansion 1 (thetaMF A hpos heven hdet)).coeff m = (Nat.card (halfNorm A ⁻¹' {m}) : ℂ) :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL
    (f := thetaMF A hpos heven hdet) (fun τ => hasSum_thetaH_q A hpos heven τ) m).symm

/-- The only vector of norm zero is zero. -/
lemma card_halfNorm_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin n → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) :
    Nat.card (halfNorm A ⁻¹' {0}) = 1 := by
  have hset : halfNorm A ⁻¹' {0} = {0} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hz
      have hz' : vcast z ≠ 0 := by
        intro h0; apply hz; ext i
        have := congrFun h0 i
        simpa [vcast] using this
      have hq := qf_pos hpos hz'
      rw [qf_cast, norm_eq_two_halfNorm A hpos heven z, h] at hq
      simp at hq
    · rintro rfl; simp [halfNorm]
  rw [hset, Nat.card_unique]

/-- **The theta series is `E₄`.** -/
theorem thetaMF_eq_E₄ (A : Matrix (Fin 8) (Fin 8) ℤ) (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin 8 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (hdet : IsUnit A.det) :
    thetaMF A hpos heven hdet = E₄ := by
  have hrank : Module.finrank ℂ (ModularForm 𝒮ℒ 4) = 1 :=
    Module.finrank_eq_of_rank_eq (by simpa using levelOne_weight_four_rank_one)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' E₄
    (EisensteinSeries.E_ne_zero (by norm_num) ⟨2, rfl⟩)).mp hrank (thetaMF A hpos heven hdet)
  have h0 := thetaMF_coeff A hpos heven hdet 0
  rw [card_halfNorm_zero A hpos heven, ← hc, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_smul,
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩] at h0
  simp only [smul_eq_mul, mul_one, Nat.cast_one] at h0
  rw [← hc, h0, one_smul]

/-- **A rank-eight even unimodular lattice has exactly 240 roots.** -/
theorem card_roots_eq_240 (A : Matrix (Fin 8) (Fin 8) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin 8 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (hdet : IsUnit A.det) :
    Nat.card {z : Fin 8 → ℤ // z ⬝ᵥ (A *ᵥ z) = 2} = 240 := by
  have h1 := thetaMF_coeff A hpos heven hdet 1
  rw [thetaMF_eq_E₄, E₄_qExpansion_coeff_one] at h1
  have hcard : Nat.card (halfNorm A ⁻¹' {1}) = 240 := by exact_mod_cast h1.symm
  rw [← hcard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
  rw [norm_eq_two_halfNorm A hpos heven z]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  omega

/-- The explicit E8 Gram matrix has exactly 240 roots. -/
theorem e8_card_roots :
    Nat.card {z : Fin 8 → ℤ // z ⬝ᵥ (Lattices.gram *ᵥ z) = 2} = 240 :=
  card_roots_eq_240 Lattices.gram e8_even_unimodular.1 e8_even_unimodular.2.1
    e8_even_unimodular.2.2

end PMArch.ThetaE8
