import PMArch.Translation

/-!
# Postulate D as modular covariance

For an integral positive-definite lattice, unimodularity (self-duality) is equivalent to the
weight-`n/2` inversion law `θ(s) = s^{-n/2} θ(1/s)` for `Re s > 0`.
-/

noncomputable section
open Complex Matrix
open scoped Real

namespace PMArch.Translation
open PMArch.RankEight

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}

/-- Real theta sums. -/
def thR (G : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  ∑' z : Fin n → ℤ, Real.exp (-(π * t) * qf G (vcast z))

lemma summable_thR {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {t : ℝ} (ht : 0 < t) :
    Summable (fun z : Fin n → ℤ => Real.exp (-(π * t) * qf G (vcast z))) := by
  simpa only [sub_zero] using summable_qf G hG (mul_pos Real.pi_pos ht) 0

lemma theta_ofReal (G : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    theta G (t : ℂ) = (thR G t : ℂ) := by
  rw [thR, Complex.ofReal_tsum]
  refine tsum_congr fun z => ?_
  push_cast; ring_nf

lemma thR_ge_one {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {t : ℝ} (ht : 0 < t) :
    1 ≤ thR G t := by
  have h := (summable_thR hG ht).le_tsum 0 (fun _ _ => (Real.exp_pos _).le)
  have hv0 : vcast (0 : Fin n → ℤ) = 0 := by ext; simp [vcast]
  calc (1 : ℝ) = Real.exp (-(π * t) * qf G (vcast 0)) := by simp [qf, hv0]
    _ ≤ thR G t := h

lemma det_ne_zero_of_posDef (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) : A.det ≠ 0 := by
  intro h0
  have := hpos.det_pos
  have e : ((A.det : ℤ) : ℝ) = (A.map (Int.cast : ℤ → ℝ)).det :=
    RingHom.map_det (Int.castRingHom ℝ) A
  rw [← e, h0] at this
  simp at this

lemma mulVec_injective_of_det (hd : A.det ≠ 0) : Function.Injective (fun z => A *ᵥ z) := by
  intro z w h
  by_contra hne
  have : A *ᵥ (z - w) = 0 := by simp only [mulVec_sub] at *; exact sub_eq_zero.mpr h
  exact hd (Matrix.exists_mulVec_eq_zero_iff.mp ⟨z - w, sub_ne_zero.mpr hne, this⟩)

lemma exists_not_mem_range (hdet : ¬ IsUnit A.det) : ∃ m, m ∉ Set.range (fun z => A *ᵥ z) := by
  by_contra hall
  push Not at hall
  choose b hb using fun k : Fin n => hall (Pi.single k 1)
  let Bm : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i k => b k i
  have hAB : A * Bm = 1 := by
    ext i k
    have := congrFun (hb k) i
    simp only [mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Bm, of_apply, this, Matrix.one_apply, Pi.single_apply]
  apply hdet
  have := congrArg det hAB
  rw [det_mul, det_one] at this
  exact isUnit_of_mul_isUnit_left (y := Bm.det) (by rw [this]; exact isUnit_one)

/-- **Postulate D as modular covariance.** For an integral positive-definite lattice,
unimodularity is equivalent to the inversion law `θ(s) = (s^{1/2})^{-n} θ(1/s)`. -/
theorem unimodular_iff_S_covariant (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef) :
    IsUnit A.det ↔ ∀ s : ℂ, 0 < s.re → theta (A.map (Int.cast : ℤ → ℝ)) s
      = ((s ^ (1 / 2 : ℂ)) ^ n)⁻¹ * theta (A.map (Int.cast : ℤ → ℝ)) s⁻¹ := by
  constructor
  · intro hdet s hs
    exact theta_inversion A hpos hdet s hs
  · intro hS
    by_contra hdet
    set G := A.map (Int.cast : ℤ → ℝ) with hGdef
    have hGi := hpos.inv
    obtain ⟨C, hC⟩ := poisson n G hpos
    -- the dual theta sum
    let f : ℝ → (Fin n → ℤ) → ℝ := fun t m => Real.exp (-(π * t) * qf G⁻¹ (vcast m))
    have hfs : ∀ t, 0 < t → Summable (f t) := fun t ht => by
      simpa only [sub_zero, f] using summable_qf G⁻¹ hGi (mul_pos Real.pi_pos ht) 0
    -- relation θ(t) = C θ*(t)
    have hrel : ∀ t : ℝ, 0 < t → (thR G t : ℂ) = C * ((∑' m, f t m : ℝ) : ℂ) := by
      intro t ht
      have hre : 0 < ((t : ℂ)⁻¹).re := inv_re_pos (by simpa using ht)
      have h1 := hC (t : ℂ)⁻¹ hre 0
      have h2 := hS (t : ℂ)⁻¹ hre
      simp only [zero_dotProduct, Complex.ofReal_zero, mul_zero, add_zero, inv_inv,
        sub_zero] at h1
      rw [inv_inv] at h2
      have hr : ((((t : ℂ)⁻¹) ^ (1 / 2 : ℂ)) ^ n)⁻¹ ≠ 0 := by
        apply inv_ne_zero; apply pow_ne_zero
        rw [Ne, Complex.cpow_eq_zero_iff]; simp [ht.ne']
      have h3 : theta G (t : ℂ) = C * ∑' m : Fin n → ℤ,
          cexp (-π * (t : ℂ) * (qf G⁻¹ (vcast m) : ℂ)) := by
        have := h2.symm.trans h1
        rw [mul_comm C, mul_assoc] at this
        exact (mul_left_cancel₀ hr this).trans (by ring)
      rw [← theta_ofReal, h3, Complex.ofReal_tsum]
      congr 1
      refine tsum_congr fun m => ?_
      simp only [f]; push_cast; ring_nf
    -- split the dual sum over the image of `A` and its complement
    have hinj := mulVec_injective_of_det (det_ne_zero_of_posDef hpos)
    have hGu : IsUnit G.det := (isUnit_iff_isUnit_det G).mp hpos.isUnit
    have hfA : ∀ t z, f t (A *ᵥ z) = Real.exp (-(π * t) * qf G (vcast z)) := by
      intro t z
      have hv : vcast (A *ᵥ z) = G *ᵥ vcast z := by ext i; simp [vcast, G, mulVec, dotProduct]
      simp only [f, hv, qf, mulVec_mulVec, nonsing_inv_mul G hGu, one_mulVec]
      rw [dotProduct_comm]
    let S := Set.range (fun z => A *ᵥ z)
    let R : ℝ → ℝ := fun t => ∑' m : ↑Sᶜ, f t m
    have hsplit : ∀ t, 0 < t → ∑' m, f t m = thR G t + R t := by
      intro t ht
      rw [← (hfs t ht).tsum_subtype_add_tsum_subtype_compl S]
      congr 1
      rw [tsum_range (f t) hinj]
      exact tsum_congr fun z => hfA t z
    -- positivity of the excess
    obtain ⟨m0, hm0⟩ := exists_not_mem_range hdet
    have hRpos : ∀ t, 0 < t → 0 < R t := by
      intro t ht
      have := ((hfs t ht).subtype Sᶜ).le_tsum ⟨m0, hm0⟩ (fun _ _ => (Real.exp_pos _).le)
      exact lt_of_lt_of_le (Real.exp_pos _) this
    -- exponential decay of the excess
    obtain ⟨l, hl, hlb⟩ := exists_lower G⁻¹ hGi
    have hm1 : ∀ m : ↑Sᶜ, l ≤ qf G⁻¹ (vcast (m : Fin n → ℤ)) := by
      intro m
      have hm0' : (m : Fin n → ℤ) ≠ 0 := by
        intro h; apply m.2; exact ⟨0, by simp [h]⟩
      obtain ⟨i, hi⟩ : ∃ i, (m : Fin n → ℤ) i ≠ 0 := by
        by_contra h; push Not at h; exact hm0' (funext h)
      have hsq : 1 ≤ vcast (m : Fin n → ℤ) ⬝ᵥ vcast (m : Fin n → ℤ) := by
        have h1 : (1 : ℝ) ≤ ((m : Fin n → ℤ) i : ℝ) ^ 2 := by
          have : (1 : ℤ) ≤ ((m : Fin n → ℤ) i) ^ 2 := by
            have h1 := Int.one_le_abs hi
            have h2 := sq_abs ((m : Fin n → ℤ) i)
            nlinarith
          exact_mod_cast this
        have h2 := Finset.single_le_sum (f := fun j => vcast (m : Fin n → ℤ) j * vcast (m : Fin n → ℤ) j)
          (fun j _ => mul_self_nonneg (vcast (m : Fin n → ℤ) j)) (Finset.mem_univ i)
        simp only [vcast, dotProduct] at h2 ⊢
        nlinarith
      nlinarith [hlb (vcast (m : Fin n → ℤ))]
    have hdecay : ∀ K : ℝ, 0 ≤ K → R (1 + K) ≤ Real.exp (-(π * K * l)) * R 1 := by
      intro K hK
      have hs1 := (hfs 1 one_pos).subtype Sᶜ
      have hsK := (hfs (1 + K) (by linarith)).subtype Sᶜ
      rw [← tsum_mul_left]
      refine hsK.tsum_le_tsum (fun m => ?_) (hs1.mul_left _)
      simp only [f]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := hm1 m
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg Real.pi_pos.le hK)]
    -- C is real
    have hT1 : 0 < ∑' m, f 1 m := by
      rw [hsplit 1 one_pos]; linarith [thR_ge_one hpos one_pos, hRpos 1 one_pos]
    set c : ℝ := thR G 1 / ∑' m, f 1 m with hc
    have hCc : C = c := by
      have := hrel 1 one_pos
      rw [hc, Complex.ofReal_div, eq_div_iff (Complex.ofReal_ne_zero.mpr hT1.ne')]
      exact this.symm
    have hrelR : ∀ t, 0 < t → thR G t = c * (thR G t + R t) := by
      intro t ht
      have := hrel t ht
      rw [hCc, hsplit t ht] at this
      exact_mod_cast this
    have hcpos : 0 < c := div_pos (by linarith [thR_ge_one hpos one_pos]) hT1
    have h1c : 0 < 1 - c := by
      have := hrelR 1 one_pos
      have hR1 := hRpos 1 one_pos
      have hth := thR_ge_one hpos one_pos
      nlinarith
    -- choose a large `t`
    set K : ℝ := c * R 1 / ((1 - c) * (π * l)) with hK
    have hKnn : 0 ≤ K := by
      have := hRpos 1 one_pos
      positivity
    have hexp : Real.exp (-(π * K * l)) ≤ 1 / (1 + π * K * l) := by
      rw [Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le (by positivity)
      linarith [Real.add_one_le_exp (π * K * l)]
    have key := hrelR (1 + K) (by linarith)
    have hthK := thR_ge_one hpos (show (0 : ℝ) < 1 + K by linarith)
    have hdK := hdecay K hKnn
    have hR1 := hRpos 1 one_pos
    -- (1 - c) ≤ (1 - c) θ(t) = c R(t) ≤ c R(1) / (1 + π K l) < 1 - c
    have e1 : (1 - c) * thR G (1 + K) = c * R (1 + K) := by linarith
    have e2 : 1 + π * K * l = 1 + c * R 1 / (1 - c) := by
      rw [hK]; field_simp
    have hlt : c * R 1 * (1 / (1 + π * K * l)) < 1 - c := by
      rw [e2]
      have h0 : 0 < 1 + c * R 1 / (1 - c) := by positivity
      rw [mul_one_div, div_lt_iff₀ h0]
      field_simp
      nlinarith
    have : (1 - c) ≤ c * R 1 * (1 / (1 + π * K * l)) := by
      calc 1 - c ≤ (1 - c) * thR G (1 + K) := by nlinarith
        _ = c * R (1 + K) := e1
        _ ≤ c * (Real.exp (-(π * K * l)) * R 1) := by gcongr
        _ ≤ c * ((1 / (1 + π * K * l)) * R 1) := by gcongr
        _ = c * R 1 * (1 / (1 + π * K * l)) := by ring
    linarith

end PMArch.Translation
