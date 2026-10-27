import PMArch.E8Unique

/-!
# Independence of the lattice postulates

Each of the postulates used to select E8 (positive-definite, even, unimodular, minimal rank) is
needed: dropping any one of them admits a lattice that satisfies the others but not the
conclusion. The first three examples violate `8 ∣ n` (`RankEight.rank_dvd_eight`); the fourth
shows that without minimal rank an even unimodular positive-definite lattice need not have
rank eight.
-/

noncomputable section
open Matrix

namespace PMArch.Postulates

/-- `ℤ¹`: positive-definite and unimodular but odd; its rank is not divisible by 8. -/
theorem evenness_needed : ∃ A : Matrix (Fin 1) (Fin 1) ℤ,
    (A.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit A.det ∧
      ¬ (∀ z : Fin 1 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) ∧ ¬ 8 ∣ 1 := by
  refine ⟨1, PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_, by simp, ?_, by norm_num⟩
  · ext i j; fin_cases i; fin_cases j; simp
  · have h0 : x 0 ≠ 0 := fun h => hx (by ext i; fin_cases i; exact h)
    simp [dotProduct, mulVec]
    positivity
  · intro h
    have := h (fun _ => 1)
    simp [dotProduct, mulVec] at this

/-- `A₁` (Gram matrix `[2]`): positive-definite and even but not unimodular. -/
theorem unimodularity_needed : ∃ A : Matrix (Fin 1) (Fin 1) ℤ,
    (A.map (Int.cast : ℤ → ℝ)).PosDef ∧ (∀ z : Fin 1 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) ∧
      ¬ IsUnit A.det ∧ ¬ 8 ∣ 1 := by
  refine ⟨!![2], PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_, fun z => ?_, ?_, by norm_num⟩
  · ext i j; fin_cases i; fin_cases j; simp
  · have h0 : x 0 ≠ 0 := fun h => hx (by ext i; fin_cases i; exact h)
    simp [dotProduct, mulVec]
    nlinarith [mul_self_pos.mpr h0]
  · exact ⟨z 0 * z 0, by simp [dotProduct, mulVec]; ring⟩
  · simp [Int.isUnit_iff]

/-- The hyperbolic plane `II₁,₁`: even and unimodular but indefinite; rank 2. -/
theorem positivity_needed : ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
    A.IsSymm ∧ (∀ z : Fin 2 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) ∧ IsUnit A.det ∧
      ¬ (A.map (Int.cast : ℤ → ℝ)).PosDef ∧ ¬ 8 ∣ 2 := by
  refine ⟨!![0, 1; 1, 0], ?_, fun z => ?_, ?_, fun h => ?_, by norm_num⟩
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · exact ⟨z 0 * z 1, by simp [dotProduct, mulVec, Fin.sum_univ_two]; ring⟩
  · simp [Matrix.det_fin_two]
  · have := h.dotProduct_mulVec_pos (x := ![1, 0]) (by simp)
    simp [dotProduct, mulVec, Fin.sum_univ_two] at this

/-- Block-diagonal sum of two copies of an 8×8 matrix (index type `Fin 8 ⊕ Fin 8`, rank 16). -/
def blk {R : Type*} [Zero R] (M : Matrix (Fin 8) (Fin 8) R) :
    Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) R :=
  fromBlocks M 0 0 M

lemma q_split {R : Type*} [CommRing R] (M : Matrix (Fin 8) (Fin 8) R) (x : Fin 8 ⊕ Fin 8 → R) :
    x ⬝ᵥ (blk M *ᵥ x) = (x ∘ Sum.inl) ⬝ᵥ (M *ᵥ (x ∘ Sum.inl))
      + (x ∘ Sum.inr) ⬝ᵥ (M *ᵥ (x ∘ Sum.inr)) := by
  simp [dotProduct, mulVec, Fintype.sum_sum_type, blk]

/-- `E8 ⊕ E8`: positive-definite, even and unimodular of rank 16. Without the minimal-rank
postulate, the remaining postulates do not force rank eight. -/
theorem minimality_needed :
    Fintype.card (Fin 8 ⊕ Fin 8) = 16 ∧
    ((blk Lattices.gram).map (Int.cast : ℤ → ℝ)).PosDef ∧
      (∀ z : Fin 8 ⊕ Fin 8 → ℤ, Even (z ⬝ᵥ (blk Lattices.gram *ᵥ z))) ∧
      IsUnit (blk Lattices.gram).det := by
  refine ⟨by simp, ?_, fun z => ?_, ?_⟩
  · have hE := RankEight.e8_even_unimodular.1
    have hmap : (blk Lattices.gram).map (Int.cast : ℤ → ℝ)
        = blk (Lattices.gram.map (Int.cast : ℤ → ℝ)) := by
      simp [blk, fromBlocks_map]
    rw [hmap]
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · simp only [blk, IsHermitian, fromBlocks_conjTranspose, conjTranspose_zero]
      rw [hE.1]
    · simp only [star_trivial]
      rw [q_split]
      have hl := fun (v : Fin 8 → ℝ) (hv : v ≠ 0) => hE.dotProduct_mulVec_pos hv
      have nn : ∀ v : Fin 8 → ℝ, 0 ≤ v ⬝ᵥ ((Lattices.gram.map (Int.cast : ℤ → ℝ)) *ᵥ v) := by
        intro v; by_cases hv : v = 0
        · simp [hv]
        · simpa using (hl v hv).le
      by_cases h1 : x ∘ Sum.inl = 0
      · have h2 : x ∘ Sum.inr ≠ 0 := by
          intro h2; apply hx; ext i
          cases i with
          | inl a => exact congrFun h1 a
          | inr a => exact congrFun h2 a
        have := hl _ h2
        simp only [star_trivial] at this
        linarith [nn (x ∘ Sum.inl)]
      · have := hl _ h1
        simp only [star_trivial] at this
        linarith [nn (x ∘ Sum.inr)]
  · rw [q_split]
    obtain ⟨k, hk⟩ := Lattices.even_norm (z ∘ Sum.inl)
    obtain ⟨l, hl⟩ := Lattices.even_norm (z ∘ Sum.inr)
    simp only [Lattices.pairing] at hk hl
    exact ⟨k + l, by rw [hk, hl]; ring⟩
  · rw [blk, det_fromBlocks_zero₂₁]
    exact Lattices.gram_unimodular.mul Lattices.gram_unimodular

end PMArch.Postulates
