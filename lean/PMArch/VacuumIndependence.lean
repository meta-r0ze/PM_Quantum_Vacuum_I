import PMArch.Vacuum
import PMArch.Postulates

/-!
# The vacuum postulates: equivalence and independence

* `geometric_iff`: the geometric postulates hold exactly for positive-definite, even,
  unimodular, nonzero lattices. They are therefore a PM reading of the classical conditions,
  neither weaker nor stronger.
* Each postulate is needed: `finiteness_needed` (hyperbolic plane), `readability_needed`
  (`D₄`), `bitAddressing_needed` (`A₂`), `exchange_needed` (`ℤ`), `economy_needed`
  (`E₈ ⊕ E₈`). Each witness satisfies every other postulate.
-/

namespace PMArch.Vacuum
open Matrix

/-- If every entry of a nonempty integral matrix is even, its determinant is even. -/
lemma det_even_of_entries_even {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i j, Even (A i j)) : Even A.det := by
  have hA : A = (2 : ℤ) • A.map (· / 2) := by
    ext i j; obtain ⟨k, hk⟩ := h i j; simp [hk]; omega
  rw [hA, det_smul, Fintype.card_fin]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨2 ^ m * (A.map (· / 2)).det, by ring⟩

/-- **The postulates are exactly the classical lattice conditions.** A substrate meets the
geometric postulates iff it is positive definite, even, unimodular and nonzero. -/
theorem geometric_iff (s : Substrate) :
    Geometric s ↔ (s.A.map (Int.cast : ℤ → ℝ)).PosDef ∧ (∀ z, Even (z ⬝ᵥ (s.A *ᵥ z))) ∧
      IsUnit s.A.det ∧ 0 < s.n := by
  refine ⟨geometric_lattice, ?_⟩
  rintro ⟨hp, he, hd, hn⟩
  have hd' := Int.isUnit_iff.mp hd
  have hodd : Odd s.A.det := by rcases hd' with h | h <;> rw [h] <;> decide
  refine ⟨(Translation.posDef_iff_finite_levels s.symm).mp hp, ?_, ?_, ?_⟩
  · exact (SelfReadable.bitReadable_iff_odd _).mpr hodd
  · refine ⟨(2 * s.A.det) • s.A.adjugate, ?_⟩
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    congr 1
    rcases hd' with h | h <;> rw [h] <;> norm_num
  · refine ⟨OrthogonalExchange.pairingExchange s.A, fun x => ?_, fun x y h => ?_, fun h0 => ?_⟩
    · change ((x ⬝ᵥ (s.A *ᵥ x) : ℤ) : ZMod 2) = 0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (even_iff_two_dvd.mp (he x))
    · change ((x ⬝ᵥ (s.A *ᵥ y) : ℤ) : ZMod 2) = 0
      simp [h]
    · apply Int.not_even_iff_odd.mpr hodd
      apply det_even_of_entries_even hn
      intro i j
      have := congrArg (fun C : OrthogonalExchange.Exchange s.n => C (Pi.single i 1) (Pi.single j 1)) h0
      simp only [OrthogonalExchange.pairingExchange, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.zero_apply] at this
      rw [mulVec_single_one, single_dotProduct, one_mul] at this
      exact even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this)

/-- The reduced pairing is an admissible exchange law on any even lattice with an odd
off-diagonal pairing. -/
lemma pairing_exchange_ok {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (he : ∀ z, Even (z ⬝ᵥ (A *ᵥ z))) (i j : Fin n) (hij : Odd (A i j)) :
    ∃ C : OrthogonalExchange.Exchange n, OrthogonalExchange.Alternating C ∧
      OrthogonalExchange.OrthogonalLocal A C ∧ C ≠ 0 := by
  refine ⟨OrthogonalExchange.pairingExchange A, fun x => ?_, fun x y h => ?_, fun h0 => ?_⟩
  · change ((x ⬝ᵥ (A *ᵥ x) : ℤ) : ZMod 2) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (even_iff_two_dvd.mp (he x))
  · change ((x ⬝ᵥ (A *ᵥ y) : ℤ) : ZMod 2) = 0
    simp [h]
  · have := congrArg (fun C : OrthogonalExchange.Exchange n => C (Pi.single i 1) (Pi.single j 1)) h0
    simp only [OrthogonalExchange.pairingExchange, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.zero_apply] at this
    rw [mulVec_single_one, single_dotProduct, one_mul] at this
    exact (Int.not_even_iff_odd.mpr hij)
      (even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this))

/-! ## Independence: each postulate is needed -/

/-- The hyperbolic plane: readable, bit-addressed, with a local nontrivial exchange law,
but with infinitely many states of bounded cost. **Finiteness is needed.** -/
def hypA : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
lemma hypA_symm : hypA.IsSymm := by ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem finiteness_needed :
    SelfReadable.BitReadable hypA ∧ (∃ M, hypA * M = (2 : ℤ) • 1) ∧
      (∃ C : OrthogonalExchange.Exchange 2, OrthogonalExchange.Alternating C ∧
        OrthogonalExchange.OrthogonalLocal hypA C ∧ C ≠ 0) ∧
      ¬ ∀ c : ℤ, {z : Fin 2 → ℤ | z ⬝ᵥ (hypA *ᵥ z) ≤ c}.Finite := by
  have he : ∀ z : Fin 2 → ℤ, Even (z ⬝ᵥ (hypA *ᵥ z)) := fun z =>
    ⟨z 0 * z 1, by simp [hypA, dotProduct, mulVec, Fin.sum_univ_two]; ring⟩
  refine ⟨(SelfReadable.bitReadable_iff_odd _).mpr ?_, ⟨(2 : ℤ) • hypA, ?_⟩,
    pairing_exchange_ok hypA he 0 1 (by decide), fun hf => ?_⟩
  · simp [hypA, Matrix.det_fin_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [hypA]
  · have hp := (Translation.posDef_iff_finite_levels hypA_symm).mpr hf
    have := hp.dotProduct_mulVec_pos (x := ![1, 0]) (by simp)
    simp [hypA, dotProduct, mulVec, Fin.sum_univ_two] at this

/-- `D₄`: positive definite, bit-addressed, local nontrivial exchange, but the glue vector
`(1,0,1,0)` pairs evenly with every probe. **Self-readability is needed.** -/
def d4A : Matrix (Fin 4) (Fin 4) ℤ := !![2, -1, 0, 0; -1, 2, -1, -1; 0, -1, 2, 0; 0, -1, 0, 2]
lemma d4A_symm : d4A.IsSymm := by decide

lemma d4_quad (z : Fin 4 → ℤ) : z ⬝ᵥ (d4A *ᵥ z) =
    2 * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - z 0 * z 1 - z 1 * z 2 - z 1 * z 3) := by
  simp [d4A, dotProduct, mulVec, Fin.sum_univ_succ]; ring

theorem readability_needed :
    (∀ c : ℤ, {z : Fin 4 → ℤ | z ⬝ᵥ (d4A *ᵥ z) ≤ c}.Finite) ∧
      (∃ M, d4A * M = (2 : ℤ) • 1) ∧
      (∃ C : OrthogonalExchange.Exchange 4, OrthogonalExchange.Alternating C ∧
        OrthogonalExchange.OrthogonalLocal d4A C ∧ C ≠ 0) ∧
      ¬ SelfReadable.BitReadable d4A := by
  have he : ∀ z : Fin 4 → ℤ, Even (z ⬝ᵥ (d4A *ᵥ z)) := fun z => by
    rw [d4_quad]; exact even_two_mul _
  refine ⟨(Translation.posDef_iff_finite_levels d4A_symm).mp ?_,
    ⟨!![2, 2, 1, 1; 2, 4, 2, 2; 1, 2, 2, 1; 1, 2, 1, 2], by decide⟩,
    pairing_exchange_ok d4A he 0 1 (by decide), fun hr => ?_⟩
  · refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [d4A]
    · have key : 2 * (star x ⬝ᵥ (d4A.map (Int.cast : ℤ → ℝ) *ᵥ x)) =
          (2 * x 1 - x 0 - x 2 - x 3) ^ 2 + (x 0 - x 2) ^ 2 + (x 0 - x 3) ^ 2 +
            (x 2 - x 3) ^ 2 + x 0 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
        simp [d4A, dotProduct, mulVec, Fin.sum_univ_succ]; ring
      by_cases h : x 0 = 0 ∧ x 2 = 0 ∧ x 3 = 0
      · obtain ⟨h0, h2, h3⟩ := h
        have h1 : x 1 ≠ 0 := fun h1 => hx (by ext i; fin_cases i <;> simp [h0, h1, h2, h3])
        have : 0 < (2 * x 1 - x 0 - x 2 - x 3) ^ 2 := by
          refine sq_pos_of_ne_zero ?_
          rw [h0, h2, h3]; intro h; apply h1; linarith
        nlinarith [sq_nonneg (x 0 - x 2), sq_nonneg (x 0 - x 3), sq_nonneg (x 2 - x 3),
          sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3)]
      · have : 0 < x 0 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
          by_contra hc
          apply h
          refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3)]
        nlinarith [sq_nonneg (2 * x 1 - x 0 - x 2 - x 3), sq_nonneg (x 0 - x 2),
          sq_nonneg (x 0 - x 3), sq_nonneg (x 2 - x 3)]
  · obtain ⟨w, hw⟩ := hr ![1, 0, 1, 0] fun y =>
      ⟨y 0 - y 1 + y 2, by simp [d4A, dotProduct, mulVec, Fin.sum_univ_succ]; ring⟩
    have := congrFun hw 0
    simp at this
    omega

/-- `A₂`: positive definite, readable (determinant 3), local nontrivial exchange, but its glue
group `ℤ/3` is not 2-torsion. **Bit-addressing is needed.** -/
def a2A : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -1, 2]
lemma a2A_symm : a2A.IsSymm := by decide

theorem bitAddressing_needed :
    (∀ c : ℤ, {z : Fin 2 → ℤ | z ⬝ᵥ (a2A *ᵥ z) ≤ c}.Finite) ∧
      SelfReadable.BitReadable a2A ∧
      (∃ C : OrthogonalExchange.Exchange 2, OrthogonalExchange.Alternating C ∧
        OrthogonalExchange.OrthogonalLocal a2A C ∧ C ≠ 0) ∧
      ¬ ∃ M, a2A * M = (2 : ℤ) • 1 := by
  have he : ∀ z : Fin 2 → ℤ, Even (z ⬝ᵥ (a2A *ᵥ z)) := fun z =>
    ⟨z 0 ^ 2 - z 0 * z 1 + z 1 ^ 2, by simp [a2A, dotProduct, mulVec, Fin.sum_univ_two]; ring⟩
  refine ⟨(Translation.posDef_iff_finite_levels a2A_symm).mp ?_,
    (SelfReadable.bitReadable_iff_odd _).mpr ?_,
    pairing_exchange_ok a2A he 0 1 (by decide), ?_⟩
  · refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [a2A]
    · have key : star x ⬝ᵥ (a2A.map (Int.cast : ℤ → ℝ) *ᵥ x) =
          x 0 ^ 2 + x 1 ^ 2 + (x 0 - x 1) ^ 2 := by
        simp [a2A, dotProduct, mulVec, Fin.sum_univ_two]; ring
      rw [key]
      by_cases h0 : x 0 = 0
      · have h1 : x 1 ≠ 0 := fun h1 => hx (by ext i; fin_cases i <;> simp [h0, h1])
        nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (x 0), sq_nonneg (x 0 - x 1)]
      · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 1), sq_nonneg (x 0 - x 1)]
  · simp [a2A, Matrix.det_fin_two]; decide
  · rintro ⟨M, hM⟩
    have := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one] at this
    simp [a2A, Matrix.det_fin_two] at this
    omega

/-- `ℤ¹`: finite, readable and bit-addressed, but every alternating exchange form on a rank-one
lattice vanishes. **A nontrivial local exchange law is needed.** -/
def z1A : Matrix (Fin 1) (Fin 1) ℤ := 1
lemma z1A_symm : z1A.IsSymm := by simp [z1A, IsSymm]

theorem exchange_needed :
    (∀ c : ℤ, {z : Fin 1 → ℤ | z ⬝ᵥ (z1A *ᵥ z) ≤ c}.Finite) ∧
      SelfReadable.BitReadable z1A ∧ (∃ M, z1A * M = (2 : ℤ) • 1) ∧
      ¬ ∃ C : OrthogonalExchange.Exchange 1, OrthogonalExchange.Alternating C ∧ C ≠ 0 := by
  refine ⟨(Translation.posDef_iff_finite_levels z1A_symm).mp ?_,
    (SelfReadable.bitReadable_iff_odd _).mpr (by simp [z1A]), ⟨(2 : ℤ) • 1, by simp [z1A]⟩, ?_⟩
  · refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · ext i j; fin_cases i; fin_cases j; simp [z1A]
    · have h0 : x 0 ≠ 0 := fun h => hx (by ext i; fin_cases i; exact h)
      simp [z1A, dotProduct, mulVec]
      positivity
  · rintro ⟨C, halt, hC⟩
    apply hC
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    have hx : x = x 0 • (fun _ => 1) := by ext i; fin_cases i; simp
    have hy : y = y 0 • (fun _ => 1) := by ext i; fin_cases i; simp
    rw [hx, hy]
    simp only [map_smul, LinearMap.smul_apply, LinearMap.zero_apply]
    rw [halt]

/-- `E₈ ⊕ E₈` (on `Fin 16`). -/
def e8e8A : Matrix (Fin 16) (Fin 16) ℤ :=
  (Postulates.blk Lattices.gram).submatrix (finSumFinEquiv (m := 8) (n := 8)).symm
    (finSumFinEquiv (m := 8) (n := 8)).symm

def e8e8 : Substrate :=
  ⟨16, e8e8A, by
    have hs : (Postulates.blk Lattices.gram).IsSymm := by
      unfold Postulates.blk
      rw [IsSymm, fromBlocks_transpose, Lattices.gram_symmetric]; simp
    exact hs.submatrix _⟩

/-- `E₈ ⊕ E₈` meets every geometric postulate but has rank 16. **Economy is needed.** -/
theorem economy_needed : Geometric e8e8 ∧ ¬ Economical e8e8 := by
  obtain ⟨_, hp, he, hd⟩ := Postulates.minimality_needed
  refine ⟨(geometric_iff _).mpr ⟨?_, ?_, ?_, by show 0 < 16; decide⟩, fun h => ?_⟩
  · show (e8e8A.map (Int.cast : ℤ → ℝ)).PosDef
    unfold e8e8A
    rw [← Matrix.submatrix_map]
    exact hp.submatrix (finSumFinEquiv (m := 8) (n := 8)).symm.injective
  · show ∀ z : Fin 16 → ℤ, Even (z ⬝ᵥ (e8e8A *ᵥ z))
    intro z
    unfold e8e8A
    rw [submatrix_mulVec_equiv]
    have := he (z ∘ (finSumFinEquiv (m := 8) (n := 8)).symm.symm)
    rwa [← dotProduct_comp_equiv_symm] at this
  · show IsUnit e8e8A.det
    unfold e8e8A
    rw [det_submatrix_equiv_self]; exact hd
  · have := h e8 e8_geometric
    exact absurd this (by show ¬ (16 ≤ 8); decide)

end PMArch.Vacuum
