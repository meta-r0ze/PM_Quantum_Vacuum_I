import PMArch.Research.OperationalDuality
import PMArch.Parity

/-!
# Intrinsic parity and rank-eight alternatives

These results test necessity of the operational symmetry premises. Intrinsic
parity and a corrected exchange law are mathematical alternatives, not assumed
physical statistics. No microscopic quantum vacuum is constructed here.
-/
noncomputable section
namespace PMArch.IntrinsicConstraints
open Matrix

lemma integer_self_correction_even (k : ℤ) : Even (k-k^2) := by
  have h := (Int.even_mul_pred_self k).neg
  convert h using 1
  ring

/-- The parity-corrected exchange exponent has even diagonal on every
integral lattice, including odd ones. -/
theorem corrected_diagonal_even {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (z : Fin n → ℤ) :
    Even (z ⬝ᵥ (A *ᵥ z) - (z ⬝ᵥ (A *ᵥ z))^2) :=
  integer_self_correction_even _

/-- The admissible readout space is intrinsically determined by A. For every
positive Gram matrix, the state-to-readout map is lossless onto that space,
whether or not the lattice is unimodular. This does not assert every ambient
integer readout is physically admissible. -/
def intrinsicReadout {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hp : (A.map (Int.cast : ℤ → ℝ)).PosDef) :
    (Fin n → ℤ) ≃ Set.range (fun z => A *ᵥ z) :=
  Equiv.ofInjective (fun z => A *ᵥ z)
    (Translation.mulVec_injective_of_det (Translation.det_ne_zero_of_posDef hp))

theorem intrinsic_readout_value {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hp : (A.map (Int.cast : ℤ → ℝ)).PosDef) (z : Fin n → ℤ) :
    (intrinsicReadout A hp z).val = A *ᵥ z := rfl

theorem intrinsic_readout_reconstructs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hp : (A.map (Int.cast : ℤ → ℝ)).PosDef) (z : Fin n → ℤ) :
    (intrinsicReadout A hp).symm (intrinsicReadout A hp z) = z :=
  (intrinsicReadout A hp).symm_apply_apply z

/-- Finite-resolution distinctions are preserved if the readout resolution
is inherited from its own image lattice. Demanding the same ambient modulus
instead is the stronger condition used to force unimodularity. -/
theorem natural_readout_congruence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hp : (A.map (Int.cast : ℤ → ℝ)).PosDef) (m : ℕ) (x y : Fin n → ℤ) :
    (∃ w, x-y = (m : ℤ) • w) ↔
    (∃ w, A *ᵥ x - A *ᵥ y = (m : ℤ) • (A *ᵥ w)) := by
  have hi := Translation.mulVec_injective_of_det (Translation.det_ne_zero_of_posDef hp)
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [← Matrix.mulVec_sub, hw, Matrix.mulVec_smul]
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    apply hi
    change A *ᵥ (x-y) = A *ᵥ ((m : ℤ) • w)
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    exact hw

/-- Conserving the cost conserves its intrinsic norm parity. No separate
external bit needs to be supplied to the state or update law. -/
theorem parity_preserved {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (F : (Fin n → ℤ) → (Fin n → ℤ))
    (h : ∀ z, F z ⬝ᵥ (A *ᵥ F z) = z ⬝ᵥ (A *ᵥ z)) (z : Fin n → ℤ) :
    parity A (F z) = parity A z := by
  unfold parity
  rw [h]

/-- A fully explicit closed reversible operation on integer labels. -/
def shift (z : ℤ) : Equiv.Perm ℤ where
  toFun := fun x => z+x
  invFun := fun x => x-z
  left_inv := by intro x; ring
  right_inv := by intro x; ring

def flip : Equiv.Perm ℤ where
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := neg_neg
  right_inv := neg_neg

theorem flip_nontrivial : flip ≠ 1 := by
  intro h
  have h1 := congrArg (fun e : Equiv.Perm ℤ => e 1) h
  norm_num [flip] at h1

theorem shift_faithful : Function.Injective shift := by
  intro a b h
  have h0 := congrArg (fun e : Equiv.Perm ℤ => e 0) h
  simpa [shift] using h0

/-- For the odd rank-one pairing B(x,y)=xy, adding the intrinsic parity
correction makes a consistent exchange law. The correction is computed from
x,y, not stored as an external state. This is an alternative law, not a claim
that the PM vacuum necessarily uses it. -/
theorem odd_lattice_reversible_exchange (x y : ℤ) :
    shift x * shift y =
      OperationalDuality.exchangeSign flip (x*y-x^2*y^2) * (shift y * shift x) := by
  have he : Even (x*y-x^2*y^2) := by
    convert integer_self_correction_even (x*y) using 1
    ring
  simp only [OperationalDuality.exchangeSign, if_pos he, one_mul]
  ext t
  simp [shift]
  ring

/-- Rank eight, positive and unimodular, yet odd. Rank and a reversible
lattice description cannot by themselves select the T symmetry. -/
def oddParent : Matrix (Fin 8) (Fin 8) ℤ := 1

def oddClockU : Fin 8 → ℤ := ![1,1,0,0,0,0,0,0]
def oddClockV : Fin 8 → ℤ := ![2,-1,4,1,0,0,0,0]

theorem rank_eight_odd_parent :
    (oddParent.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit oddParent.det ∧
      ¬ (∀ z, Even (z ⬝ᵥ (oddParent *ᵥ z))) := by
  refine ⟨?_, ?_, ?_⟩
  · have hm : oddParent.map (Int.cast : ℤ → ℝ) = 1 := by simp [oddParent]
    rw [hm]
    refine PosDef.of_dotProduct_mulVec_pos (by simp) fun x hx => ?_
    simpa using RankEight.dot_self_pos hx
  · simp [oddParent]
  · intro h
    have he := h ![1,0,0,0,0,0,0,0]
    norm_num [oddParent, dotProduct, Fin.sum_univ_succ] at he

theorem odd_parent_clock_gram :
    oddClockU ⬝ᵥ (oddParent *ᵥ oddClockU) = 2 ∧
    oddClockU ⬝ᵥ (oddParent *ᵥ oddClockV) = 1 ∧
    oddClockV ⬝ᵥ (oddParent *ᵥ oddClockV) = 22 := by decide

/-- Two standard D4 root sectors inside the odd rank-eight parent. The norm
certificate below shows that their root substructure alone does not impose
evenness on the entire parent. -/
def rootBasis : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![1,0,0,0,0,0,0,0],
    ![-1,1,0,0,0,0,0,0],
    ![0,-1,1,1,0,0,0,0],
    ![0,0,-1,1,0,0,0,0],
    ![0,0,0,0,1,0,0,0],
    ![0,0,0,0,-1,1,0,0],
    ![0,0,0,0,0,-1,1,1],
    ![0,0,0,0,0,0,-1,1]]

theorem odd_parent_two_d4_norms (w : Fin 8 → ℤ) :
    (rootBasis *ᵥ w) ⬝ᵥ (oddParent *ᵥ (rootBasis *ᵥ w)) =
      Lattices.d4Norm ![w 0,w 1,w 2,w 3] +
      Lattices.d4Norm ![w 4,w 5,w 6,w 7] := by
  simp [oddParent, rootBasis, Lattices.d4Norm, dotProduct, mulVec, Fin.sum_univ_succ]
  ring

theorem root_basis_injective : Function.Injective (fun w => rootBasis *ᵥ w) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  have h7 := congrFun h 7
  simp [rootBasis, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  funext i
  fin_cases i <;> simp_all <;> omega

/-- An index-two sublattice of E8 obtained without increasing rank. The
clock vectors have zero last coordinate and therefore survive unchanged. -/
def stretch : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.diagonal (fun i => if i = 7 then 2 else 1)

def evenParent : Matrix (Fin 8) (Fin 8) ℤ := stretchᵀ * Lattices.gram * stretch

lemma stretch_det : stretch.det = 2 := by
  norm_num [stretch, Matrix.det_diagonal, Fin.prod_univ_succ]

lemma stretch_clock_fixed :
    stretch *ᵥ ClockPlane.cu = ClockPlane.cu ∧
      stretch *ᵥ ClockPlane.cv = ClockPlane.cv := by decide

lemma stretched_pair (x y : Fin 8 → ℤ) :
    x ⬝ᵥ (evenParent *ᵥ y) =
      (stretch *ᵥ x) ⬝ᵥ (Lattices.gram *ᵥ (stretch *ᵥ y)) := by
  exact (E8Unique.B_mulVec stretch x y).symm

/-- Evenness, rank eight and the earlier clock still do not force the
self-dual S law: the rescaled integral sublattice is not unimodular. -/
theorem rank_eight_even_nonunimodular :
    (evenParent.map (Int.cast : ℤ → ℝ)).PosDef ∧
      (∀ z, Even (z ⬝ᵥ (evenParent *ᵥ z))) ∧ ¬ IsUnit evenParent.det := by
  refine ⟨?_, ?_, ?_⟩
  · let P := stretch.map (Int.cast : ℤ → ℝ)
    have hinj : Function.Injective (fun x : Fin 8 → ℝ => P *ᵥ x) := by
      intro x y h
      funext i
      have hi := congrFun h i
      simp [P, stretch, Matrix.mulVec_diagonal] at hi
      split_ifs at hi <;> linarith
    have hm : evenParent.map (Int.cast : ℤ → ℝ) =
        Pᴴ * (Lattices.gram.map (Int.cast : ℤ → ℝ)) * P := by
      ext i j
      simp [evenParent, P, Matrix.mul_apply]
    rw [hm]
    exact RankEight.e8_even_unimodular.1.conjTranspose_mul_mul_same hinj
  · intro z
    rw [stretched_pair]
    exact RankEight.e8_even_unimodular.2.1 (stretch *ᵥ z)
  · intro h
    rw [evenParent, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, stretch_det] at h
    have htwo := isUnit_of_mul_isUnit_right h
    norm_num [Int.isUnit_iff] at htwo

theorem even_parent_clock_gram :
    ClockPlane.cu ⬝ᵥ (evenParent *ᵥ ClockPlane.cu) = 2 ∧
    ClockPlane.cu ⬝ᵥ (evenParent *ᵥ ClockPlane.cv) = 1 ∧
    ClockPlane.cv ⬝ᵥ (evenParent *ᵥ ClockPlane.cv) = 22 := by
  simp only [stretched_pair, stretch_clock_fixed.1, stretch_clock_fixed.2]
  exact ClockPlane.e8_plane_gram

/-- Even rank-eight clock-compatible data can fail the scalar inversion law. -/
theorem even_parent_fails_S :
    ¬ (∀ s : ℂ, 0 < s.re →
      RankEight.theta (evenParent.map (Int.cast : ℤ → ℝ)) s =
      ((s ^ (1 / 2 : ℂ)) ^ 8)⁻¹ *
      RankEight.theta (evenParent.map (Int.cast : ℤ → ℝ)) s⁻¹) := by
  intro h
  exact rank_eight_even_nonunimodular.2.2
    ((Translation.unimodular_iff_S_covariant rank_eight_even_nonunimodular.1).mpr h)

/-- Positive unimodular rank-eight clock-compatible data can fail the unit
phase shift. The actual lattice rank and clock form are held fixed. -/
theorem odd_parent_fails_T :
    ¬ (∀ s : ℂ, 0 < s.re →
      RankEight.theta (oddParent.map (Int.cast : ℤ → ℝ)) (s - Complex.I) =
      RankEight.theta (oddParent.map (Int.cast : ℤ → ℝ)) s) := by
  intro h
  exact rank_eight_odd_parent.2.2
    ((Translation.even_iff_T_invariant rank_eight_odd_parent.1).mpr h)

end PMArch.IntrinsicConstraints
