import PMArch.Research.ConstraintFoundations
import PMArch.ClockPlane
import Mathlib.Data.ZMod.Basic

/-!
# Operational tests for the missing theta symmetries

These bridges have explicit extra premises. Autonomous closure, homogeneous
updates, and conservation alone are not identified with readout completeness
or with the exchange-phase law. No physical axioms are introduced.
-/
noncomputable section
namespace PMArch.OperationalDuality
open Matrix

/-- The integer readout A z realizes every residue label modulo q. The
auxiliary integer vector records congruence, not an extra physical state. -/
def FiniteReadoutComplete {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) : Prop :=
  ∀ b : Fin n → ℤ, ∃ z w : Fin n → ℤ, A *ᵥ z + (q : ℤ) • w = b

/-- Realizing every integer readout is exactly unimodularity. A non-unit
determinant is a missing-readout obstruction, not automatically information
loss in an otherwise well-defined model. -/
theorem integer_readout_iff_unimodular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Function.Surjective (fun z => A *ᵥ z) ↔ IsUnit A.det := by
  rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]

/-- Completeness at the intrinsic determinant modulus suffices. Positive
definiteness ensures that modulus is nonzero. This is a substantive additional
readout requirement; closure does not assert it. -/
theorem intrinsic_readout_iff_unimodular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hp : (A.map (Int.cast : ℤ → ℝ)).PosDef) :
    FiniteReadoutComplete A A.det.natAbs ↔ IsUnit A.det := by
  have hd : 0 < A.det := by
    have h := hp.det_pos
    have he : ((A.det : ℤ) : ℝ) = (A.map (Int.cast : ℤ → ℝ)).det :=
      RingHom.map_det (Int.castRingHom ℝ) A
    rw [← he] at h
    exact_mod_cast h
  have hc : (A.det.natAbs : ℤ) = A.det := by
    rw [Int.natCast_natAbs, abs_of_pos hd]
  constructor
  · intro hread
    apply (integer_readout_iff_unimodular A).mp
    intro b
    obtain ⟨z, w, hw⟩ := hread b
    refine ⟨z + A.adjugate *ᵥ w, ?_⟩
    change A *ᵥ (z + A.adjugate *ᵥ w) = b
    have ha : A *ᵥ (A.adjugate *ᵥ w) = A.det • w := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate]
      simp
    rw [Matrix.mulVec_add, ha]
    simpa only [hc] using hw
  · intro hdet b
    obtain ⟨z, hz⟩ := (integer_readout_iff_unimodular A).mpr hdet b
    exact ⟨z, 0, by simpa using hz⟩

/-- All positive finite resolutions give an operational characterization of
unimodularity. This quantifier is stronger than one fixed finite clock. -/
theorem all_finite_readouts_iff_unimodular {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hp : (A.map (Int.cast : ℤ → ℝ)).PosDef) :
    (∀ q : ℕ, 0 < q → FiniteReadoutComplete A q) ↔ IsUnit A.det := by
  constructor
  · intro h
    apply (intrinsic_readout_iff_unimodular A hp).mp
    exact h A.det.natAbs (Int.natAbs_pos.mpr (Translation.det_ne_zero_of_posDef hp))
  · intro hd q _ b
    obtain ⟨z, hz⟩ := (integer_readout_iff_unimodular A).mpr hd b
    exact ⟨z, 0, by simpa using hz⟩

/-- The fixed 43-state clock cannot rule out the determinant-two readout:
22 is the inverse of 2 modulo 43. The readout still fails at modulus 2. -/
theorem determinant_two_fixed_clock :
    (∀ b : ℤ, ∃ z w : ℤ, 2*z + 43*w = b) ∧
    ¬ (∀ b : ℤ, ∃ z w : ℤ, 2*z + 2*w = b) := by
  constructor
  · intro b
    exact ⟨22*b, -b, by ring⟩
  · intro h
    obtain ⟨z, w, hw⟩ := h 1
    omega

/-- Fixed-clock readout by multiplication by two is injective and surjective
on ZMod 43, despite the corresponding integral determinant being two. -/
theorem two_mod_43_lossless :
    Function.Bijective (fun x : ZMod 43 => 2*x) := by
  have hinv : (2 : ZMod 43) * 22 = 1 := by decide
  constructor
  · intro a b h
    have h' := congrArg (fun x : ZMod 43 => 22*x) h
    have hi : (22 : ZMod 43) * 2 = 1 := by decide
    simpa only [← mul_assoc, hi, one_mul] using h'
  · intro b
    refine ⟨22*b, ?_⟩
    change (2 : ZMod 43) * (22*b) = b
    rw [← mul_assoc, hinv, one_mul]

/-- A larger even parent retains the actual E8 clock plane but need not be
unimodular. This tests the embedded-clock requirement, not only an arbitrary
43-state counter. -/
def clockParent : Matrix (Fin 8 ⊕ Fin 1) (Fin 8 ⊕ Fin 1) ℤ :=
  Matrix.fromBlocks Lattices.gram 0 0 !![2]

lemma clock_parent_split {R : Type*} [CommRing R]
    (A : Matrix (Fin 8) (Fin 8) R) (x y : Fin 8 ⊕ Fin 1 → R) :
    x ⬝ᵥ (Matrix.fromBlocks A 0 0 !![2] *ᵥ y) =
      (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (y ∘ Sum.inl)) +
      2*x (Sum.inr 0)*y (Sum.inr 0) := by
  simp [dotProduct, mulVec, Fintype.sum_sum_type]
  ring

theorem clock_parent_positive_even_nonunimodular :
    (clockParent.map (Int.cast : ℤ → ℝ)).PosDef ∧
    (∀ z, Even (z ⬝ᵥ (clockParent *ᵥ z))) ∧ ¬ IsUnit clockParent.det := by
  have hp := RankEight.e8_even_unimodular.1
  have hm : clockParent.map (Int.cast : ℤ → ℝ) =
      Matrix.fromBlocks (Lattices.gram.map (Int.cast : ℤ → ℝ)) 0 0 !![2] := by
    ext i j
    cases i <;> cases j <;> simp [clockParent]
  refine ⟨?_, ?_, ?_⟩
  · rw [hm]
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · simp only [IsHermitian, fromBlocks_conjTranspose, conjTranspose_zero]
      rw [hp.1]
      have hb : (!![2] : Matrix (Fin 1) (Fin 1) ℝ)ᴴ = !![2] := by
        ext i j
        fin_cases i
        fin_cases j
        norm_num
      rw [hb]
    · simp only [star_trivial]
      rw [clock_parent_split]
      by_cases hleft : x ∘ Sum.inl = 0
      · have hr : x (Sum.inr 0) ≠ 0 := by
          intro hzero
          apply hx
          ext i
          cases i with
          | inl j => exact congrFun hleft j
          | inr j => have : j = 0 := Subsingleton.elim _ _; subst j; exact hzero
        have hs : 0 < (x (Sum.inr 0))^2 := sq_pos_of_ne_zero hr
        simp only [hleft, zero_dotProduct]
        nlinarith
      · have hl := hp.dotProduct_mulVec_pos hleft
        simp only [star_trivial] at hl
        nlinarith [sq_nonneg (x (Sum.inr 0))]
  · intro z
    rw [clockParent, clock_parent_split]
    obtain ⟨k, hk⟩ := Lattices.even_norm (z ∘ Sum.inl)
    refine ⟨k + z (Sum.inr 0)*z (Sum.inr 0), ?_⟩
    change (z ∘ Sum.inl) ⬝ᵥ (Lattices.gram *ᵥ (z ∘ Sum.inl)) = 2*k at hk
    rw [hk]
    ring
  · intro hunit
    rw [clockParent, Matrix.det_fromBlocks_zero₂₁] at hunit
    have htwo := isUnit_of_mul_isUnit_right hunit
    norm_num [Int.isUnit_iff] at htwo

/-- The determinant-43 plane is unchanged in E8 plus A1. Its existence cannot
by itself force unimodularity of the whole parent. -/
theorem augmented_clock_gram :
    let u : Fin 8 ⊕ Fin 1 → ℤ := Sum.elim ClockPlane.cu (fun _ => 0)
    let v : Fin 8 ⊕ Fin 1 → ℤ := Sum.elim ClockPlane.cv (fun _ => 0)
    u ⬝ᵥ (clockParent *ᵥ u) = 2 ∧
      u ⬝ᵥ (clockParent *ᵥ v) = 1 ∧ v ⬝ᵥ (clockParent *ᵥ v) = 22 := by
  dsimp
  simp only [clockParent, clock_parent_split, Sum.elim_inr, mul_zero, add_zero]
  simpa only [Function.comp_def, Sum.elim_inl] using ClockPlane.e8_plane_gram

/-- An autonomous pointwise reflection commutes with every relabeling of
sites. Thus the earlier reflection counterexamples do not rely on an
inhomogeneous local rule; the value update is identical at every site. -/
theorem reflection_is_homogeneous {I : Type*} {n : ℕ}
    (relabel : Equiv.Perm I) (field : I → (Fin n → ℤ)) :
    (fun i => ConstraintFoundations.reflect (field (relabel i))) =
    (fun i => (fun j => ConstraintFoundations.reflect (field j)) (relabel i)) := by
  rfl

theorem pointwise_reflection_reversible {I : Type*} {n : ℕ}
    (field : I → (Fin n → ℤ)) :
    (fun i => ConstraintFoundations.reflect (ConstraintFoundations.reflect (field i))) =
      field := by
  funext i
  exact ConstraintFoundations.reflect.left_inv (field i)

/-- Ordinary basis/relabeling invariance is reindexing of the same state sum.
It holds whenever the costs match, without evenness or self-duality. It must
not be confused with changing the complex theta parameter by T or S. -/
theorem theta_relabel_invariant {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ)
    (e : (Fin n → ℤ) ≃ (Fin n → ℤ))
    (hq : ∀ z, z ⬝ᵥ (A *ᵥ z) = e z ⬝ᵥ (B *ᵥ e z)) (s : ℂ) :
    RankEight.theta (A.map (Int.cast : ℤ → ℝ)) s =
    RankEight.theta (B.map (Int.cast : ℤ → ℝ)) s := by
  unfold RankEight.theta
  calc
    _ = ∑' z : Fin n → ℤ,
        Complex.exp (-Real.pi * s *
          (RankEight.qf (B.map (Int.cast : ℤ → ℝ)) (RankEight.vcast (e z)) : ℂ)) := by
      apply tsum_congr
      intro z
      rw [RankEight.qf_cast, RankEight.qf_cast, hq]
    _ = _ := e.tsum_eq (fun z : Fin n → ℤ =>
      Complex.exp (-Real.pi * s *
        (RankEight.qf (B.map (Int.cast : ℤ → ℝ)) (RankEight.vcast z) : ℂ)))

/-- A normalized two-sector transform can be lossless and self-inverse.
This is a finite algebra certificate, not a proof of theta covariance or a
construction of a quantum vacuum. Multiple internal sectors need not require
an external controller or incur information loss. -/
def sectorMix (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![r, r; r, -r]

theorem sector_mix_self_inverse (r : ℝ) (hr : r*r = 1/2) :
    sectorMix r * sectorMix r = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sectorMix, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

theorem normalized_sector_mix_exists :
    ∃ r : ℝ, sectorMix r * sectorMix r = 1 ∧
      (sectorMix r)ᵀ * sectorMix r = 1 := by
  let r : ℝ := Real.sqrt 2 / 2
  have hr : r*r = 1/2 := by
    dsimp [r]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hs : (sectorMix r)ᵀ = sectorMix r := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  exact ⟨r, sector_mix_self_inverse r hr, by rw [hs]; exact sector_mix_self_inverse r hr⟩

/-- A candidate parity exchange phase, explicitly stated. Selecting this
rather than a trivial or differently normalized phase is a physical premise. -/
def exchangeSign {G : Type*} [Group G] (ε : G) (k : ℤ) : G :=
  if Even k then 1 else ε

/-- Invertible operations cannot anticommute with themselves. Therefore an
exchange law whose sign is norm parity forces even norms. Neither the sign law
nor the operator realization is derived from the existing PM postulates. -/
theorem parity_exchange_forces_even {G : Type*} [Group G] (ε : G) (hε : ε ≠ 1)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (U : (Fin n → ℤ) → G)
    (hexchange : ∀ x y, U x * U y =
      exchangeSign ε (x ⬝ᵥ (A *ᵥ y)) * (U y * U x)) :
    ∀ z : Fin n → ℤ, Even (z ⬝ᵥ (A *ᵥ z)) := by
  intro z
  have h := hexchange z z
  have hphase : exchangeSign ε (z ⬝ᵥ (A *ᵥ z)) = 1 := by
    apply mul_right_cancel (b := U z * U z)
    simpa using h.symm
  by_contra hodd
  exact hε (by simpa [exchangeSign, hodd] using hphase)

/-- Scalar evenness and self-duality emerge from these operational premises.
Their independent physical necessity remains open. The resulting theta laws
are obtained via the previously proved equivalences, not assumed here. -/
theorem operational_premises_select_e8 {G : Type*} [Group G]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hsym : A.IsSymm)
    (hfinite : ∀ c : ℤ, ({z : Fin n → ℤ | z ⬝ᵥ (A *ᵥ z) ≤ c}).Finite)
    (ε : G) (hε : ε ≠ 1) (U : (Fin n → ℤ) → G)
    (hexchange : ∀ x y, U x * U y =
      exchangeSign ε (x ⬝ᵥ (A *ᵥ y)) * (U y * U x))
    (hreadout : FiniteReadoutComplete A A.det.natAbs)
    (hn : 0 < n) (hminimal : ClaimBoundary.MinimalRank n) : ClaimBoundary.IsE8 A := by
  have hp := (Translation.posDef_iff_finite_levels hsym).mpr hfinite
  have he := parity_exchange_forces_even ε hε A U hexchange
  have hd := (intrinsic_readout_iff_unimodular A hp).mp hreadout
  exact ClaimBoundary.state_sum_selects_e8 A hsym hfinite
    ((Translation.even_iff_T_invariant hp).mp he)
    ((Translation.unimodular_iff_S_covariant hp).mp hd) hn hminimal

end PMArch.OperationalDuality
