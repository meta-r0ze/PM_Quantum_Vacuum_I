import PMArch.Parity
import PMArch.RankEight

/-!
# Orthogonal exchange locality: checking the independent research proposal

The evenness theorem is inspired by Claude's supplied research note. The proof
uses an explicit orthogonal integer combination, avoiding factorization through
an ideal. Orthogonal exchange locality and nontrivial exchange remain extra
physical premises; metric orthogonality is not identified with causal separation.
-/
noncomputable section
namespace PMArch.OrthogonalExchange
open Matrix

abbrev Label (n : ℕ) := Fin n → ℤ
abbrev Exchange (n : ℕ) := Label n →ₗ[ℤ] Label n →ₗ[ℤ] ZMod 2

/-- An alternating bi-additive exchange form, already abstracted from an
operator construction. The group/Weyl-to-bilinear construction is not assumed
to follow from PM; the physical applicability is a separate obligation. -/
def Alternating {n : ℕ} (C : Exchange n) : Prop := ∀ x, C x x = 0

def OrthogonalLocal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (C : Exchange n) : Prop := ∀ x y, x ⬝ᵥ (A *ᵥ y) = 0 → C x y = 0

/-- If Q(v) is odd, form w=Q(v) z-B(v,z) v. It is B-orthogonal to v.
Locality and alternation then give Q(v) C(v,z)=0, hence C(v,z)=0 modulo two. -/
theorem odd_row_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (C : Exchange n) (halt : Alternating C) (hloc : OrthogonalLocal A C)
    (v : Label n) (hv : IntrinsicConstraints.parity A v = 1) : ∀ z, C v z = 0 := by
  intro z
  let q : ℤ := v ⬝ᵥ (A *ᵥ v)
  let b : ℤ := v ⬝ᵥ (A *ᵥ z)
  have ho : v ⬝ᵥ (A *ᵥ (q • z - b • v)) = 0 := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    dsimp [q, b]
    ring
  have hc := hloc v (q • z - b • v) ho
  rw [map_sub, map_smul, map_smul, halt v, smul_zero, sub_zero] at hc
  have hq : (q : ZMod 2) = 1 := hv
  simpa only [zsmul_eq_mul, hq, one_mul] using hc

/-- One odd norm makes the entire exchange form trivial. Symmetry of A is
needed only for additivity of norm parity; no positive-definiteness,
unimodularity, rank bound or assumed sign matching is used. -/
theorem odd_norm_trivializes_exchange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm) (C : Exchange n) (halt : Alternating C)
    (hloc : OrthogonalLocal A C) (y : Label n)
    (hy : IntrinsicConstraints.parity A y = 1) : C = 0 := by
  have hyrow := odd_row_zero A C halt hloc y hy
  have hcases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro z
  change C x z = 0
  by_cases hx : IntrinsicConstraints.parity A x = 0
  · have hsum : IntrinsicConstraints.parity A (x+y) = 1 := by
      rw [IntrinsicConstraints.parity_add A hs, hx, hy, zero_add]
    have hr := odd_row_zero A C halt hloc (x+y) hsum z
    have hadd : C (x+y) z = C x z + C y z := by simp
    rw [hadd, hyrow z, add_zero] at hr
    exact hr
  · exact odd_row_zero A C halt hloc x ((hcases _).resolve_left hx) z

/-- Claude's proposed sufficient evenness criterion, with a direct proof.
The commutator form must be alternating and bi-additive, orthogonal pairs
must commute, and the exchange form must be nontrivial. These conditions are
not derived from the existing persistence postulates in this theorem. -/
theorem orthogonal_nontrivial_exchange_forces_even {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hs : A.IsSymm)
    (C : Exchange n) (halt : Alternating C) (hloc : OrthogonalLocal A C)
    (hnonzero : C ≠ 0) : ∀ z, Even (z ⬝ᵥ (A *ᵥ z)) := by
  intro z
  by_contra he
  have hp : IntrinsicConstraints.parity A z ≠ 0 := by
    intro hz
    have hd : (2 : ℤ) ∣ z ⬝ᵥ (A *ᵥ z) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
    exact he (even_iff_two_dvd.mpr hd)
  have hcases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  exact hnonzero (odd_norm_trivializes_exchange A hs C halt hloc z
    ((hcases _).resolve_left hp))

/-- The abstract exchange form obtained by reducing the pairing modulo two.
Used as an algebraic consistency witness, not selected as the physical law. -/
def pairingExchange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Exchange n where
  toFun := fun x => {
    toFun := fun y => ((x ⬝ᵥ (A *ᵥ y) : ℤ) : ZMod 2)
    map_add' := by intro y z; simp [Matrix.mulVec_add, dotProduct_add]
    map_smul' := by
      intro a y
      change ((x ⬝ᵥ (A *ᵥ (a • y)) : ℤ) : ZMod 2) =
        a • ((x ⬝ᵥ (A *ᵥ y) : ℤ) : ZMod 2)
      rw [Matrix.mulVec_smul, dotProduct_smul]
      simp [zsmul_eq_mul] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change (((x+y) ⬝ᵥ (A *ᵥ z) : ℤ) : ZMod 2) =
      ((x ⬝ᵥ (A *ᵥ z) : ℤ) : ZMod 2) + ((y ⬝ᵥ (A *ᵥ z) : ℤ) : ZMod 2)
    simp [add_dotProduct]
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro z
    change (((a • x) ⬝ᵥ (A *ᵥ z) : ℤ) : ZMod 2) =
      a • ((x ⬝ᵥ (A *ᵥ z) : ℤ) : ZMod 2)
    rw [smul_dotProduct]
    simp [zsmul_eq_mul]

/-- The sufficient premises are consistent at the exchange-form level on E8.
This is not a constructed Hamiltonian, operator representation or proof of
physical necessity. -/
theorem e8_exchange_form_witness :
    ∃ C : Exchange 8, Alternating C ∧ OrthogonalLocal Lattices.gram C ∧ C ≠ 0 := by
  refine ⟨pairingExchange Lattices.gram, ?_, ?_, ?_⟩
  · intro x
    change ((x ⬝ᵥ (Lattices.gram *ᵥ x) : ℤ) : ZMod 2) = 0
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr
    exact even_iff_two_dvd.mp (RankEight.e8_even_unimodular.2.1 x)
  · intro x y h
    change ((x ⬝ᵥ (Lattices.gram *ᵥ y) : ℤ) : ZMod 2) = 0
    simp [h]
  · intro h
    have hh := congrArg (fun C : Exchange 8 =>
      C ![1,0,0,0,0,0,0,0] ![0,0,1,0,0,0,0,0]) h
    norm_num [pairingExchange, Lattices.gram, dotProduct, mulVec, Fin.sum_univ_succ] at hh

end PMArch.OrthogonalExchange
