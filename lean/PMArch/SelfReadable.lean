import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Prime.Basic

/-!
# One-bit self-readability of the closed substrate

PM postulate (Closure + Conservation): every one-bit distinction of the complete
substrate's state can be detected by a probe that is itself a substrate state,
with the outcome read at the same one-bit resolution. A state whose pairing with
every substrate probe is even is therefore twice a state.

* `bitReadable_iff_odd`: this holds exactly when the Gram determinant is odd.
* Route C (`bitAddressed_bitReadable_unimodular`): with bit-addressed glue
  (`2Λ* ⊆ Λ`), the discriminant group is both 2-torsion and free of 2-torsion,
  hence trivial: the substrate is unimodular.
* Route B (`sublattice_bitReadable_unimodular`): a finite-index sublattice whose
  Gram determinant is a power of two (e.g. `D₄ ⊕ D₄`) gives the same conclusion.

The canonical image readout (`IntrinsicConstraints.intrinsicReadout`) is lossless
for every lattice but reads outcomes at a finer resolution than the states; the
matched resolution is the physical content of this postulate.
-/

namespace PMArch.SelfReadable
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One-bit self-readability. -/
def BitReadable (A : Matrix ι ι ℤ) : Prop :=
  ∀ x : ι → ℤ, (∀ y : ι → ℤ, (2 : ℤ) ∣ x ⬝ᵥ (A *ᵥ y)) → ∃ w : ι → ℤ, x = (2 : ℤ) • w

local notation "f2" => Int.castRingHom (ZMod 2)

lemma pair_dvd_iff (A : Matrix ι ι ℤ) (x : ι → ℤ) :
    (∀ y : ι → ℤ, (2 : ℤ) ∣ x ⬝ᵥ (A *ᵥ y)) ↔ (f2 ∘ x) ᵥ* A.map f2 = 0 := by
  constructor
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at hj
    rw [← RingHom.map_vecMul]
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hj
  · intro h y
    rw [dotProduct_mulVec]
    have : ∀ j, (2 : ℤ) ∣ (x ᵥ* A) j := by
      intro j
      have hj := congrFun h j
      rw [← RingHom.map_vecMul] at hj
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hj
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (this j) _

omit [Fintype ι] [DecidableEq ι] in
lemma double_iff (x : ι → ℤ) : (∃ w : ι → ℤ, x = (2 : ℤ) • w) ↔ f2 ∘ x = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    funext i
    simp only [Function.comp, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_mul]
    have : (f2 (2 : ℤ)) = 0 := by decide
    rw [this, zero_mul]
  · intro h
    refine ⟨fun i => x i / 2, ?_⟩
    funext i
    have hi := congrFun h i
    simp only [Function.comp, Pi.zero_apply, eq_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
    simp only [Pi.smul_apply, smul_eq_mul]
    omega

theorem bitReadable_iff_odd (A : Matrix ι ι ℤ) : BitReadable A ↔ Odd A.det := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdet : f2 A.det = (A.map f2).det := RingHom.map_det f2 A
  have hodd : Odd A.det ↔ (A.map f2).det ≠ 0 := by
    rw [← hdet, ← Int.not_even_iff_odd, even_iff_two_dvd]
    simp [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [hodd, Ne, ← Matrix.exists_vecMul_eq_zero_iff]
  constructor
  · rintro hread ⟨v, hv, hvA⟩
    let x : ι → ℤ := fun i => ((v i).val : ℤ)
    have hx : f2 ∘ x = v := by
      funext i; simp [x]
    obtain ⟨w, hw⟩ := hread x ((pair_dvd_iff A x).mpr (by rw [hx]; exact hvA))
    exact hv (by rw [← hx]; exact (double_iff x).mp ⟨w, hw⟩)
  · intro hnot x hx
    rw [double_iff]
    by_contra hne
    exact hnot ⟨f2 ∘ x, hne, (pair_dvd_iff A x).mp hx⟩


lemma odd_dvd_two_pow_isUnit {d : ℤ} (hd : Odd d) {k : ℕ} (h : d ∣ 2 ^ k) : IsUnit d := by
  rw [Int.isUnit_iff_natAbs_eq]
  have h1 : d.natAbs ∣ 2 ^ k := by
    have := Int.natAbs_dvd_natAbs.mpr h
    simpa [Int.natAbs_pow] using this
  have hodd : Odd d.natAbs := Int.natAbs_odd.mpr hd
  have hcop : Nat.Coprime d.natAbs (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact Nat.Coprime.eq_one_of_dvd hcop h1

/-- **Route C.** Bit-addressed glue (`2Λ* ⊆ Λ`, i.e. `A M = 2`) together with one-bit
self-readability forces unimodularity. -/
theorem bitAddressed_bitReadable_unimodular (A M : Matrix ι ι ℤ) (hM : A * M = (2 : ℤ) • 1)
    (h : BitReadable A) : IsUnit A.det := by
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  exact odd_dvd_two_pow_isUnit ((bitReadable_iff_odd A).mp h) ⟨M.det, hdet.symm⟩

/-- **Route B.** If a sublattice of finite index has Gram determinant a power of two
(e.g. `D₄ ⊕ D₄`, determinant 16), one-bit self-readability forces unimodularity. -/
theorem sublattice_bitReadable_unimodular (A S G : Matrix ι ι ℤ) (hS : Sᵀ * A * S = G)
    {k : ℕ} (hG : G.det = 2 ^ k) (h : BitReadable A) : IsUnit A.det := by
  have hdet := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hG] at hdet
  exact odd_dvd_two_pow_isUnit ((bitReadable_iff_odd A).mp h) ⟨S.det * S.det, by rw [← hdet]; ring⟩

end PMArch.SelfReadable
