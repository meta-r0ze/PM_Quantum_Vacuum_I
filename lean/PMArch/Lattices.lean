import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Explicit integral E8 and D4 ⊕ D4 coordinate models.
The construction does not assert uniqueness among all rank-eight lattices. -/
set_option maxRecDepth 10000

noncomputable section
namespace PMArch.Lattices
open Matrix

def gram : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![2, 0, (-1), 0, 0, 0, 0, 0],
  ![0, 2, 0, (-1), 0, 0, 0, 0],
  ![(-1), 0, 2, (-1), 0, 0, 0, 0],
  ![0, (-1), (-1), 2, (-1), 0, 0, 0],
  ![0, 0, 0, (-1), 2, (-1), 0, 0],
  ![0, 0, 0, 0, (-1), 2, (-1), 0],
  ![0, 0, 0, 0, 0, (-1), 2, (-1)],
  ![0, 0, 0, 0, 0, 0, (-1), 2]]

def gramInverse : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![4, 5, 7, 10, 8, 6, 4, 2],
  ![5, 8, 10, 15, 12, 9, 6, 3],
  ![7, 10, 14, 20, 16, 12, 8, 4],
  ![10, 15, 20, 30, 24, 18, 12, 6],
  ![8, 12, 16, 24, 20, 15, 10, 5],
  ![6, 9, 12, 18, 15, 12, 8, 4],
  ![4, 6, 8, 12, 10, 8, 6, 3],
  ![2, 3, 4, 6, 5, 4, 3, 2]]

def d4Embedding : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![0, 0, 0, 0, 0, 0, (-2), 2],
  ![0, 0, 0, 1, 0, 0, (-2), 3],
  ![(-1), 0, 0, 1, 0, 0, (-3), 4],
  ![0, (-1), 0, 2, 0, 0, (-4), 6],
  ![0, 0, (-1), 1, 0, 0, (-3), 5],
  ![0, 0, 0, 0, 0, 0, (-2), 4],
  ![0, 0, 0, 0, (-1), 0, (-1), 3],
  ![0, 0, 0, 0, 0, (-1), 0, 2]]

theorem gram_inverse : gramInverse * gram = 1 := by
  decide

theorem gram_symmetric : gram.transpose = gram := by
  decide

def pairing (x y : Fin 8 → ℤ) : ℤ := dotProduct x (gram *ᵥ y)

theorem even_norm (z : Fin 8 → ℤ) : ∃ k : ℤ, pairing z z = 2 * k := by
  refine ⟨(z 0)^2 + (z 1)^2 + (z 2)^2 + (z 3)^2 + (z 4)^2 + (z 5)^2 + (z 6)^2 + (z 7)^2 - z 0 * z 2 - z 1 * z 3 - z 2 * z 3 - z 3 * z 4 - z 4 * z 5 - z 5 * z 6 - z 6 * z 7, ?_⟩
  simp [pairing, gram, dotProduct, mulVec, Fin.sum_univ_succ]
  ring

/-- Every real vector with integral pairings has integral coordinates. -/
theorem integral_dual (x : Fin 8 → ℝ)
    (h : ∀ i, ∃ z : ℤ, ((gram.map (Int.castRingHom ℝ)) *ᵥ x) i = z) :
    ∃ z : Fin 8 → ℤ, ∀ i, x i = z i := by
  choose z hz using h
  refine ⟨gramInverse *ᵥ z, ?_⟩
  intro i
  have hi := congrFun (congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M *ᵥ x)
    (show (gramInverse.map (Int.castRingHom ℝ)) * (gram.map (Int.castRingHom ℝ)) = 1 by
      rw [← Matrix.map_mul, gram_inverse]
      simp)) i
  change (((gramInverse.map (Int.castRingHom ℝ)) *
    (gram.map (Int.castRingHom ℝ))) *ᵥ x) i = (1 *ᵥ x) i at hi
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at hi
  rw [← hi]
  have hz' : (gram.map (Int.castRingHom ℝ)) *ᵥ x = fun j => (z j : ℝ) := funext hz
  rw [hz']
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) gramInverse z i).symm


theorem positive_norm (z : Fin 8 → ℤ) (hz : z ≠ 0) : 0 < pairing z z := by
  let a0 : ℤ := (1) * z 0 + (2) * z 1 + (-2) * z 2
  let a1 : ℤ := (-1) * z 0 + (2) * z 1 + (2) * z 2 + (-2) * z 3
  let a2 : ℤ := (-1) * z 0 + (2) * z 3 + (-2) * z 4
  let a3 : ℤ := (-1) * z 0 + (2) * z 4 + (-2) * z 5
  let a4 : ℤ := (-1) * z 0 + (2) * z 5 + (-2) * z 6
  let a5 : ℤ := (-1) * z 0 + (2) * z 6 + (-2) * z 7
  let a6 : ℤ := (-1) * z 0 + (2) * z 7
  let a7 : ℤ := (1) * z 0
  have heq : 4 * pairing z z = a0^2 + a1^2 + a2^2 + a3^2 + a4^2 + a5^2 + a6^2 + a7^2 := by
    simp [pairing, gram, dotProduct, mulVec, Fin.sum_univ_succ, a0, a1, a2, a3, a4, a5, a6, a7]
    ring
  by_contra h
  have hn : pairing z z ≤ 0 := by omega
  have hs0 := sq_nonneg a0
  have hs1 := sq_nonneg a1
  have hs2 := sq_nonneg a2
  have hs3 := sq_nonneg a3
  have hs4 := sq_nonneg a4
  have hs5 := sq_nonneg a5
  have hs6 := sq_nonneg a6
  have hs7 := sq_nonneg a7
  have h0 : a0 = 0 := by
    have hs : a0^2 = 0 := by omega
    exact sq_eq_zero_iff.mp hs
  have h1 : a1 = 0 := by
    have hs : a1^2 = 0 := by omega
    exact sq_eq_zero_iff.mp hs
  have h2 : a2 = 0 := by
    have hs : a2^2 = 0 := by omega
    exact sq_eq_zero_iff.mp hs
  have h3 : a3 = 0 := by
    have hs : a3^2 = 0 := by omega
    exact sq_eq_zero_iff.mp hs
  have h4 : a4 = 0 := by
    have hs : a4^2 = 0 := by omega
    exact sq_eq_zero_iff.mp hs
  have h5 : a5 = 0 := by
    have hs : a5^2 = 0 := by omega
    exact sq_eq_zero_iff.mp hs
  have h6 : a6 = 0 := by
    have hs : a6^2 = 0 := by omega
    exact sq_eq_zero_iff.mp hs
  have h7 : a7 = 0 := by
    have hs : a7^2 = 0 := by omega
    exact sq_eq_zero_iff.mp hs
  apply hz
  ext i
  fin_cases i <;> simp only [Pi.zero_apply] <;> dsimp [a0, a1, a2, a3, a4, a5, a6, a7] at * <;> linarith

/-- The two residue coordinates distinguish the four D4 ⊕ D4 glue classes. -/
def glueCode (z : Fin 8 → ℤ) : ZMod 2 × ZMod 2 := (z 0, z 5)

theorem glue_surjective : Function.Surjective glueCode := by
  intro p
  refine ⟨![p.1.val, 0, 0, 0, 0, p.2.val, 0, 0], ?_⟩
  simp [glueCode]

theorem four_glue_labels : Fintype.card (ZMod 2 × ZMod 2) = 4 := by decide

theorem d4_range_iff (z : Fin 8 → ℤ) :
    (∃ w, d4Embedding *ᵥ w = z) ↔ (2 ∣ z 0 ∧ 2 ∣ z 5) := by
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · refine ⟨-w 6 + w 7, ?_⟩
      simp [d4Embedding, mulVec, dotProduct, Fin.sum_univ_succ]
      ring
    · refine ⟨-w 6 + 2 * w 7, ?_⟩
      simp [d4Embedding, mulVec, dotProduct, Fin.sum_univ_succ]
      ring
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨![a + z 1 - z 2, 2 * z 1 - z 3, z 1 - z 4 + b,
      -a + z 1 - b, -a + 2 * b - z 6, -2 * a + 2 * b - z 7,
      -2 * a + b, -a + b], ?_⟩
    ext i
    fin_cases i <;> simp [d4Embedding, mulVec, dotProduct, Fin.sum_univ_succ, ha, hb]
    <;> ring

theorem glue_kernel (z : Fin 8 → ℤ) :
    glueCode z = 0 ↔ ∃ w, d4Embedding *ᵥ w = z := by
  rw [d4_range_iff]
  change ((z 0 : ZMod 2), (z 5 : ZMod 2)) = (0, 0) ↔ _
  rw [Prod.mk.injEq]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat]

theorem d4_code_zero (w : Fin 8 → ℤ) : glueCode (d4Embedding *ᵥ w) = 0 :=
  (glue_kernel _).mpr ⟨w, rfl⟩

/-- Squared norm for the conventional simple-root basis of D4. -/
def d4Norm (w : Fin 4 → ℤ) : ℤ :=
  2 * ((w 0)^2 + (w 1)^2 + (w 2)^2 + (w 3)^2 -
    w 0 * w 1 - w 1 * w 2 - w 1 * w 3)

theorem d4_direct_sum_norm (w : Fin 8 → ℤ) :
    pairing (d4Embedding *ᵥ w) (d4Embedding *ᵥ w) =
      d4Norm ![w 0, w 1, w 2, w 3] + d4Norm ![w 4, w 5, w 6, w 7] := by
  simp [pairing, gram, d4Embedding, d4Norm, dotProduct, mulVec, Fin.sum_univ_succ]
  ring

private theorem det_unit_of_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℤ) (h : B * A = 1) : IsUnit A.det := by
  apply isUnit_iff_dvd_one.mpr
  refine ⟨B.det, ?_⟩
  rw [mul_comm, ← Matrix.det_mul, h, Matrix.det_one]

theorem gram_unimodular : IsUnit gram.det :=
  det_unit_of_inverse gram gramInverse gram_inverse

def glueHom : (Fin 8 → ℤ) →+ ZMod 2 × ZMod 2 where
  toFun := glueCode
  map_zero' := by simp [glueCode]
  map_add' := by intros; ext <;> simp [glueCode]

def d4Pair : AddSubgroup (Fin 8 → ℤ) := glueHom.ker

theorem mem_d4Pair (z : Fin 8 → ℤ) : z ∈ d4Pair ↔ ∃ w, d4Embedding *ᵥ w = z :=
  glue_kernel z

def glueEquiv : ((Fin 8 → ℤ) ⧸ d4Pair) ≃+ (ZMod 2 × ZMod 2) :=
  QuotientAddGroup.quotientKerEquivOfSurjective glueHom glue_surjective

theorem four_glue_cosets : Nat.card ((Fin 8 → ℤ) ⧸ d4Pair) = 4 := by
  rw [Nat.card_congr glueEquiv.toEquiv, Nat.card_eq_fintype_card]
  exact four_glue_labels

def realPairing (x y : Fin 8 → ℝ) : ℝ :=
  dotProduct x ((gram.map (Int.castRingHom ℝ)) *ᵥ y)

theorem real_pairing_cast (z w : Fin 8 → ℤ) :
    realPairing (fun i => (z i : ℝ)) (fun i => (w i : ℝ)) = (pairing z w : ℝ) := by
  simp [realPairing, pairing, dotProduct, mulVec, Matrix.map_apply]

/-- The dual in the ambient real vector space is exactly the integral lattice. -/
theorem self_dual (x : Fin 8 → ℝ) :
    (∀ w : Fin 8 → ℤ, ∃ n : ℤ, realPairing (fun i => (w i : ℝ)) x = n) ↔
      ∃ z : Fin 8 → ℤ, ∀ i, x i = z i := by
  constructor
  · intro h
    apply integral_dual x
    intro i
    obtain ⟨n, hn⟩ := h (Pi.single i 1)
    refine ⟨n, ?_⟩
    have hs : (fun j : Fin 8 => ((Pi.single i (1 : ℤ) : Fin 8 → ℤ) j : ℝ)) =
        (Pi.single i (1 : ℝ) : Fin 8 → ℝ) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [hs, realPairing, single_dotProduct, one_mul] at hn
    exact hn
  · rintro ⟨z, hz⟩ w
    refine ⟨pairing w z, ?_⟩
    rw [show x = fun i => (z i : ℝ) from funext hz, real_pairing_cast]

theorem real_positive_norm (z : Fin 8 → ℝ) (hz : z ≠ 0) : 0 < realPairing z z := by
  let a0 : ℝ := (1) * z 0 + (2) * z 1 + (-2) * z 2
  let a1 : ℝ := (-1) * z 0 + (2) * z 1 + (2) * z 2 + (-2) * z 3
  let a2 : ℝ := (-1) * z 0 + (2) * z 3 + (-2) * z 4
  let a3 : ℝ := (-1) * z 0 + (2) * z 4 + (-2) * z 5
  let a4 : ℝ := (-1) * z 0 + (2) * z 5 + (-2) * z 6
  let a5 : ℝ := (-1) * z 0 + (2) * z 6 + (-2) * z 7
  let a6 : ℝ := (-1) * z 0 + (2) * z 7
  let a7 : ℝ := (1) * z 0
  have heq : 4 * realPairing z z = a0^2 + a1^2 + a2^2 + a3^2 + a4^2 + a5^2 + a6^2 + a7^2 := by
    simp only [realPairing, dotProduct, mulVec, Matrix.map_apply, Fin.sum_univ_succ]
    simp [gram, a0, a1, a2, a3, a4, a5, a6, a7]
    ring
  by_contra h
  have hn : realPairing z z ≤ 0 := by linarith
  have hs0 := sq_nonneg a0
  have hs1 := sq_nonneg a1
  have hs2 := sq_nonneg a2
  have hs3 := sq_nonneg a3
  have hs4 := sq_nonneg a4
  have hs5 := sq_nonneg a5
  have hs6 := sq_nonneg a6
  have hs7 := sq_nonneg a7
  have h0 : a0 = 0 := by
    have hs : a0^2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hs
  have h1 : a1 = 0 := by
    have hs : a1^2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hs
  have h2 : a2 = 0 := by
    have hs : a2^2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hs
  have h3 : a3 = 0 := by
    have hs : a3^2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hs
  have h4 : a4 = 0 := by
    have hs : a4^2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hs
  have h5 : a5 = 0 := by
    have hs : a5^2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hs
  have h6 : a6 = 0 := by
    have hs : a6^2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hs
  have h7 : a7 = 0 := by
    have hs : a7^2 = 0 := by linarith
    exact sq_eq_zero_iff.mp hs
  apply hz
  ext i
  fin_cases i <;> simp only [Pi.zero_apply] <;> dsimp [a0, a1, a2, a3, a4, a5, a6, a7] at * <;> linarith

def d4Roots (w : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![w 0, -w 0 + w 1, -w 1 + w 2 + w 3, -w 2 + w 3]

theorem d4_norm_euclidean (w : Fin 4 → ℤ) :
    d4Norm w = ∑ i, (d4Roots w i)^2 := by
  simp [d4Norm, d4Roots, Fin.sum_univ_succ]
  ring

/-- The D4 root lattice is precisely the integer vectors with even coordinate sum. -/
theorem d4_roots_range (x : Fin 4 → ℤ) :
    (∃ w, d4Roots w = x) ↔ 2 ∣ ∑ i, x i := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w 3, ?_⟩
    simp [d4Roots, Fin.sum_univ_succ]
    ring
  · rintro ⟨a, ha⟩
    refine ⟨![x 0, x 0 + x 1, a - x 3, a], ?_⟩
    simp [Fin.sum_univ_succ] at ha
    ext i
    fin_cases i <;> simp [d4Roots]; omega

end PMArch.Lattices
