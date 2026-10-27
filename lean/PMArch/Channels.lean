import PMArch.Lattices

/-!
# Sectors and channels from the lattice

* `e8_two_d4_sectors`: `E₈` contains two orthogonal `D₄` root sectors (Postulate B; the sector
  type `D₄` is forced among rank-4 root sectors by `Sectors.sector_selection`).
* A **channel** is a nontrivial glue class of a sector (an element of `D₄*/D₄ ≅ (ℤ/2)²`); its
  **capacity** is its number of minimal, least-cost vectors. `minimal_class_card`: each of the
  three nontrivial classes (vector, spinor, conjugate spinor) has exactly 8. This replaces the
  appeal to `Spin(8)` representation dimensions by a lattice count.
* Directional flow uses two distinct classes (input, output): `ν = 16`, and two sectors give
  `N = 32` (`channel_total`), whichever two classes are chosen.
-/

namespace PMArch.Channels
open Matrix

/-- Doubled coordinates `y = 2x` of the dual `D₄* = ℤ⁴ ∪ (ℤ⁴ + ½)` of `D₄ = {x ∈ ℤ⁴ : Σx even}`,
restricted to the box `|yᵢ| ≤ 2`, encoded by `k ↦ k - 2`. -/
def boxVec (k : Fin 4 → Fin 5) : Fin 4 → ℤ := fun i => (k i : ℤ) - 2

/-- Glue class of a doubled dual vector: 0 = `D₄`, 1 = vector, 2 = spinor, 3 = conjugate spinor,
4 = not in the dual. -/
def glueClass (y : Fin 4 → ℤ) : ℕ :=
  if (∀ i, Even (y i)) then (if Even ((∑ i, y i) / 2) then 0 else 1)
  else if (∀ i, Odd (y i)) then (if (∑ i, y i) % 4 = 0 then 2 else 3)
  else 4

def norm4 (y : Fin 4 → ℤ) : ℤ := ∑ i, y i ^ 2

/-- Number of minimal (norm-one, i.e. `|y|² = 4`) vectors in glue class `c`. -/
def minimalCount (c : ℕ) : ℕ :=
  (Finset.univ.filter fun k : Fin 4 → Fin 5 => glueClass (boxVec k) = c ∧ norm4 (boxVec k) = 4).card

theorem minimal_vector : minimalCount 1 = 8 := by decide
theorem minimal_spinor : minimalCount 2 = 8 := by decide
theorem minimal_cospinor : minimalCount 3 = 8 := by decide

lemma boxVec_injective : Function.Injective boxVec := by
  intro k l h
  funext i
  have := congrFun h i
  simp only [boxVec] at this
  exact Fin.ext (by omega)

lemma mem_box (y : Fin 4 → ℤ) (hy : norm4 y = 4) : ∃ k, boxVec k = y := by
  have hb : ∀ i, -2 ≤ y i ∧ y i ≤ 2 := by
    intro i
    have hle : y i ^ 2 ≤ norm4 y :=
      Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
    rw [hy] at hle
    constructor <;> nlinarith [sq_nonneg (y i + 2), sq_nonneg (y i - 2)]
  refine ⟨fun i => ⟨(y i + 2).toNat, by have := hb i; omega⟩, ?_⟩
  funext i
  have := hb i
  simp only [boxVec]
  omega

/-- **Each nontrivial glue class of `D₄` has exactly eight minimal vectors.** -/
theorem minimal_class_card (c : ℕ) (hc : c = 1 ∨ c = 2 ∨ c = 3) :
    Set.ncard {y : Fin 4 → ℤ | glueClass y = c ∧ norm4 y = 4} = 8 := by
  have hset : {y : Fin 4 → ℤ | glueClass y = c ∧ norm4 y = 4} =
      boxVec '' ↑(Finset.univ.filter fun k : Fin 4 → Fin 5 =>
        glueClass (boxVec k) = c ∧ norm4 (boxVec k) = 4) := by
    ext y
    simp only [Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨k, rfl⟩ := mem_box y h2
      exact ⟨k, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact hk
  rw [hset, Set.ncard_image_of_injective _ boxVec_injective, Set.ncard_coe_finset]
  rcases hc with rfl | rfl | rfl
  · exact minimal_vector
  · exact minimal_spinor
  · exact minimal_cospinor

/-- The sector Gram matrix `D₄` is realized by the even-sum lattice in `ℤ⁴`. -/
def d4Basis : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0; -1, 1, 0, 0; 0, -1, 1, 1; 0, 0, -1, 1]

def d4Gram : Matrix (Fin 4) (Fin 4) ℤ := !![2, -1, 0, 0; -1, 2, -1, -1; 0, -1, 2, 0; 0, -1, 0, 2]

theorem d4_even_sum_model : d4Basisᵀ * d4Basis = d4Gram ∧
    ∀ i, Even (∑ j, d4Basis j i) := by
  refine ⟨by decide, by decide⟩

/-- Two orthogonal `D₄` sectors spanned by roots of `E₈`. -/
def sectorBasis : Matrix (Fin 8) (Fin 8) ℤ := (!![
  -1, -1, -2, -3, -2, -1, -1, -1;
  -1, -2, -2, -3, -3, -3, -2, -1;
  0, 0, 0, 0, 0, 1, 1, 1;
  1, 2, 2, 3, 3, 2, 1, 1;
  0, 0, 1, 0, 0, 0, 0, 0;
  -1, -1, -2, -2, -1, -1, 0, 0;
  0, 1, 1, 2, 1, 1, 0, 0;
  1, 0, 1, 1, 1, 1, 0, 0])ᵀ

def d4d4 : Matrix (Fin 8) (Fin 8) ℤ := !![
  2, -1, 0, 0, 0, 0, 0, 0;
  -1, 2, -1, -1, 0, 0, 0, 0;
  0, -1, 2, 0, 0, 0, 0, 0;
  0, -1, 0, 2, 0, 0, 0, 0;
  0, 0, 0, 0, 2, -1, 0, 0;
  0, 0, 0, 0, -1, 2, -1, -1;
  0, 0, 0, 0, 0, -1, 2, 0;
  0, 0, 0, 0, 0, -1, 0, 2]

theorem e8_two_d4_sectors : sectorBasisᵀ * Lattices.gram * sectorBasis = d4d4 := by decide

/-- **Channel counts.** A channel is a nontrivial glue class of a `D₄` sector, with capacity
its number of minimal (least-cost) vectors: `8`. Directional flow uses two distinct classes
(input and output), so `ν = 16` per sector and `N = 32` for the two sectors, whichever two
classes are chosen. -/
def channelCapacity : ℕ := minimalCount 1
def nu : ℕ := 2 * channelCapacity
def channelTotal : ℕ := 2 * nu

theorem channel_capacity : channelCapacity = 8 ∧ minimalCount 2 = 8 ∧ minimalCount 3 = 8 :=
  ⟨minimal_vector, minimal_spinor, minimal_cospinor⟩
theorem nu_eq : nu = 16 := by simp [nu, channelCapacity, minimal_vector]
theorem channel_total : channelTotal = 32 := by simp [channelTotal, nu_eq]


attribute [irreducible] minimalCount channelCapacity nu channelTotal

end PMArch.Channels
