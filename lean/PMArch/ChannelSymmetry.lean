import PMArch.Channels
import Mathlib.Algebra.BigOperators.Fin

/-!
# The channel labels are uniform because the substrate's own symmetries act transitively

`ClosureSymmetry.invariant_measure_uniform` assumes that every relabeling of a finite label
set is a symmetry. For the 32 channel labels used by Toll's legs this is not needed: the
symmetries of the forced structure (`E₈` with two `D₄` sectors) already act transitively, so any
measure invariant under them is uniform.

Channels are the minimal vectors of two nontrivial glue classes in each of the two sectors, in
the doubled coordinates of `Channels` (`carriers c`, 8 each; we take the vector and spinor
classes, see `pair_choice`). The generators are:

* `refl r` in either sector, for the four simple roots of `D₄` (the even-sum model): Weyl
  reflections. They preserve the norm (`refl_norm`), the 24 sector roots (`refl_roots`) and
  every glue class (`refl_class`), so they act trivially on glue.
* `hada`, applied to both sectors at once: the orthogonal map `H/2` with `H Hᵀ = 4` (`hada_orth`).
  It preserves the sector roots (`hada_roots`) and permutes the glue classes the same way in
  both sectors, exchanging vector and spinor and fixing the rest (`hada_class`).
* `swapS`: exchange of the two sectors.

With `E₈` glued from `D₄ ⊕ D₄` by pairing equal glue classes, each generator preserves the
sector roots and the glue pairing, so it is an automorphism of the forced lattice that
preserves the sector split. (Every gluing of two `D₄`s into an even unimodular lattice pairs the
classes by a bijection, and a triality in one sector brings it to this form.)

* `generators_preserve`: each generator maps the 32 channels to themselves (`gen_table`).
* `orbit_all`: from one channel, the generators reach all 32 (in at most eight steps).
* `invariant_constant`, `invariant_uniform`: a probability on the channels invariant under the
  generators gives each channel `1/32`.
* `pair_choice`: `hada` and a single sign flip permute the three classes as `S₃`, so which two
  classes carry the flow is itself not distinguished.
-/

namespace PMArch.ChannelSymmetry
open Channels Finset

abbrev V4 := Fin 4 → ℤ

/-- The eight minimal vectors of glue class `c` (doubled coordinates). -/
def carriers (c : ℕ) : Finset V4 :=
  (univ.filter fun k : Fin 4 → Fin 5 => glueClass (boxVec k) = c ∧ norm4 (boxVec k) = 4).image
    boxVec

/-- The 24 roots of a sector (doubled coordinates: glue class 0, `|y|² = 8`). -/
def roots : Finset V4 :=
  (univ.filter fun k : Fin 4 → Fin 5 => glueClass (boxVec k) = 0 ∧ norm4 (boxVec k) = 8).image
    boxVec

theorem carriers_card : (carriers 1).card = 8 ∧ (carriers 2).card = 8 ∧ (carriers 3).card = 8 := by
  decide +kernel

theorem roots_card : roots.card = 24 := by decide +kernel

def dot4 (x y : V4) : ℤ := ∑ i, x i * y i

/-- Reflection in a root `r` (undoubled even-sum coordinates, `r·r = 2`). -/
def refl (r : V4) (y : V4) : V4 := fun i => y i - dot4 y r * r i

/-- `H/2`, with `H` the 4×4 Hadamard matrix. -/
def hada (y : V4) : V4 := ![(y 0 + y 1 + y 2 + y 3) / 2, (y 0 + y 1 - y 2 - y 3) / 2,
  (y 0 - y 1 + y 2 - y 3) / 2, (y 0 - y 1 - y 2 + y 3) / 2]

/-- A sign flip of one coordinate (an outer automorphism of `D₄`). -/
def flip (y : V4) : V4 := ![-y 0, y 1, y 2, y 3]

/-- Simple roots of `D₄` in the even-sum model. -/
def simple : Fin 4 → V4 := ![![1, -1, 0, 0], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, 1]]

theorem simple_norm (j : Fin 4) : dot4 (simple j) (simple j) = 2 := by
  fin_cases j <;> decide +kernel

theorem refl_norm (r y : V4) (hr : dot4 r r = 2) : norm4 (refl r y) = norm4 y := by
  simp only [norm4, refl, dot4, Fin.sum_univ_four] at *
  linear_combination (y 0 * r 0 + y 1 * r 1 + y 2 * r 2 + y 3 * r 3) ^ 2 * hr

theorem refl_roots (j : Fin 4) : roots.image (refl (simple j)) = roots := by
  fin_cases j <;> decide +kernel

theorem refl_class (j : Fin 4) (c : Fin 4) :
    (carriers c).image (refl (simple j)) = carriers c := by
  fin_cases j <;> fin_cases c <;> decide +kernel

def hadaMat : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]

theorem hada_orth : hadaMat * hadaMat.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide +kernel

/-- On the sector roots and all carriers, `hada` is exactly `H/2` (no rounding). -/
theorem hada_exact : ∀ y ∈ roots ∪ carriers 1 ∪ carriers 2 ∪ carriers 3,
    (2 : ℤ) • hada y = hadaMat.mulVec y := by
  decide +kernel

theorem hada_roots : roots.image hada = roots := by decide +kernel

theorem hada_class : (carriers 1).image hada = carriers 2 ∧ (carriers 2).image hada = carriers 1 ∧
    (carriers 3).image hada = carriers 3 := by decide +kernel

theorem flip_roots : roots.image flip = roots := by decide +kernel

theorem flip_class : (carriers 1).image flip = carriers 1 ∧ (carriers 2).image flip = carriers 3 ∧
    (carriers 3).image flip = carriers 2 := by decide +kernel

/-! ## The 32 channels and their symmetries -/

/-- A channel: a sector (`false`, `true`) and a minimal vector of the vector or spinor class. -/
def channels : Finset (Bool × V4) := univ ×ˢ (carriers 1 ∪ carriers 2)

/-- Weyl reflection in sector `s`. -/
def reflS (s : Bool) (j : Fin 4) (x : Bool × V4) : Bool × V4 :=
  if x.1 = s then (x.1, refl (simple j) x.2) else x

/-- The ten generators: four reflections in each sector, `hada` on both, and the sector swap. -/
def gen : Fin 10 → Bool × V4 → Bool × V4 := fun i =>
  if h : i.val < 4 then reflS false ⟨i.val, h⟩
  else if h' : i.val < 8 then reflS true ⟨i.val - 4, by omega⟩
  else if i.val = 8 then fun x => (x.1, hada x.2)
  else fun x => (!x.1, x.2)

/-- An enumeration of the channels. -/
def chanTable : Fin 32 → Bool × V4 := ![(false, ![2, 0, 0, 0]),
  (false, ![-2, 0, 0, 0]),
  (false, ![0, 2, 0, 0]),
  (false, ![0, -2, 0, 0]),
  (false, ![0, 0, 2, 0]),
  (false, ![0, 0, -2, 0]),
  (false, ![0, 0, 0, 2]),
  (false, ![0, 0, 0, -2]),
  (false, ![1, 1, 1, 1]),
  (false, ![1, 1, -1, -1]),
  (false, ![1, -1, 1, -1]),
  (false, ![1, -1, -1, 1]),
  (false, ![-1, 1, 1, -1]),
  (false, ![-1, 1, -1, 1]),
  (false, ![-1, -1, 1, 1]),
  (false, ![-1, -1, -1, -1]),
  (true, ![2, 0, 0, 0]),
  (true, ![-2, 0, 0, 0]),
  (true, ![0, 2, 0, 0]),
  (true, ![0, -2, 0, 0]),
  (true, ![0, 0, 2, 0]),
  (true, ![0, 0, -2, 0]),
  (true, ![0, 0, 0, 2]),
  (true, ![0, 0, 0, -2]),
  (true, ![1, 1, 1, 1]),
  (true, ![1, 1, -1, -1]),
  (true, ![1, -1, 1, -1]),
  (true, ![1, -1, -1, 1]),
  (true, ![-1, 1, 1, -1]),
  (true, ![-1, 1, -1, 1]),
  (true, ![-1, -1, 1, 1]),
  (true, ![-1, -1, -1, -1])]

theorem chanTable_injective : Function.Injective chanTable := by decide +kernel

theorem channels_eq : channels = univ.image chanTable := by decide +kernel

theorem channels_card : channels.card = 32 := by
  rw [channels_eq, card_image_of_injective _ chanTable_injective]; rfl

/-- The generators' action on the enumeration (computed, then checked). -/
def genTable : Fin 10 → Fin 32 → Fin 32 := ![![2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
  ![0, 1, 4, 5, 2, 3, 6, 7, 8, 10, 9, 11, 12, 14, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
  ![0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 11, 10, 13, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
  ![0, 1, 2, 3, 7, 6, 5, 4, 9, 8, 10, 11, 12, 13, 15, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 16, 17, 20, 21, 22, 23, 24, 25, 28, 29, 26, 27, 30, 31],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 18, 19, 22, 23, 24, 26, 25, 27, 28, 30, 29, 31],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 20, 21, 24, 25, 27, 26, 29, 28, 30, 31],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 23, 22, 21, 20, 25, 24, 26, 27, 28, 29, 31, 30],
  ![8, 15, 9, 14, 10, 13, 11, 12, 0, 2, 4, 6, 7, 5, 3, 1, 24, 31, 25, 30, 26, 29, 27, 28, 16, 18, 20, 22, 23, 21, 19, 17],
  ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]

theorem gen_table : ∀ i k, gen i (chanTable k) = chanTable (genTable i k) := by decide +kernel

theorem generators_preserve (i : Fin 10) : channels.image (gen i) ⊆ channels := by
  intro x hx
  rw [channels_eq] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
  obtain ⟨k, -, rfl⟩ := mem_image.mp hy
  rw [gen_table]; exact mem_image_of_mem _ (mem_univ _)

/-- Indices reachable from channel `0` in at most `n` generator steps. -/
def reach : ℕ → Finset (Fin 32)
  | 0 => {0}
  | n + 1 => univ.filter fun k => k ∈ reach n ∨ ∃ i, ∃ j ∈ reach n, genTable i j = k

theorem orbit_all : reach 8 = univ := by decide +kernel

/-- **A measure invariant under the substrate's symmetries is constant on the channels.** -/
theorem invariant_constant (p : Bool × V4 → ℝ)
    (hp : ∀ i, ∀ x ∈ channels, p (gen i x) = p x) : ∀ x ∈ channels, p x = p (chanTable 0) := by
  have hp' : ∀ i k, p (chanTable (genTable i k)) = p (chanTable k) := fun i k => by
    rw [← gen_table]; exact hp i _ (by rw [channels_eq]; exact mem_image_of_mem _ (mem_univ _))
  have key : ∀ n, ∀ k ∈ reach n, p (chanTable k) = p (chanTable 0) := by
    intro n
    induction n with
    | zero => intro k hk; simp [reach] at hk; rw [hk]
    | succ n ih =>
      intro k hk
      simp only [reach, mem_filter, mem_univ, true_and] at hk
      rcases hk with hk | ⟨i, j, hj, rfl⟩
      · exact ih k hk
      · rw [hp']; exact ih j hj
  intro x hx
  rw [channels_eq] at hx
  obtain ⟨k, -, rfl⟩ := mem_image.mp hx
  exact key 8 k (by rw [orbit_all]; exact mem_univ _)

/-- **Each channel has probability `1/32`.** -/
theorem invariant_uniform (p : Bool × V4 → ℝ)
    (hp : ∀ i, ∀ x ∈ channels, p (gen i x) = p x) (hsum : ∑ x ∈ channels, p x = 1) :
    ∀ x ∈ channels, p x = 1 / 32 := by
  have hc := invariant_constant p hp
  rw [sum_congr rfl hc, sum_const, channels_card, nsmul_eq_mul] at hsum
  intro x hx
  rw [hc x hx]; push_cast at hsum; linarith

/-- The choice of the two flow classes is not distinguished: `flip` carries vector and conjugate
spinor to vector and spinor, and `flip ∘ hada` carries spinor and conjugate spinor there. -/
theorem pair_choice :
    ((carriers 1 ∪ carriers 3).image flip = carriers 1 ∪ carriers 2) ∧
      ((carriers 2 ∪ carriers 3).image (flip ∘ hada) = carriers 1 ∪ carriers 2) := by
  decide +kernel

end PMArch.ChannelSymmetry
