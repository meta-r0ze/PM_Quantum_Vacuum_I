import PMArch.Channels
import PMArch.ThetaE8
import PMArch.ClockPlane
import PMArch.Impedance

/-!
# What the forced substrate itself provides

Intrinsic counts of the forced structures — `E₈`, its two `D₄` sectors and the clock plane —
computed without reference to the six-term formula, for comparison with the paper's
bookkeeping integers.

* `E₈`: 240 roots (`ThetaE8.e8_card_roots`), rank 8, so the Coxeter number is
  `h = 240/8 = 30` and the Lie-algebra dimension per rank is `248/8 = h + 1 = 31`.
* `D₄`: 24 roots (`d4_card_roots`), rank 4, Coxeter number `h = 24/4 = 6`; three nontrivial glue
  classes of 8 minimal vectors (`Channels.minimal_class_card`).
* Clock plane: discriminant group of order 43 (`ClockPlane.clock_glue`).

`margin_reading`: the Margin denominator `L_embed (σ+1) Δ²` equals
`(h(E₈)+1) · h(D₄) · |clock states|²`. This is an identity between integers; whether it is the
right reading of Margin is a modeling question recorded in the comparison note.
-/

namespace PMArch.E8Invariants
open Matrix

/-- Vectors of `ℤ⁴` in the box `|yᵢ| ≤ 1`, encoded by `k ↦ k - 1`. -/
def box1 (k : Fin 4 → Fin 3) : Fin 4 → ℤ := fun i => (k i : ℤ) - 1

/-- Roots of `D₄ = {x ∈ ℤ⁴ : Σx even}`: norm 2. -/
def IsD4Root (y : Fin 4 → ℤ) : Prop := Even (∑ i, y i) ∧ ∑ i, y i ^ 2 = 2

instance (y : Fin 4 → ℤ) : Decidable (IsD4Root y) := by unfold IsD4Root; infer_instance

theorem d4_roots_box : (Finset.univ.filter fun k => IsD4Root (box1 k)).card = 24 := by decide

lemma box1_injective : Function.Injective box1 := by
  intro k l h; funext i
  have := congrFun h i; simp only [box1] at this; exact Fin.ext (by omega)

lemma mem_box1 (y : Fin 4 → ℤ) (hy : ∑ i, y i ^ 2 = 2) : ∃ k, box1 k = y := by
  have hb : ∀ i, -1 ≤ y i ∧ y i ≤ 1 := by
    intro i
    have hle : y i ^ 2 ≤ ∑ j, y j ^ 2 :=
      Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
    rw [hy] at hle
    constructor <;> nlinarith [sq_nonneg (y i + 1), sq_nonneg (y i - 1)]
  refine ⟨fun i => ⟨(y i + 1).toNat, by have := hb i; omega⟩, ?_⟩
  funext i; have := hb i; simp only [box1]; omega

/-- **`D₄` has 24 roots.** -/
theorem d4_card_roots : Set.ncard {y : Fin 4 → ℤ | IsD4Root y} = 24 := by
  have hset : {y : Fin 4 → ℤ | IsD4Root y} =
      box1 '' ↑(Finset.univ.filter fun k => IsD4Root (box1 k)) := by
    ext y
    simp only [Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; obtain ⟨k, rfl⟩ := mem_box1 y h.2; exact ⟨k, h, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact hk
  rw [hset, Set.ncard_image_of_injective _ box1_injective, Set.ncard_coe_finset, d4_roots_box]

/-- Coxeter numbers `h = |Φ| / rank`. -/
theorem coxeter_numbers :
    Nat.card {z : Fin 8 → ℤ // z ⬝ᵥ (Lattices.gram *ᵥ z) = 2} = 8 * 30 ∧
      Set.ncard {y : Fin 4 → ℤ | IsD4Root y} = 4 * 6 := by
  rw [ThetaE8.e8_card_roots, d4_card_roots]; norm_num

/-- **Margin in substrate terms.** The paper's Margin denominator equals
`(h(E₈) + 1) · h(D₄) · 43²`, with `h(E₈) + 1 = (|Φ(E₈)| + 8)/8 = dim 𝔢₈ / rank`. -/
theorem margin_reading :
    (Nat.card {z : Fin 8 → ℤ // z ⬝ᵥ (Lattices.gram *ᵥ z) = 2} + 8) / 8 *
        (Set.ncard {y : Fin 4 → ℤ | IsD4Root y} / 4) * 43 ^ 2 =
      baseline.embeddingLoad * (baseline.embeddingDimension + 1) * baseline.period ^ 2 := by
  rw [ThetaE8.e8_card_roots, d4_card_roots]; decide

/-! ## Triality: the minimal neutral interaction has three legs

The glue group of a `D₄` sector is `(ℤ/2)²`, with three nonzero classes (vector, spinor,
conjugate spinor). A combination of glue classes that leaves no net glue — an interaction the
sector can absorb — using pairwise distinct, nonzero classes must use all three: two equal
classes merely propagate one channel, and there is no fourth distinct type. -/

/-- Any set of distinct nonzero glue classes with zero total has exactly three elements. -/
theorem neutral_distinct_classes :
    ∀ s : Finset (ZMod 2 × ZMod 2), (0 : ZMod 2 × ZMod 2) ∉ s → s.Nonempty →
      ∑ x ∈ s, x = 0 → s.card = 3 := by decide

/-- A neutral pair of nonzero classes is a repeated class (propagation). -/
theorem neutral_pair (x y : ZMod 2 × ZMod 2) : x + y = 0 ↔ x = y := by
  revert x y; decide

end PMArch.E8Invariants
