import PMArch.Impedance
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate

/-!
# Experimental comparison and Postulate R

* `alpha_deviations`: the deviations `(Z_geo - α⁻¹_exp) / σ_exp` quoted in the manuscript's table,
  computed from the certified enclosure of `geometricIndex`. The experimental values and
  uncertainties are inputs copied from the cited sources; only the arithmetic is checked.
* `never_merge_iff_bijective`: on a finite state space, an update never merges two distinct
  states at any time iff it is bijective (Postulate R as an exact translation).
-/

namespace PMArch

/-- Certified deviations, in units of the quoted standard uncertainty, for the four inputs in
the manuscript's comparison table. Each lies within rounding of the stated value. -/
theorem alpha_deviations :
    (0.575 : ℝ) < (geometricIndex - 137.035999206) / 0.000000011 ∧
      (geometricIndex - 137.035999206) / 0.000000011 < 0.585 ∧
    (3.085 : ℝ) < (geometricIndex - 137.035999166) / 0.000000015 ∧
      (geometricIndex - 137.035999166) / 0.000000015 < 3.095 ∧
    (6.155 : ℝ) < (geometricIndex - 137.035999046) / 0.000000027 ∧
      (geometricIndex - 137.035999046) / 0.000000027 < 6.165 ∧
    (1.675 : ℝ) < (geometricIndex - 137.035999177) / 0.000000021 ∧
      (geometricIndex - 137.035999177) / 0.000000021 < 1.685 := by
  obtain ⟨hlo, hhi⟩ := geometricIndex_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  first
  | (rw [lt_div_iff₀ (by norm_num)]; linarith)
  | (rw [div_lt_iff₀ (by norm_num)]; linarith)

/-- **Postulate R as an exact translation.** On a finite state space, no two distinct states
are ever merged by the evolution iff the update is bijective. -/
theorem never_merge_iff_bijective {X : Type*} [Finite X] (U : X → X) :
    (∀ t : ℕ, Function.Injective (U^[t])) ↔ Function.Bijective U := by
  constructor
  · intro h
    exact Finite.injective_iff_bijective.mp (by simpa using h 1)
  · intro h t
    exact h.1.iterate t

end PMArch
