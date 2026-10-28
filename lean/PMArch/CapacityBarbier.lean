import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import PMArch.Impedance

/-!
# Capacity: the largest boundary a causal cycle allows is `πΔ`

A planar convex envelope is described by its support function `h(θ)`; its width in direction
`θ` is `h(θ) + h(θ + π)`, and its perimeter is `∫₀^{2π} h` (Cauchy's formula, taken here as the
boundary measure of a convex envelope).

* `barbier`: every envelope of constant width `w` has perimeter `π w`, whatever its shape.
* `perimeter_le`: if every width is at most `w`, the perimeter is at most `π w`.
* `capacity_is_max`: with the causal bound `width ≤ Δ` (a signal must cross and return within
  one cycle), the largest admissible boundary is exactly `πΔ = capacityTerm`. It is attained by
  every constant-width envelope (the disk is one).

So neither roundness nor saturation is a separate choice: Capacity is the maximal causally
admissible boundary, and its value does not depend on the envelope's shape.

Here `h` ranges over all continuous functions, a class containing every support function, so
the upper bound covers convex envelopes a fortiori. `CapacityEnvelope` restates it on actual
compact convex sets: the support function is computed from the set, the width bound is derived
from a causal diameter bound, and the disk is shown to attain `πΔ`. Cauchy's formula
(perimeter = `∫ h`) is used as the definition of the boundary measure in both files and is not
proved.
-/

open Real intervalIntegral

namespace PMArch.Capacity

theorem half_turn_split (h : ℝ → ℝ) (hc : Continuous h) :
    ∫ θ in (0)..(2 * π), h θ = ∫ θ in (0)..π, (h θ + h (θ + π)) := by
  have h1 : ∫ θ in (0)..(2 * π), h θ = (∫ θ in (0)..π, h θ) + ∫ θ in π..(2 * π), h θ :=
    (integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  have h2 : ∫ θ in π..(2 * π), h θ = ∫ θ in (0)..π, h (θ + π) := by
    rw [intervalIntegral.integral_comp_add_right]; congr 1 <;> ring
  have hc2 : Continuous fun θ => h (θ + π) := hc.comp (continuous_id.add continuous_const)
  rw [h1, h2, intervalIntegral.integral_add (hc.intervalIntegrable 0 π) (hc2.intervalIntegrable 0 π)]

theorem barbier (h : ℝ → ℝ) (hc : Continuous h) (w : ℝ) (hw : ∀ θ, h θ + h (θ + π) = w) :
    ∫ θ in (0)..(2 * π), h θ = π * w := by
  rw [half_turn_split h hc]
  simp [hw]

theorem perimeter_le (h : ℝ → ℝ) (hc : Continuous h) (w : ℝ) (hw : ∀ θ, h θ + h (θ + π) ≤ w) :
    ∫ θ in (0)..(2 * π), h θ ≤ π * w := by
  rw [half_turn_split h hc]
  have : ∫ θ in (0)..π, (h θ + h (θ + π)) ≤ ∫ θ in (0)..π, w :=
    intervalIntegral.integral_mono_on pi_pos.le
      ((hc.add (hc.comp (continuous_id.add continuous_const))).intervalIntegrable _ _)
      intervalIntegrable_const (fun θ _ => hw θ)
  simpa using this

/-- **Capacity is the causal maximum.** Over all continuous support functions whose widths obey
the causal bound `≤ Δ`, the perimeter never exceeds `πΔ`, and `πΔ` is attained. -/
theorem capacity_is_max (p : Parameters) :
    (∀ h : ℝ → ℝ, Continuous h → (∀ θ, h θ + h (θ + π) ≤ p.period) →
        ∫ θ in (0)..(2 * π), h θ ≤ capacityTerm p) ∧
      ∃ h : ℝ → ℝ, Continuous h ∧ (∀ θ, h θ + h (θ + π) ≤ p.period) ∧
        ∫ θ in (0)..(2 * π), h θ = capacityTerm p := by
  refine ⟨fun h hc hw => ?_, fun _ => (p.period : ℝ) / 2, continuous_const, fun θ => by linarith, ?_⟩
  · simpa [capacityTerm] using perimeter_le h hc _ hw
  · rw [barbier _ continuous_const (p.period : ℝ) (fun θ => by ring)]
    rfl

end PMArch.Capacity
