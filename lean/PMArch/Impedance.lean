import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
The paper's six-term expression is a definition, not a proved consequence of
closure, lattice geometry, or independent pillars. All divisions are in ℝ.
-/
noncomputable section

namespace PMArch

/-- Architectural parameters; no geometric derivation is asserted here. -/
structure Parameters where
  dimension : ℕ
  period : ℕ
  sectorChannels : ℕ
  embeddingDimension : ℕ
  eulerCharacteristic : ℕ
  deriving DecidableEq

def baseline : Parameters := ⟨4, 43, 16, 5, 2⟩
def Parameters.nodeCapacity (p : Parameters) : ℕ := 2 * p.sectorChannels
def Parameters.resolution (p : Parameters) : ℕ := p.dimension * p.period
def Parameters.intrinsicLoad (p : Parameters) : ℕ :=
  p.sectorChannels + p.embeddingDimension + p.eulerCharacteristic
def Parameters.embeddingLoad (p : Parameters) : ℕ := p.intrinsicLoad + 2 * p.dimension
def Parameters.substrateLoad (p : Parameters) : ℕ := p.resolution + p.sectorChannels

/-- Useful side conditions: the mathematical expression is defined for all
parameters in Lean, but these ensure no physical denominator is zero. -/
def Parameters.Admissible (p : Parameters) : Prop :=
  0 < p.period ∧ 0 < p.nodeCapacity ∧ 0 < p.embeddingDimension ∧
  p.embeddingDimension < p.resolution ∧ 0 < p.embeddingLoad

theorem baseline_loads :
    baseline.nodeCapacity = 32 ∧ baseline.resolution = 172 ∧
    baseline.intrinsicLoad = 23 ∧ baseline.embeddingLoad = 31 ∧
    baseline.substrateLoad = 188 := by decide

theorem baseline_admissible : baseline.Admissible := by
  unfold Parameters.Admissible
  decide

def capacityTerm (p : Parameters) : ℝ := Real.pi * p.period
def mapTerm (p : Parameters) : ℝ := p.eulerCharacteristic
def protocolTerm (p : Parameters) : ℝ :=
  -(1 / ((p.resolution : ℝ) - p.embeddingDimension))
def governorTerm (p : Parameters) : ℝ := -(p.eulerCharacteristic / (p.period : ℝ))
def tollTerm (p : Parameters) : ℝ :=
  p.eulerCharacteristic * ((p.resolution : ℝ) - p.embeddingDimension) /
    ((p.nodeCapacity : ℝ)^3 * p.embeddingDimension * p.resolution)
def marginTerm (p : Parameters) : ℝ :=
  1 / ((p.embeddingLoad : ℝ) * (p.embeddingDimension + 1) * (p.period : ℝ)^2)

/-- Signed additivity and unit weights are part of the model definition. -/
def impedance (p : Parameters) : ℝ :=
  capacityTerm p + mapTerm p + protocolTerm p + governorTerm p + tollTerm p + marginTerm p

noncomputable def geometricIndex : ℝ := impedance baseline
noncomputable def causalCoupling : ℝ := 1 / geometricIndex

/-- Exact specialization of the paper's formula, with no floating-point arithmetic. -/
theorem geometricIndex_exact : geometricIndex =
    43 * Real.pi + 2 - 1 / 167 - 2 / 43 +
    334 / (32^3 * 5 * 172) + 1 / (31 * 6 * 43^2) := by
  norm_num [geometricIndex, impedance, capacityTerm, mapTerm, protocolTerm,
    governorTerm, tollTerm, marginTerm, baseline, Parameters.nodeCapacity,
    Parameters.resolution, Parameters.embeddingLoad, Parameters.intrinsicLoad]
  ring

/-- Certified enclosure, using mathlib's proved 20-decimal bounds on π.
Decimal literals here denote exact rationals, not floating-point numbers. -/
theorem geometricIndex_bounds :
    (137.035999212381397211 : ℝ) < geometricIndex ∧
    geometricIndex < (137.035999212381397213 : ℝ) := by
  rw [geometricIndex_exact]
  constructor
  · nlinarith [Real.pi_gt_d20]
  · nlinarith [Real.pi_lt_d20]

theorem geometricIndex_gt_one : 1 < geometricIndex := by
  linarith [geometricIndex_bounds.1]

/-- Under the admittance definition the coupling is a valid probability-sized
number. This does not identify it with a measured physical coupling. -/
theorem causalCoupling_bounds : 0 < causalCoupling ∧ causalCoupling < 1 := by
  have hz : 0 < geometricIndex := lt_trans (by norm_num) geometricIndex_gt_one
  constructor
  · exact one_div_pos.mpr hz
  · exact (div_lt_iff₀ hz).mpr (by simpa using geometricIndex_gt_one)

end PMArch
