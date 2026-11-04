import PMSubstrate.Impedance
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt

/-!
# Derived readouts of the geometric index

These are unit readouts built from `α⁻¹ = geometricIndex` and exact SI constants.
`speedOfLight` is the defined SI value `299792458 m/s`, written in units of
`10⁷ m/s`; it is a supplied convention, not a fitted input. The E8 content is
only the certified enclosure of `geometricIndex`.
-/

noncomputable section
namespace PMSubstrate

/-- Exact SI speed of light in units of `10⁷ m/s`. -/
def speedOfLight : ℝ := 149896229 / 5000000

theorem speedOfLight_value : speedOfLight = 149896229 / 5000000 := rfl

/-- Von Klitzing constant `h/e² = 2πc/α`, using `1/α = geometricIndex`. -/
def vonKlitzing : ℝ := 2 * Real.pi * speedOfLight * geometricIndex

theorem vonKlitzing_bounds :
    (25812.8074694137 : ℝ) < vonKlitzing ∧ vonKlitzing < 25812.8074694138 := by
  have hg := geometricIndex_bounds
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  have hpi0 : (0 : ℝ) < Real.pi := by linarith
  have hg0 : (0 : ℝ) < geometricIndex := by linarith [hg.1]
  have p1 : (3.14159265358979323846 : ℝ) * 137.035999212381397211 <
      Real.pi * geometricIndex :=
    mul_lt_mul'' hp1 hg.1 (by norm_num) (by norm_num)
  have p2 : Real.pi * geometricIndex <
      (3.14159265358979323847 : ℝ) * 137.035999212381397213 :=
    mul_lt_mul'' hp2 hg.2 (by linarith) (by linarith)
  unfold vonKlitzing speedOfLight
  constructor <;> nlinarith [p1, p2]

/-- `√α⁻¹`, the inverse Planck-charge ratio (attenuation). -/
def planckChargeAttenuation : ℝ := Real.sqrt geometricIndex

theorem planckChargeAttenuation_bounds :
    (11.70623761984957 : ℝ) < planckChargeAttenuation ∧
      planckChargeAttenuation < 11.70623761984958 := by
  have h := geometricIndex_bounds
  unfold planckChargeAttenuation
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    linarith [h.1]
  · rw [Real.sqrt_lt' (by norm_num)]
    linarith [h.2]

/-- `1/√α⁻¹`, the Planck-charge ratio. -/
def planckChargeRatio : ℝ := 1 / Real.sqrt geometricIndex

theorem planckChargeRatio_bounds :
    (0.0854245430918 : ℝ) < planckChargeRatio ∧ planckChargeRatio < 0.0854245430919 := by
  have ha := planckChargeAttenuation_bounds
  have ha1 : (11.70623761984957 : ℝ) < Real.sqrt geometricIndex := by
    simpa [planckChargeAttenuation] using ha.1
  have ha2 : Real.sqrt geometricIndex < 11.70623761984958 := by
    simpa [planckChargeAttenuation] using ha.2
  have hpos : 0 < Real.sqrt geometricIndex := by linarith
  have q1 : 0.0854245430918 * Real.sqrt geometricIndex <
      0.0854245430918 * 11.70623761984958 :=
    mul_lt_mul_of_pos_left ha2 (by norm_num)
  have q2 : 0.0854245430919 * 11.70623761984957 <
      0.0854245430919 * Real.sqrt geometricIndex :=
    mul_lt_mul_of_pos_left ha1 (by norm_num)
  unfold planckChargeRatio
  constructor
  · rw [lt_div_iff₀ hpos]
    nlinarith [q1]
  · rw [div_lt_iff₀ hpos]
    nlinarith [q2]

end PMSubstrate
