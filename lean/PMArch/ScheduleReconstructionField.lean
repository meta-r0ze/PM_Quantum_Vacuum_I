import PMArch.ScheduleReconstruction
import PMArch.ClassNumber

/-! `schedule_selects_43_of_field` with the serialization and `NoAdjacentIdle` hypotheses
discharged from reconstruction (see `ScheduleReconstruction`). Kept separate because it imports
the class-number-one classification. -/

namespace PMArch.ScheduleReconstruction

/-- `schedule_selects_43_of_field` with the scheduling hypotheses derived. -/
theorem schedule_selects_43_of_field_reconstructible {Δ : ℕ} (K : Type*) [Field K]
    [NumberField K] (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hc : NumberField.classNumber K = 1)
    (hΔ : Δ = (NumberField.discr K).natAbs) (h : Reconstructible 32 Δ) : Δ = 43 := by
  obtain ⟨e, a, he, ha, hg⟩ := slot_schedule_of_reconstructible h
  exact schedule_selects_43_of_field K hK m hm hsq hc hΔ e he (finRotate Δ) a ha hg

end PMArch.ScheduleReconstruction
