import Classification
import PMArch.MainResult

/-!
Integration of the vendored class-number-one classification (`classification/`) with the
scheduling argument. The candidate list in `PMArch.Selection` is no longer an assumption:
it is derived from the actual field discriminant of an imaginary quadratic number field of
class number one. The physical identification of the clock period with that discriminant
remains a hypothesis (`hΔ`).
-/

namespace PMArch

/-- The absolute discriminant of an imaginary quadratic field of class number one lies in
the explicit candidate list used by the scheduling argument. -/
theorem class_one_discr_mem (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hc : NumberField.classNumber K = 1) :
    (NumberField.discr K).natAbs ∈ discriminantCandidates := by
  rw [PMArchClassification.abs_discriminant_eq K hK m hm hsq]
  exact PMArchClassification.class_one_discriminant_candidates K hK m hm hsq hc

/-- Period selection with the candidate list discharged by the classification theorem. -/
theorem schedule_selects_43_of_field {Δ : ℕ} (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hc : NumberField.classNumber K = 1)
    (hΔ : Δ = (NumberField.discr K).natAbs)
    (encode : Fin 32 → Fin Δ) (hinj : Function.Injective encode)
    (advance : Equiv.Perm (Fin Δ)) (active : Finset (Fin Δ))
    (hactive : active.card = 32) (hgap : NoAdjacentIdle advance active) : Δ = 43 :=
  schedule_selects_43 encode hinj advance active hactive hgap
    (hΔ ▸ class_one_discr_mem K hK m hm hsq hc)

/-- End-to-end conditional result with the period identified with the discriminant of an
imaginary quadratic field of class number one. -/
theorem schedule_impedance_bounds_of_field {Δ : ℕ} (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hc : NumberField.classNumber K = 1)
    (hΔ : Δ = (NumberField.discr K).natAbs)
    (encode : Fin 32 → Fin Δ) (hinj : Function.Injective encode)
    (advance : Equiv.Perm (Fin Δ)) (active : Finset (Fin Δ))
    (hactive : active.card = 32) (hgap : NoAdjacentIdle advance active) :
    (137.035999212381397211 : ℝ) < impedance { baseline with period := Δ } ∧
    impedance { baseline with period := Δ } < (137.035999212381397213 : ℝ) :=
  schedule_impedance_bounds encode hinj advance active hactive hgap
    (hΔ ▸ class_one_discr_mem K hK m hm hsq hc)

end PMArch
