import ELEM.Main
import CN1.Foundations.Discr

namespace PMArchClassification

/-- Absolute-discriminant arithmetic for a squarefree imaginary quadratic radicand.
The identification with the field discriminant is proved below. -/
def discriminantMagnitude (m : ℕ) : ℕ := if m % 4 = 3 then m else 4 * m

theorem class_one_discriminant_candidates (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hc : NumberField.classNumber K = 1) :
    discriminantMagnitude m ∈ ({3, 4, 7, 8, 11, 19, 43, 67, 163} : Finset ℕ) := by
  have h := (CN1.classNumber_eq_one_iff K hK m hm hsq).mp hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h | h | h | h | h <;>
    subst m <;> norm_num [discriminantMagnitude]

theorem class_one_window (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hc : NumberField.classNumber K = 1)
    (hlo : 32 ≤ discriminantMagnitude m) (hhi : discriminantMagnitude m ≤ 64) :
    discriminantMagnitude m = 43 := by
  have h := class_one_discriminant_candidates K hK m hm hsq hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  omega

theorem abs_discriminant_eq (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    (NumberField.discr K).natAbs = discriminantMagnitude m := by
  obtain ⟨α, hα⟩ := hsq
  rw [CN1.Foundations.discr_eq hα hK hm]
  simp only [Int.natAbs_neg, Int.natAbs_natCast]
  rfl

theorem actual_discriminant_window (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hc : NumberField.classNumber K = 1)
    (hlo : 32 ≤ (NumberField.discr K).natAbs)
    (hhi : (NumberField.discr K).natAbs ≤ 64) :
    (NumberField.discr K).natAbs = 43 := by
  rw [abs_discriminant_eq K hK m hm hsq] at hlo hhi ⊢
  exact class_one_window K hK m hm hsq hc hlo hhi

end PMArchClassification
