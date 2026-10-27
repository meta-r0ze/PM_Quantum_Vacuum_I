import PMArch.Scheduling
import Mathlib.Logic.Equiv.Fin.Rotate

namespace PMArch

/-- Absolute fundamental discriminants listed in the paper. Membership is an
explicit hypothesis here; the class-number-one classification is proved in the separately
pinned `classification/` project. -/
def discriminantCandidates : Finset ℕ := {3, 4, 7, 8, 11, 19, 43, 67, 163}

/-- The interval filter has exactly one result. -/
theorem filtered_candidates :
    discriminantCandidates.filter (fun d => 32 ≤ d ∧ d ≤ 64) = {43} := by
  decide

/-- Conditional selection of 43, without assuming its conclusion. -/
theorem delta_eq_43 {Δ : ℕ} (hc : Δ ∈ discriminantCandidates)
    (hlo : 32 ≤ Δ) (hhi : Δ ≤ 64) : Δ = 43 := by
  have hm : Δ ∈ discriminantCandidates.filter (fun d => 32 ≤ d ∧ d ≤ 64) :=
    Finset.mem_filter.mpr ⟨hc, hlo, hhi⟩
  rw [filtered_candidates] at hm
  simpa using hm

/-- Compose actual serialization and scheduling hypotheses with the candidate
list. Identifying 32 channels with 32 active slots is explicit. -/
theorem schedule_selects_43 {Δ : ℕ}
    (encode : Fin 32 → Fin Δ) (hinj : Function.Injective encode)
    (advance : Equiv.Perm (Fin Δ)) (active : Finset (Fin Δ))
    (hactive : active.card = 32) (hgap : NoAdjacentIdle advance active)
    (hc : Δ ∈ discriminantCandidates) : Δ = 43 := by
  apply delta_eq_43 hc (serialization_bound encode hinj)
  have hhi := periodic_schedule_bound advance active hgap
  simpa [hactive] using hhi

/-- A concrete 43-slot cycle: slots 1,3,...,21 are idle; all others active. -/
def exampleActive : Finset (Fin 43) :=
  Finset.univ.filter (fun s => s.val % 2 = 0 ∨ 22 ≤ s.val)

theorem exampleActive_card : exampleActive.card = 32 := by decide

/-- The scheduling premises are realizable on a genuine single cycle. -/
theorem example_no_adjacent_idle : NoAdjacentIdle (finRotate 43) exampleActive := by
  change ∀ s : Fin 43, s ∉ exampleActive → finRotate 43 s ∈ exampleActive
  decide

theorem baseline_schedule_exists :
    ∃ active : Finset (Fin 43), active.card = 32 ∧
      NoAdjacentIdle (finRotate 43) active := by
  exact ⟨exampleActive, exampleActive_card, example_no_adjacent_idle⟩

end PMArch
