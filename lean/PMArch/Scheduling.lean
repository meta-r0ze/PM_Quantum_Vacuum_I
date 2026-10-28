import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
Finite scheduling consequences. The interpretation of states as channels and
slots as physical time is a modeling assumption, not a theorem in this file.
-/
namespace PMArch

/-- An injective serialization needs at least as many slots as states. -/
theorem serialization_bound {N Δ : ℕ} (encode : Fin N → Fin Δ)
    (hencode : Function.Injective encode) : N ≤ Δ := by
  simpa using Fintype.card_le_of_injective encode hencode

/-- Every idle slot is immediately followed by an active slot. A permutation
models reversible advancement; the bound also holds when it has multiple cycles.
In particular it holds for advancement around a single periodic cycle.

On a cycle this is "every idle run has length at most one". In this file and in
`Selection`, `ClassNumber`, `Clock` and `MainResult` it is a hypothesis. It is
derived from reconstruction under gap-only observation in `Sectors.obs_injOn_iff`, and
`ScheduleReconstruction` discharges it (with the serialization map) for every theorem
that takes it. -/
def NoAdjacentIdle {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (advance : Equiv.Perm Slot) (active : Finset Slot) : Prop :=
  ∀ s, s ∉ active → advance s ∈ active

/-- Map each idle slot injectively to the active slot that follows it. -/
theorem idle_card_le_active {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (advance : Equiv.Perm Slot) (active : Finset Slot)
    (h : NoAdjacentIdle advance active) :
    (Finset.univ \ active).card ≤ active.card := by
  have hsubset : (Finset.univ \ active).image advance ⊆ active := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact h t (Finset.mem_sdiff.mp ht).2
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ advance.injective] at hcard
  exact hcard

/-- On a finite periodic schedule, no adjacent idle slots implies Δ ≤ 2N,
where N is the number of active slots. -/
theorem periodic_schedule_bound {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (advance : Equiv.Perm Slot) (active : Finset Slot)
    (h : NoAdjacentIdle advance active) :
    Fintype.card Slot ≤ 2 * active.card := by
  have hi := idle_card_le_active advance active h
  have hc : (Finset.univ \ active).card + active.card = Fintype.card Slot := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ active)
  omega

end PMArch
