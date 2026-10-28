import PMArch.SchedulingComplete
import PMArch.Sectors
import PMArch.Channels
import PMArch.MainResult
import PMArch.Clock

/-!
# Scheduling from reconstruction

The older scheduling route (`Scheduling`, `Selection`, `ClassNumber`, `Clock`, `MainResult`)
takes the slot-level condition `NoAdjacentIdle` as a hypothesis. This module derives it.

The premise used instead is the one in `Vacuum.ClockPostulates.schedule`: a cycle serializes
`N` active slots, each followed by an idle run `g i`, and the schedule must be recoverable from
gap-only local observations (`Sectors.obs`: one bit per active slot, "an idle run follows").
`Sectors.obs_injOn_iff` shows that recoverability holds exactly when every idle run has length
at most one. With longer runs `Sectors.aliasing` gives two schedules with the same observations
and different periods.

* `reconstructible_period_iff`: the periods of reconstructible gap schedules are exactly
  `N ≤ Δ ≤ 2N`.
* `reconstructible_iff_noAdjacentIdle`: those are exactly the periods that admit a slot-level
  schedule satisfying `NoAdjacentIdle` on a single cycle. On a cycle, `NoAdjacentIdle` is the
  slot-level form of "idle runs have length at most one", which reconstruction forces.
* `schedule_selects_43_of_reconstructible` and the `_of_clock` variant (and `_of_field` in
  `ScheduleReconstructionField`) restate the
  older selection theorems with the serialization and `NoAdjacentIdle` hypotheses discharged.

The remaining premise is the observation model: each active slot records only whether an idle
run follows it. An observation that also records run lengths removes the bound.
-/

namespace PMArch.ScheduleReconstruction

open Sectors

/-- Gap data of `N` active slots whose idle runs are bounded and recoverable from the gap-only
observation, with period `Δ`. -/
def Reconstructible (N Δ : ℕ) : Prop :=
  ∃ (k : ℕ) (g : Fin N → ℕ), (∀ i, g i ≤ k) ∧
    Set.InjOn obs {g : Fin N → ℕ | ∀ i, g i ≤ k} ∧ period g = Δ

lemma sum_indicator (m N : ℕ) (h : m ≤ N) :
    (∑ i : Fin N, if i.val < m then 1 else 0 : ℕ) = m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < m then 1 else 0), Finset.sum_boole]
  have : (Finset.range N).filter (· < m) = Finset.range m := by
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
  simp [this]

/-- The periods of reconstructible schedules are exactly the window `N ≤ Δ ≤ 2N`. -/
theorem reconstructible_period_iff {N : ℕ} (hN : 0 < N) (Δ : ℕ) :
    Reconstructible N Δ ↔ N ≤ Δ ∧ Δ ≤ 2 * N := by
  constructor
  · rintro ⟨k, g, hk, hinj, rfl⟩
    have hk1 := (obs_injOn_iff hN k).mp hinj
    exact ⟨by unfold period; omega, period_le_two_mul g fun i => (hk i).trans hk1⟩
  · rintro ⟨hlo, hhi⟩
    refine ⟨1, fun i => if i.val < Δ - N then 1 else 0, fun i => by dsimp only; split_ifs <;> omega,
      (obs_injOn_iff hN 1).mpr le_rfl, ?_⟩
    unfold period
    rw [sum_indicator _ _ (by omega)]
    omega

/-- Reconstructible gap schedules and slot-level schedules with no adjacent idle slots on a
single cycle have the same periods. -/
theorem reconstructible_iff_noAdjacentIdle {N : ℕ} (hN : 0 < N) (Δ : ℕ) :
    Reconstructible N Δ ↔
      ∃ active : Finset (Fin Δ), active.card = N ∧ NoAdjacentIdle (finRotate Δ) active := by
  rw [reconstructible_period_iff hN, cyclic_schedule_exists_iff]

/-- Reconstruction supplies every scheduling hypothesis of `schedule_selects_43`. -/
theorem slot_schedule_of_reconstructible {Δ : ℕ} (h : Reconstructible 32 Δ) :
    ∃ (encode : Fin 32 → Fin Δ) (active : Finset (Fin Δ)), Function.Injective encode ∧
      active.card = 32 ∧ NoAdjacentIdle (finRotate Δ) active := by
  have hw := (reconstructible_period_iff (by norm_num) Δ).mp h
  obtain ⟨active, hc, hg⟩ := (reconstructible_iff_noAdjacentIdle (by norm_num) Δ).mp h
  exact ⟨Fin.castLE hw.1, active, Fin.castLE_injective hw.1, hc, hg⟩

/-- `schedule_selects_43` with the scheduling hypotheses derived from reconstruction. -/
theorem schedule_selects_43_of_reconstructible {Δ : ℕ} (h : Reconstructible 32 Δ)
    (hc : Δ ∈ discriminantCandidates) : Δ = 43 := by
  obtain ⟨e, a, he, ha, hg⟩ := slot_schedule_of_reconstructible h
  exact schedule_selects_43 e he (finRotate Δ) a ha hg hc

/-- `schedule_impedance_bounds` with the scheduling hypotheses derived from reconstruction. -/
theorem schedule_impedance_bounds_of_reconstructible {Δ : ℕ} (h : Reconstructible 32 Δ)
    (hc : Δ ∈ discriminantCandidates) :
    (137.035999212381397211 : ℝ) < impedance { baseline with period := Δ } ∧
    impedance { baseline with period := Δ } < (137.035999212381397213 : ℝ) := by
  obtain ⟨e, a, he, ha, hg⟩ := slot_schedule_of_reconstructible h
  exact schedule_impedance_bounds e he (finRotate Δ) a ha hg hc

/-- `Clock.schedule_selects_43_of_clock` with the scheduling hypotheses derived. -/
theorem schedule_selects_43_of_clock_reconstructible {Δ : ℕ} (D : ℤ) (hΔ : (Δ : ℤ) = -D)
    (hU : Clock.UniqueClock D) (h : Reconstructible 32 Δ) : Δ = 43 := by
  obtain ⟨e, a, he, ha, hg⟩ := slot_schedule_of_reconstructible h
  exact Clock.schedule_selects_43_of_clock D hΔ hU e he (finRotate Δ) a ha hg

/-- The premise in `Vacuum.ClockPostulates.schedule` is `Reconstructible 32 Δ`. -/
theorem clock_schedule_iff {Δ : ℕ} :
    (∃ (k : ℕ) (g : Fin Channels.channelTotal → ℕ), (∀ i, g i ≤ k) ∧
      Set.InjOn obs {g : Fin Channels.channelTotal → ℕ | ∀ i, g i ≤ k} ∧ Δ = period g) ↔
      Reconstructible 32 Δ := by
  rw [← Channels.channel_total]
  constructor
  · rintro ⟨k, g, hk, hi, rfl⟩; exact ⟨k, g, hk, hi, rfl⟩
  · rintro ⟨k, g, hk, hi, rfl⟩; exact ⟨k, g, hk, hi, rfl⟩

end PMArch.ScheduleReconstruction
