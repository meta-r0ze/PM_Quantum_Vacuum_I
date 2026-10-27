import PMArch.ProtocolToll
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Sampling weights from specified finite dynamics

Frequencies are equal-duration per-tick counts over one full orbit. This does
not derive the vacuum's update, its sample space, events, or physical rates.
-/
noncomputable section
namespace PMArch.SamplingDynamics
open Finset

def frequency {N : ℕ} {Ω : Type*} [DecidableEq Ω]
    (sample : Fin N → Ω) (E : Finset Ω) : ℚ :=
  ((Finset.univ.filter (fun t => sample t ∈ E)).card : ℚ) / N

/-- An enumerated full orbit defines a reversible autonomous clock. Selection
of such an orbit for the physical vacuum is not proved by its existence. -/
def orbitAdvance {N : ℕ} {Ω : Type*} (orbit : Fin N ≃ Ω) : Equiv.Perm Ω :=
  orbit.symm.trans ((finRotate N).trans orbit)

theorem orbit_advance {N : ℕ} {Ω : Type*} (orbit : Fin N ≃ Ω) (t : Fin N) :
    orbitAdvance orbit (orbit t) = orbit (finRotate N t) := by
  simp [orbitAdvance]

theorem orbit_iterates {N : ℕ} {Ω : Type*} (orbit : Fin N ≃ Ω)
    (s : Fin N) (t : ℕ) :
    ((orbitAdvance orbit)^[t]) (orbit s) = orbit (((finRotate N)^[t]) s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, orbit_advance]

theorem actual_tick_enumeration {N : ℕ} [NeZero N] {Ω : Type*}
    (orbit : Fin N ≃ Ω) (t : Fin N) :
    ((orbitAdvance orbit)^[t.val]) (orbit 0) = orbit t := by
  rw [orbit_iterates, ← finCycle_eq_finRotate_iterate (k := t)]
  simp

/-- Uniform event visitation is derived from a complete orbit and equal tick
counting. No initial probabilistic prior is used in this finite identity. -/
theorem full_orbit_frequency {N : ℕ} {Ω : Type*} [DecidableEq Ω]
    (orbit : Fin N ≃ Ω) (E : Finset Ω) : frequency orbit E = (E.card : ℚ) / N := by
  let T := Finset.univ.filter (fun t : Fin N => orbit t ∈ E)
  have himage : T.image orbit = E := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp ht).2
    · intro hx
      apply Finset.mem_image.mpr
      refine ⟨orbit.symm x, ?_, by simp⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa using hx⟩
  have hc := Finset.card_image_of_injective T orbit.injective
  rw [himage] at hc
  unfold frequency
  rw [← hc]

/-- `⟨0, h⟩ = 0` in `Fin N`, stated for abstract `N` so that no cardinality is evaluated. -/
lemma fin_mk_zero {N : ℕ} [NeZero N] (h : 0 < N) : (⟨0, h⟩ : Fin N) = 0 :=
  Fin.ext (Fin.val_zero N).symm

/-- This is the frequency of the actual autonomous update, rather than only
an abstract enumeration of a finite sample space. -/
theorem actual_clock_frequency {N : ℕ} [NeZero N] {Ω : Type*} [DecidableEq Ω]
    (orbit : Fin N ≃ Ω) (E : Finset Ω) :
    frequency (fun t : Fin N => ((orbitAdvance orbit)^[t.val]) (orbit 0)) E =
      (E.card : ℚ)/N := by
  have he : (fun t : Fin N => ((orbitAdvance orbit)^[t.val]) (orbit 0)) = orbit := by
    funext t
    exact actual_tick_enumeration orbit t
  rw [he]
  exact full_orbit_frequency orbit E

theorem uniform_full_cycle_exists (Ω : Type*) [Fintype Ω] [DecidableEq Ω] :
    ∃ orbit : Fin (Fintype.card Ω) ≃ Ω,
      ∀ E : Finset Ω, frequency orbit E = (E.card : ℚ) / Fintype.card Ω := by
  exact ⟨(Fintype.equivFin Ω).symm, fun E => full_orbit_frequency _ E⟩

/-- Uniform marginal clocks do not imply an independent joint clock. -/
def sync (t : Fin 43) : Fin 43 × Fin 43 := (t,t)

theorem synchronized_marginals :
    Function.Bijective (fun t => (sync t).1) ∧
    Function.Bijective (fun t => (sync t).2) := by
  exact ⟨Function.bijective_id, Function.bijective_id⟩

theorem synchronized_joint_not_product :
    frequency sync {(0,0)} = 1/43 ∧
    (1 : ℚ) / Fintype.card (Fin 43 × Fin 43) = 1/1849 ∧
    (1 : ℚ)/43 ≠ 1/1849 := by
  have hc : Finset.univ.filter (fun t : Fin 43 => sync t ∈ ({(0,0)} : Finset _)) = {0} := by
    ext t
    simp [sync]
  constructor
  · unfold frequency
    rw [hc]
    norm_num
  · constructor <;> norm_num

/-- The rational counterparts of the exact existing cost definitions. -/
def tollQ : ℚ := 334/(32^3*5*172)
def marginQ : ℚ := 1/(31*6*43^2)

theorem rational_costs_match :
    (tollQ : ℝ) = PMArch.tollTerm PMArch.baseline ∧
    (marginQ : ℝ) = PMArch.marginTerm PMArch.baseline := by
  norm_num [tollQ, marginQ, PMArch.tollTerm, PMArch.marginTerm, PMArch.baseline,
    PMArch.Parameters.nodeCapacity, PMArch.Parameters.resolution,
    PMArch.Parameters.embeddingLoad, PMArch.Parameters.intrinsicLoad]

theorem reduced_cost_fractions : tollQ = 167/14090240 ∧ marginQ = 1/343914 := by
  norm_num [tollQ, marginQ]

/-- The paper's stated finite configuration spaces. Neither their physical
selection nor the selected event is derived here. -/
abbrev TollSample := PMArch.ProtocolToll.Trial 32 5 172
abbrev MarginSample := Fin 31 × Fin 6 × Fin 43 × Fin 43

def selectedTollEvent : Finset TollSample :=
  PMArch.ProtocolToll.event (N := 32) (σ := 5) (R := 172) (χ := 2)
    (by decide) (by decide) (by decide) (by decide)

theorem selected_sample_sizes :
    Fintype.card TollSample = 28180480 ∧ Fintype.card MarginSample = 343914 := by
  norm_num [TollSample, MarginSample, PMArch.ProtocolToll.Trial]

/-- An actual autonomous one-cycle update realizes the stated Toll frequency
on the stated sample space/event. This replaces a uniform probabilistic prior
with a complete-orbit dynamical condition, not with a necessity proof. -/
theorem toll_dynamic_realization :
    ∃ orbit : Fin (Fintype.card TollSample) ≃ TollSample,
      frequency (fun t : Fin (Fintype.card TollSample) =>
        ((orbitAdvance orbit)^[t.val]) (orbit ⟨0, Fintype.card_pos⟩)) selectedTollEvent =
        tollQ := by
  haveI : NeZero (Fintype.card TollSample) := ⟨Fintype.card_ne_zero⟩
  let orbit : Fin (Fintype.card TollSample) ≃ TollSample := (Fintype.equivFin TollSample).symm
  refine ⟨orbit, ?_⟩
  have hz : (⟨0, Fintype.card_pos⟩ : Fin (Fintype.card TollSample)) = 0 := by
    exact fin_mk_zero _
  rw [hz, actual_clock_frequency]
  unfold selectedTollEvent
  rw [PMArch.ProtocolToll.event_count]
  norm_num [TollSample, PMArch.ProtocolToll.Trial, tollQ]

/-- A separate autonomous one-cycle update realizes the stated Margin
singleton frequency. This does not establish independence in a shared vacuum
sampler, or select the physical meaning of its singleton. -/
theorem margin_dynamic_realization :
    ∃ orbit : Fin (Fintype.card MarginSample) ≃ MarginSample,
      frequency (fun t : Fin (Fintype.card MarginSample) =>
        ((orbitAdvance orbit)^[t.val]) (orbit ⟨0, Fintype.card_pos⟩)) {(0,0,0,0)} =
        marginQ := by
  haveI : NeZero (Fintype.card MarginSample) := ⟨Fintype.card_ne_zero⟩
  let orbit : Fin (Fintype.card MarginSample) ≃ MarginSample :=
    (Fintype.equivFin MarginSample).symm
  refine ⟨orbit, ?_⟩
  have hz : (⟨0, Fintype.card_pos⟩ : Fin (Fintype.card MarginSample)) = 0 := by
    exact fin_mk_zero _
  rw [hz, actual_clock_frequency]
  norm_num [MarginSample, marginQ]

/-- An exact rational event frequency over a uniform cycle has reduced
denominator dividing that cycle length. This is not a bound for arbitrary
nonuniform, stochastic, or quantum probability laws. -/
theorem event_denominator_divides (k N p q : ℕ) (hN : N ≠ 0) (hq : q ≠ 0)
    (hcop : p.Coprime q) (h : (k : ℚ)/N = (p : ℚ)/q) : q ∣ N := by
  have hNr : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hqr : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have he := (div_eq_div_iff hNr hqr).mp h
  have hn : k*q = p*N := by exact_mod_cast he
  have hd : q ∣ p*N := by
    rw [← hn]
    exact dvd_mul_left q k
  exact hcop.symm.dvd_of_dvd_mul_left hd

theorem toll_cycle_divisibility (k N : ℕ) (hN : N ≠ 0)
    (h : (k : ℚ)/N = tollQ) : 14090240 ∣ N := by
  apply event_denominator_divides k N 167 14090240 hN (by decide) (by decide)
  simpa using h.trans reduced_cost_fractions.1

theorem margin_cycle_divisibility (k N : ℕ) (hN : N ≠ 0)
    (h : (k : ℚ)/N = marginQ) : 343914 ∣ N := by
  apply event_denominator_divides k N 1 343914 hN (by decide) (by decide)
  simpa using h.trans reduced_cost_fractions.2

theorem phase_only_cannot_realize_costs (k : ℕ) :
    (k : ℚ)/43 ≠ tollQ ∧ (k : ℚ)/43 ≠ marginQ := by
  constructor
  · intro h
    have hd := toll_cycle_divisibility k 43 (by decide) h
    norm_num at hd
  · intro h
    have hd := margin_cycle_divisibility k 43 (by decide) h
    norm_num at hd

/-- A deterministic event of the single 43-phase clock cannot have either
cost value. Other internal states, weights or a different observation process
could change this conclusion and must be specified, not silently excluded. -/
theorem clock_event_obstruction (E : Finset (Fin 43)) :
    frequency (Equiv.refl (Fin 43)) E ≠ tollQ ∧
    frequency (Equiv.refl (Fin 43)) E ≠ marginQ := by
  simp only [full_orbit_frequency]
  exact phase_only_cannot_realize_costs E.card

theorem shared_cycle_divisibility (k j N : ℕ) (hN : N ≠ 0)
    (ht : (k : ℚ)/N = tollQ) (hm : (j : ℚ)/N = marginQ) :
    56346869760 ∣ N := by
  have hd := Nat.lcm_dvd (toll_cycle_divisibility k N hN ht)
    (margin_cycle_divisibility j N hN hm)
  have he : Nat.lcm 14090240 343914 = 56346869760 := by decide
  rw [he] at hd
  exact hd

end PMArch.SamplingDynamics
