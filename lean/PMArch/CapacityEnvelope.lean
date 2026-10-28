import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import PMArch.CapacityBarbier

/-!
# Capacity on convex envelopes

`CapacityBarbier` bounds `∫₀^{2π} h` over all continuous `h` with every width
`h θ + h (θ + π) ≤ Δ`. This module checks that the bound applies to actual planar envelopes and
that the width condition follows from a causal premise instead of being assumed.

* An `Envelope` is a nonempty compact convex set `S ⊆ ℝ²`. Its support function
  `support S θ = sup_{x ∈ S} ⟨x, (cos θ, sin θ)⟩` is defined from the points of `S`, and is
  continuous (`support_continuous`).
* `CausalDiameter S Δ`: any two points of the envelope are within distance `Δ` (a signal must
  cross and return within one cycle). `width_le` derives `support S θ + support S (θ + π) ≤ Δ`
  in every direction.
* `perimeter E := ∫₀^{2π} support E θ`. For a convex body this is its boundary length
  (Cauchy's formula). Cauchy's formula is **not proved here**; it is the identification of the
  boundary measure with the support integral, stated as the definition.
* `envelope_perimeter_le`: every causal envelope has perimeter `≤ πΔ`.
* `disk_support`, `disk_causal`: the disk of radius `Δ/2` has constant support `Δ/2` and
  diameter `Δ`, so `capacity_is_max_envelope` shows `πΔ = capacityTerm` is the maximum over
  causal envelopes and is attained.
-/

open Real intervalIntegral

namespace PMArch.Capacity

/-- The component of `x` in direction `θ`. -/
noncomputable def proj (θ : ℝ) (x : ℝ × ℝ) : ℝ := x.1 * cos θ + x.2 * sin θ

/-- Support function of a planar set. -/
noncomputable def support (S : Set (ℝ × ℝ)) (θ : ℝ) : ℝ := sSup (proj θ '' S)

/-- A planar envelope: nonempty, compact and convex. -/
structure Envelope where
  carrier : Set (ℝ × ℝ)
  nonempty : carrier.Nonempty
  compact : IsCompact carrier
  convex : Convex ℝ carrier

/-- Causal premise: every two points of the envelope are within distance `Δ`. -/
def CausalDiameter (S : Set (ℝ × ℝ)) (Δ : ℝ) : Prop :=
  0 ≤ Δ ∧ ∀ x ∈ S, ∀ y ∈ S, (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2 ≤ Δ ^ 2

/-- Boundary measure of a convex envelope, by Cauchy's formula (taken as the definition). -/
noncomputable def perimeter (E : Envelope) : ℝ := ∫ θ in (0)..(2 * π), support E.carrier θ

lemma proj_sq_le (θ a b : ℝ) : (a * cos θ + b * sin θ) ^ 2 ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a * sin θ - b * cos θ), sin_sq_add_cos_sq θ]

lemma proj_add_pi (θ : ℝ) (x : ℝ × ℝ) : proj (θ + π) x = - proj θ x := by
  simp only [proj, cos_add_pi, sin_add_pi]; ring

lemma continuous_proj : Continuous fun p : ℝ × (ℝ × ℝ) => proj p.1 p.2 := by
  unfold proj; fun_prop

theorem support_continuous (E : Envelope) : Continuous (support E.carrier) :=
  E.compact.continuous_sSup (f := fun θ x => proj θ x) continuous_proj

lemma bdd (E : Envelope) (θ : ℝ) : BddAbove (proj θ '' E.carrier) :=
  E.compact.bddAbove_image (continuous_proj.comp
    (Continuous.prodMk continuous_const continuous_id)).continuousOn

lemma le_support (E : Envelope) (θ : ℝ) {x : ℝ × ℝ} (hx : x ∈ E.carrier) :
    proj θ x ≤ support E.carrier θ :=
  le_csSup (bdd E θ) ⟨x, hx, rfl⟩

/-- **The causal premise bounds every width.** -/
theorem width_le (E : Envelope) {Δ : ℝ} (hΔ : CausalDiameter E.carrier Δ) (θ : ℝ) :
    support E.carrier θ + support E.carrier (θ + π) ≤ Δ := by
  have key : ∀ x ∈ E.carrier, ∀ y ∈ E.carrier, proj θ x + proj (θ + π) y ≤ Δ := by
    intro x hx y hy
    rw [proj_add_pi]
    have h1 := proj_sq_le θ (x.1 - y.1) (x.2 - y.2)
    have h2 := hΔ.2 x hx y hy
    have e : proj θ x + -proj θ y = (x.1 - y.1) * cos θ + (x.2 - y.2) * sin θ := by
      simp only [proj]; ring
    rw [e]
    nlinarith [hΔ.1]
  have hne := E.nonempty
  have hb : ∀ y ∈ E.carrier, support E.carrier θ ≤ Δ - proj (θ + π) y := fun y hy =>
    csSup_le (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; linarith [key x hx y hy])
  have : support E.carrier (θ + π) ≤ Δ - support E.carrier θ :=
    csSup_le (hne.image _) (by rintro _ ⟨y, hy, rfl⟩; linarith [hb y hy])
  linarith

/-- **Every causal envelope has perimeter at most `πΔ`.** -/
theorem envelope_perimeter_le (E : Envelope) {Δ : ℝ} (hΔ : CausalDiameter E.carrier Δ) :
    perimeter E ≤ π * Δ :=
  perimeter_le _ (support_continuous E) Δ (width_le E hΔ)

/-! ## The disk -/

/-- The closed disk of radius `r` about the origin. -/
def disk (r : ℝ) : Set (ℝ × ℝ) := {x | x.1 ^ 2 + x.2 ^ 2 ≤ r ^ 2}

lemma disk_convex (r : ℝ) : Convex ℝ (disk r) := by
  intro x hx y hy a b ha hb hab
  simp only [disk, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at *
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg ha hb, sq_nonneg (x.1 - y.1), sq_nonneg (x.2 - y.2)]

lemma disk_compact {r : ℝ} (hr : 0 ≤ r) : IsCompact (disk r) := by
  refine (isCompact_closedBall (0 : ℝ × ℝ) r).of_isClosed_subset ?_ ?_
  · exact isClosed_le (by fun_prop) continuous_const
  · intro x hx
    simp only [disk, Set.mem_ofPred_eq] at hx
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      Real.norm_eq_abs]
    refine max_le (abs_le.mpr ⟨?_, ?_⟩) (abs_le.mpr ⟨?_, ?_⟩) <;>
      nlinarith [sq_nonneg x.1, sq_nonneg x.2]

/-- The disk as an envelope. -/
def diskEnvelope {r : ℝ} (hr : 0 ≤ r) : Envelope where
  carrier := disk r
  nonempty := ⟨0, by simp [disk]; positivity⟩
  compact := disk_compact hr
  convex := disk_convex r

theorem disk_support {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : support (disk r) θ = r := by
  apply le_antisymm
  · apply csSup_le ((diskEnvelope hr).nonempty.image _)
    rintro _ ⟨x, hx, rfl⟩
    change x.1 ^ 2 + x.2 ^ 2 ≤ r ^ 2 at hx
    have := proj_sq_le θ x.1 x.2
    simp only [proj]
    nlinarith
  · have hm : (r * cos θ, r * sin θ) ∈ disk r := by
      simp only [disk, Set.mem_ofPred_eq]; nlinarith [sin_sq_add_cos_sq θ]
    have h1 : proj θ (r * cos θ, r * sin θ) ≤ support (disk r) θ :=
      le_support (diskEnvelope hr) θ hm
    have e : proj θ (r * cos θ, r * sin θ) = r := by
      simp only [proj]; linear_combination r * sin_sq_add_cos_sq θ
    linarith

theorem disk_causal {Δ : ℝ} (hΔ : 0 ≤ Δ) : CausalDiameter (disk (Δ / 2)) Δ := by
  refine ⟨hΔ, fun x hx y hy => ?_⟩
  simp only [disk, Set.mem_ofPred_eq] at hx hy
  nlinarith [sq_nonneg (x.1 + y.1), sq_nonneg (x.2 + y.2)]

theorem disk_perimeter {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    perimeter (diskEnvelope (by linarith : (0 : ℝ) ≤ Δ / 2)) = π * Δ := by
  have hf : support (disk (Δ / 2)) = fun _ => Δ / 2 := funext (disk_support (by linarith))
  change ∫ θ in (0)..(2 * π), support (disk (Δ / 2)) θ = π * Δ
  rw [hf, barbier _ continuous_const Δ (fun θ => by ring)]

/-- **Capacity is the causal maximum over convex envelopes.** Every compact convex envelope
whose diameter respects the causal bound `Δ` has perimeter at most `πΔ = capacityTerm`, and the
disk of diameter `Δ` attains it. Cauchy's formula (perimeter = support integral) is the one
geometric identification not proved here. -/
theorem capacity_is_max_envelope (p : Parameters) :
    (∀ E : Envelope, CausalDiameter E.carrier p.period → perimeter E ≤ capacityTerm p) ∧
      ∃ E : Envelope, CausalDiameter E.carrier p.period ∧ perimeter E = capacityTerm p := by
  have hΔ : (0 : ℝ) ≤ p.period := Nat.cast_nonneg _
  have hcap : capacityTerm p = π * p.period := rfl
  refine ⟨fun E hE => hcap ▸ envelope_perimeter_le E hE,
    diskEnvelope (by linarith : (0 : ℝ) ≤ p.period / 2), disk_causal hΔ, ?_⟩
  rw [hcap, disk_perimeter hΔ]

end PMArch.Capacity
