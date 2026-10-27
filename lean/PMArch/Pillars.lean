import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Counterfactual failure modes of the six pillars

Formal versions of the failure modes in *Persistence Mechanics*, §"Necessity: Counterfactual
Failure Modes". For each pillar, under explicit discrete-time dynamics, we prove

* **with the pillar**: its mechanism excludes the characteristic failure, and
* **without it**: an explicit trajectory exhibits that failure.

These are modeling statements: each pillar is represented by one standard mechanism (intake,
distance to the non-viable set, reference-based correction, inter-component exchange, a positive
toll per transition, a bound on feedback). They do not prove the completeness conjecture, and the
failures obtained are *finite* lifetimes or *admissible* collapses, not `τ → 0` in general.
-/

namespace PMArch.Pillars

/-! ## Capacity (Finiteness, provision): starvation -/

/-- **No Capacity.** With a reserve consumed at rate at least `d > 0` and no intake, the
reserve is exhausted by step `max(r₀ / d, 0) + 1`. -/
theorem starvation {r : ℕ → ℝ} {d : ℝ} (hd : 0 < d) (hstep : ∀ t, r (t + 1) ≤ r t - d) :
    ∃ T : ℕ, (T : ℝ) ≤ max (r 0 / d) 0 + 1 ∧ r T < 0 := by
  have h : ∀ t : ℕ, r t ≤ r 0 - t * d := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => have := hstep t; push_cast; linarith
  refine ⟨⌊r 0 / d⌋₊ + 1, ?_, ?_⟩
  · push_cast
    by_cases h0 : 0 ≤ r 0 / d
    · linarith [Nat.floor_le h0, le_max_left (r 0 / d) 0]
    · rw [Nat.floor_eq_zero.mpr (by linarith)]; push_cast; linarith [le_max_right (r 0 / d) 0]
  · have hlt : r 0 / d < ((⌊r 0 / d⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hd] at hlt
    linarith [h (⌊r 0 / d⌋₊ + 1)]

/-- **With Capacity.** If intake covers consumption at every step, the reserve never runs out. -/
theorem capacity_sustains {r i : ℕ → ℝ} {d : ℝ} (h0 : 0 ≤ r 0) (hi : ∀ t, d ≤ i t)
    (hstep : ∀ t, r (t + 1) = r t - d + i t) : ∀ t, 0 ≤ r t := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih => rw [hstep]; linarith [hi t]

/-! ## Margin (Finiteness, defense): fragility -/

section Margin
variable {E : Type*} [NormedAddCommGroup E]

/-- **Margin is exactly distance to the non-viable set.** A state tolerates every perturbation
smaller than some positive `m` iff its distance to the non-viable set is positive. -/
theorem margin_iff (V : Set E) (x : E) (hne : Vᶜ.Nonempty) :
    (∃ m > 0, ∀ δ : E, ‖δ‖ < m → x + δ ∈ V) ↔ 0 < Metric.infDist x Vᶜ := by
  constructor
  · rintro ⟨m, hm, hV⟩
    by_contra h
    have h0 : Metric.infDist x Vᶜ < m := by
      have := Metric.infDist_nonneg (x := x) (s := Vᶜ); linarith
    obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff hne).mp h0
    have := hV (y - x) (by rw [← dist_eq_norm, dist_comm]; exact hxy)
    rw [add_sub_cancel] at this
    exact hy this
  · intro h
    refine ⟨_, h, fun δ hδ => ?_⟩
    by_contra hx
    have := Metric.infDist_le_dist_of_mem (x := x) (show x + δ ∈ Vᶜ from hx)
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg] at this
    linarith

/-- **No Margin.** At zero distance from the non-viable set, arbitrarily small perturbations are
fatal. -/
theorem fragility (V : Set E) (x : E) (hne : Vᶜ.Nonempty) (h0 : Metric.infDist x Vᶜ = 0) :
    ∀ ε > 0, ∃ δ : E, ‖δ‖ < ε ∧ x + δ ∉ V := by
  intro ε hε
  by_contra h
  push Not at h
  have := (margin_iff V x hne).mp ⟨ε, hε, h⟩
  linarith

end Margin

/-! ## Map and Protocol (Conservation): dissolution and decoherence -/

/-- Proportional correction with gain `k ∈ (0, 1]` keeps a deviation bounded under bounded
disturbances. -/
theorem correction_bounded {x w : ℕ → ℝ} {k W : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hw : ∀ t, |w t| ≤ W) (h : ∀ t, x (t + 1) = (1 - k) * x t + w t) :
    ∀ t, |x t| ≤ max |x 0| (W / k) := by
  intro t
  induction t with
  | zero => exact le_max_left _ _
  | succ t ih =>
    rw [h]
    set M := max |x 0| (W / k)
    have hM : W / k ≤ M := le_max_right _ _
    have hW : W ≤ k * M := by rwa [div_le_iff₀ hk0, mul_comm] at hM
    calc |(1 - k) * x t + w t| ≤ |(1 - k) * x t| + |w t| := abs_add_le _ _
      _ = (1 - k) * |x t| + |w t| := by rw [abs_mul, abs_of_nonneg (by linarith)]
      _ ≤ (1 - k) * M + W := by
        have := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ 1 - k by linarith)
        linarith [hw t]
      _ ≤ M := by linarith

/-- An uncorrected persistent disturbance accumulates without bound. -/
theorem drift_unbounded {x : ℕ → ℝ} {w : ℝ} (hw : 0 < w) (h : ∀ t, x (t + 1) = x t + w) :
    ∀ B, ∃ t, B < x t := by
  have hx : ∀ t : ℕ, x t = x 0 + t * w := by
    intro t; induction t with
    | zero => simp
    | succ t ih => rw [h, ih]; push_cast; ring
  intro B
  obtain ⟨t, ht⟩ := exists_nat_gt ((B - x 0) / w)
  refine ⟨t, ?_⟩
  rw [hx, ← sub_lt_iff_lt_add']
  rwa [div_lt_iff₀ hw] at ht

/-- **With Map.** The deviation `e = x - r` from a retained reference `r`, corrected with gain
`k`, stays bounded under bounded disturbances. -/
theorem map_maintains {x w : ℕ → ℝ} {r k W : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hw : ∀ t, |w t| ≤ W) (h : ∀ t, x (t + 1) = x t - k * (x t - r) + w t) :
    ∀ t, |x t - r| ≤ max |x 0 - r| (W / k) :=
  correction_bounded (x := fun t => x t - r) hk0 hk1 hw (fun t => by rw [h]; ring)

/-- **No Map.** Without a reference there is nothing to correct toward; a persistent
disturbance carries the state past any boundary. -/
theorem dissolution {x : ℕ → ℝ} {w : ℝ} (hw : 0 < w) (h : ∀ t, x (t + 1) = x t + w) :
    ∀ B, ∃ t, B < x t :=
  drift_unbounded hw h

/-- **With Protocol.** Two replicas with independent bounded disturbances that exchange state
with gain `k ∈ (0, 1/2]` keep their disagreement bounded. -/
theorem protocol_coheres {a b u v : ℕ → ℝ} {k W : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1 / 2)
    (hu : ∀ t, |u t| ≤ W) (hv : ∀ t, |v t| ≤ W)
    (ha : ∀ t, a (t + 1) = a t + k * (b t - a t) + u t)
    (hb : ∀ t, b (t + 1) = b t + k * (a t - b t) + v t) :
    ∀ t, |a t - b t| ≤ max |a 0 - b 0| (2 * W / (2 * k)) := by
  refine correction_bounded (x := fun t => a t - b t) (w := fun t => u t - v t)
    (by linarith) (by linarith) (fun t => ?_) (fun t => by rw [ha, hb]; ring)
  calc |u t - v t| ≤ |u t| + |v t| := abs_sub _ _
    _ ≤ 2 * W := by linarith [hu t, hv t]

/-- **No Protocol.** Without exchange, replicas subject to differing persistent disturbances
drift apart without bound. -/
theorem decoherence {a b : ℕ → ℝ} {u v : ℝ} (huv : v < u)
    (ha : ∀ t, a (t + 1) = a t + u) (hb : ∀ t, b (t + 1) = b t + v) :
    ∀ B, ∃ t, B < a t - b t :=
  drift_unbounded (x := fun t => a t - b t) (sub_pos.mpr huv) (fun t => by rw [ha, hb]; ring)

/-! ## Toll (Causality, provision): Zeno collapse -/

/-- **With Toll.** If every transition takes at least `c > 0`, then `n` transitions take at
least `n c`; only finitely many transitions fit in any bounded interval. -/
theorem toll_excludes_zeno {Δ : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (hΔ : ∀ k, c ≤ Δ k) (T : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, T < ∑ k ∈ Finset.range n, Δ k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (T / c)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : (n : ℝ) * c ≤ ∑ k ∈ Finset.range n, Δ k := by
    have := Finset.card_nsmul_le_sum (Finset.range n) Δ c (fun k _ => hΔ k)
    simpa using this
  have h2 : T < (n : ℝ) * c := by
    rw [div_lt_iff₀ hc] at hN
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  linarith

/-- **No Toll.** Without a positive lower bound on transition time, infinitely many transitions
can occur before time 1 (durations `2^{-(k+1)}`). Absence of a toll *permits*, rather than
forces, this collapse. -/
theorem zeno_without_toll : ∃ Δ : ℕ → ℝ, (∀ k, 0 < Δ k) ∧ ∀ n, ∑ k ∈ Finset.range n, Δ k < 1 := by
  refine ⟨fun k => (1 / 2 : ℝ) ^ (k + 1), fun k => by positivity, fun n => ?_⟩
  have : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) = 1 - (1 / 2) ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [this]
  have : (0 : ℝ) < (1 / 2) ^ n := by positivity
  linarith

/-! ## Governor (Causality, defense): divergence -/

/-- **No Governor.** Unconstrained positive feedback (`x ↦ a x`, `a > 1`) exceeds every bound
in finite time. -/
theorem runaway {x : ℕ → ℝ} {a : ℝ} (ha : 1 < a) (h0 : 0 < x 0) (h : ∀ t, x (t + 1) = a * x t) :
    ∀ B, ∃ t, B < x t := by
  have hx : ∀ t : ℕ, x t = a ^ t * x 0 := by
    intro t; induction t with
    | zero => simp
    | succ t ih => rw [h, ih]; ring
  intro B
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (B / x 0) ha
  refine ⟨t, ?_⟩
  rw [hx, ← div_lt_iff₀ h0]
  exact ht

/-- **With Governor.** A cap on the feedback keeps the state within its bound. -/
theorem governor_bounds {x : ℕ → ℝ} {a B : ℝ} (h0 : x 0 ≤ B)
    (h : ∀ t, x (t + 1) = min (a * x t) B) : ∀ t, x t ≤ B := by
  intro t
  cases t with
  | zero => exact h0
  | succ t => rw [h]; exact min_le_right _ _

end PMArch.Pillars
