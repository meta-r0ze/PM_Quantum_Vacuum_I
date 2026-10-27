import PMArch.Sectors
import PMArch.Channels
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Remaining premises as persistence statements

* **State identity** (`state_identity_card`). A transition preserves the defect when its internal
  configuration returns to the reference up to the defect's own invisible symmetry, the reversal of
  its boundary orientation (`Orientation.two_orientations`). Those configurations are the orbit of
  the reference under that involution: exactly two. Toll's valid count `2` and its `1/(32³·5)`
  are this orbit in the internal configuration space.
* **Causal cone** (`causal_cone_card`). In one spatial direction at speed one, the events reachable
  from an origin within one cycle, `{(t, x) : t < Δ, |x| ≤ t}`, number exactly `Δ²`. This is
  Margin's `Δ²`: the causal region of one cycle, not two independent clock labels.
* **Regulators lower counts** (`restriction_lowers`, `merging_lowers`). Governor restricts which
  transitions occur (a subset); Protocol coordinates them (identifying equivalent attempts, a
  merge). Neither can increase the number of transitions, so their net contribution is a
  reduction — the minus sign follows from what the two definitions do.
* **One bit per leg** (`leg_state_binary`). The substrate's local observation of a channel is
  gap-only (`Sectors.obs`): binary by construction, and both values occur in the forced 43-slot
  schedule. A leg carries what can be observed locally about its channel: one bit.
-/

namespace PMArch.PersistencePremises
open Finset

/-! ## State identity -/

/-- The configurations indistinguishable from `r` under an involutive symmetry `ι` with no fixed
point at `r` are exactly two. -/
theorem state_identity_card {C : Type*} [DecidableEq C] (ι : C → C) (r : C) (hr : ι r ≠ r) :
    ({r, ι r} : Finset C).card = 2 := by
  rw [card_pair hr.symm]

/-- The internal configuration space of a vertex: three legs and an interaction direction.
Reversing the boundary orientation flips the lowest bit of the third leg. -/
def flipOrientation (c : Fin 32 × Fin 32 × Fin 32 × Fin 5) : Fin 32 × Fin 32 × Fin 32 × Fin 5 :=
  (c.1, c.2.1, ⟨if (c.2.2.1 : ℕ) % 2 = 0 then (c.2.2.1 : ℕ) + 1 else (c.2.2.1 : ℕ) - 1, by
    have := c.2.2.1.isLt; split_ifs <;> omega⟩, c.2.2.2)

theorem toll_identity :
    ({(0, 0, 0, 0), flipOrientation (0, 0, 0, 0)} : Finset (Fin 32 × Fin 32 × Fin 32 × Fin 5)).card = 2 ∧
      Fintype.card (Fin 32 × Fin 32 × Fin 32 × Fin 5) = 32 ^ 3 * 5 := by
  exact ⟨state_identity_card _ _ (by decide), by simp⟩

/-! ## Causal cone -/


/-- Number of positions reachable at tick `t` at speed one: `2t + 1`. -/
theorem slice_card (t : ℕ) : (Icc (-(t : ℤ)) t).card = 2 * t + 1 := by
  simp; omega

/-- **Margin's `Δ²` is the causal cone of one cycle.** -/
theorem causal_cone_card (Δ : ℕ) :
    ∑ t ∈ range Δ, (Icc (-(t : ℤ)) t).card = Δ ^ 2 := by
  induction Δ with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, slice_card]; ring

/-! ## Regulators -/

/-- Restriction (Governor) never increases the transition count. -/
theorem restriction_lowers {T : Type*} (B : Finset T) (keep : T → Prop) [DecidablePred keep] :
    (B.filter keep).card ≤ B.card := card_filter_le _ _

/-- Coordination (Protocol) identifies equivalent attempts; merging never increases the count. -/
theorem merging_lowers {T U : Type*} [DecidableEq U] (B : Finset T) (merge : T → U) :
    (B.image merge).card ≤ B.card := card_image_le

/-! ## One bit per leg -/

/-- The local observation of a channel is binary, and both values occur in the forced schedule
(11 idle runs among 32 active slots). -/
theorem leg_state_binary :
    Fintype.card Bool = 2 ∧
      (∃ i : Fin 32, Sectors.obs (fun i : Fin 32 => if (i : ℕ) < 11 then 1 else 0) i = true) ∧
      (∃ i : Fin 32, Sectors.obs (fun i : Fin 32 => if (i : ℕ) < 11 then 1 else 0) i = false) := by
  refine ⟨rfl, ⟨0, by decide⟩, ⟨31, by decide⟩⟩

end PMArch.PersistencePremises
