import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Ring.Int.Units
import PMArch.ClosureSymmetry
import PMArch.Impedance
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# What persists: legs, orientations and the correction terms

Each remaining choice in the index is tested by asking what can persist.

* **Three legs** (`Arity`). Closure: the legs carry no external labels, so the update treats them
  symmetrically. Conservation: it is reversible. With one-bit legs (channel occupancy),
  `two_legs_separable` shows every such two-leg update is a common relabeling of each leg,
  possibly followed by exchanging them — no leg depends on another, so nothing is coordinated.
  `three_legs_interact` exhibits a symmetric reversible three-leg update that is not of that
  form. Economy then takes the least arity that interacts: three.
* **Two orientations** (`Orientation`). An orientation assigns a sign to each face, glued
  consistently across shared edges. `two_orientations`: a connected orientable boundary has
  exactly two, `s` and `−s`, whatever its genus. This is the third Toll leg's factor `2`.
* **Corrections as probabilities** (`corrections_as_probabilities`). Under Closure the measure
  on any finite label set with no internally preferred element is uniform
  (`ClosureSymmetry.invariant_measure_uniform`). Each correction term is then the probability of a
  persistence event: Protocol `1/167` (one residual address), Governor `2/43` (the `χ` boundary
  slots in a cycle), Toll `334/(32³·5·172)` (a valid transition), Margin `1/(31·6·43²)` (one
  configuration).
-/

namespace PMArch.Arity

/-- Exchange of the two legs. -/
def swap2 (x : Bool × Bool) : Bool × Bool := (x.2, x.1)

/-- **Two binary legs cannot interact.** A reversible two-leg update that does not depend on
which leg is which is a relabeling of each leg by the same map, possibly followed by exchanging
the legs: no leg's outcome depends on the other. -/
theorem two_legs_separable :
    ∀ f : Equiv.Perm (Bool × Bool), (∀ x, f (swap2 x) = swap2 (f x)) →
      ∃ g : Equiv.Perm Bool, (∀ a b, f (a, b) = (g a, g b)) ∨ (∀ a b, f (a, b) = (g b, g a)) := by
  decide

/-- The two generating exchanges of three legs. -/
def s12 (x : Bool × Bool × Bool) : Bool × Bool × Bool := (x.2.1, x.1, x.2.2)
def s23 (x : Bool × Bool × Bool) : Bool × Bool × Bool := (x.1, x.2.2, x.2.1)

/-- The three-leg vertex that exchanges "all off" with "all on" and fixes everything else. -/
def vertex : Equiv.Perm (Bool × Bool × Bool) := Equiv.swap (false, false, false) (true, true, true)

/-- **Three binary legs can interact.** `vertex` is reversible, treats the legs symmetrically,
and is not a common relabeling of the legs composed with any leg exchange. -/
theorem three_legs_interact :
    (∀ x, vertex (s12 x) = s12 (vertex x)) ∧ (∀ x, vertex (s23 x) = s23 (vertex x)) ∧
      ∀ g : Equiv.Perm Bool, ∀ π : Equiv.Perm (Fin 3), ¬ ∀ x : Fin 3 → Bool,
        (vertex (x 0, x 1, x 2)).1 = g (x (π 0)) ∧
        (vertex (x 0, x 1, x 2)).2.1 = g (x (π 1)) ∧ (vertex (x 0, x 1, x 2)).2.2 = g (x (π 2)) := by
  decide

/-- **The one-bit premise is load-bearing.** With three-valued legs a symmetric reversible
two-leg update already couples the legs. -/
def tvertex : Equiv.Perm (Fin 3 × Fin 3) :=
  Equiv.swap (0, 1) (1, 2) * Equiv.swap (1, 0) (2, 1)

theorem three_valued_two_legs_interact :
    (∀ x : Fin 3 × Fin 3, tvertex (x.2, x.1) = ((tvertex x).2, (tvertex x).1)) ∧
      ∀ g : Equiv.Perm (Fin 3),
        ¬ ((∀ a b, tvertex (a, b) = (g a, g b)) ∨ (∀ a b, tvertex (a, b) = (g b, g a))) := by
  decide

end PMArch.Arity

namespace PMArch.Orientation

variable {V : Type*} (G : SimpleGraph V)

/-- An orientation of a face-adjacency structure: a sign per face, related across each shared
edge by the gluing sign `ε`. -/
def IsOrientation (ε : V → V → ℤˣ) (s : V → ℤˣ) : Prop := ∀ u v, G.Adj u v → s u = ε u v * s v

variable {G}

lemma ratio_const {ε : V → V → ℤˣ} {s t : V → ℤˣ} (hs : IsOrientation G ε s)
    (ht : IsOrientation G ε t) {u v : V} (h : G.Reachable u v) : t u * (s u)⁻¹ = t v * (s v)⁻¹ := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    rw [← ih, hs _ _ hadj, ht _ _ hadj, mul_inv_rev]
    generalize ε _ _ = a; generalize t _ = b; generalize s _ = c
    rw [mul_comm c⁻¹, ← mul_assoc, mul_assoc a, mul_comm b, ← mul_assoc, mul_inv_cancel, one_mul]

/-- **A connected orientable boundary has exactly two orientations.** If `s` is an orientation,
the orientations are exactly `s` and `-s`, and these differ. -/
theorem two_orientations (hG : G.Connected) {ε : V → V → ℤˣ} {s : V → ℤˣ}
    (hs : IsOrientation G ε s) :
    IsOrientation G ε (fun v => -s v) ∧ (fun v => -s v) ≠ s ∧
      ∀ t, IsOrientation G ε t → t = s ∨ t = fun v => -s v := by
  refine ⟨fun u v h => by simp only [hs u v h, mul_neg], ?_, fun t ht => ?_⟩
  · intro h
    obtain ⟨v⟩ := hG.nonempty
    have := congrFun h v
    rcases Int.units_eq_one_or (s v) with h1 | h1 <;> rw [h1] at this <;> exact absurd this (by decide)
  · obtain ⟨v0⟩ := hG.nonempty
    have hc : ∀ v, t v * (s v)⁻¹ = t v0 * (s v0)⁻¹ := fun v => ratio_const hs ht (hG.preconnected v v0)
    rcases Int.units_eq_one_or (t v0 * (s v0)⁻¹) with h1 | h1
    · left; funext v; have := hc v; rw [h1] at this; exact (mul_inv_eq_one.mp this)
    · right; funext v; have := hc v; rw [h1] at this
      rw [mul_inv_eq_iff_eq_mul] at this; rw [this]; simp
end PMArch.Orientation

namespace PMArch.PersistenceEvents

/-- Uniform mass of an event `E ⊆ Ω`. -/
noncomputable def mass {Ω : Type*} [Fintype Ω] (E : Finset Ω) : ℝ := E.card / Fintype.card Ω

/-- **The four correction terms are probabilities of persistence events** under the uniform
measure forced by Closure, with the forced baseline integers. -/
theorem corrections_as_probabilities :
    mass ({0} : Finset (Fin 167)) = 1 / 167 ∧
    mass (Finset.univ.filter fun i : Fin 43 => (i : ℕ) < 2) = 2 / 43 ∧
    mass ({0} : Finset (Fin 31 × Fin 6 × Fin 43 × Fin 43)) = 1 / (31 * 6 * 43 ^ 2) ∧
    -protocolTerm baseline = 1 / 167 ∧ -governorTerm baseline = 2 / 43 ∧
    marginTerm baseline = 1 / (31 * 6 * 43 ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mass]
  · simp only [mass, Fintype.card_fin]
    rw [show (Finset.univ.filter fun i : Fin 43 => (i : ℕ) < 2).card = 2 by decide]; norm_num
  · simp [mass, Fintype.card_prod]; norm_num
  · norm_num [protocolTerm, baseline, Parameters.resolution]
  · norm_num [governorTerm, baseline]
  · norm_num [marginTerm, baseline, Parameters.embeddingLoad, Parameters.intrinsicLoad]

/-- **Toll as the probability that a transition persists** (the original three filters).
Internal configuration: three legs (32 channels each) and an interaction direction (σ = 5).
* State identity (Conservation): two legs and the direction return to the reference
  configuration — one choice each.
* Flux orientation: the third leg carries the boundary orientation, either of the two
  (`Orientation.two_orientations`).
* Non-aliasing (Causality): the target address avoids the σ embedded addresses
  (`TollFilters.nonaliasing_prob`).
Under the uniform measure the probability is the product. On the channel labels the uniform
measure is forced by the substrate's symmetries (`ChannelSymmetry.invariant_uniform`); on the
`σ` directions and the target address it is the law that persists best for every reference
(`PersistenceMaximin.toll_maximin`, which also derives the independence of the filters). -/
theorem toll_persistence :
    tollTerm baseline =
      (((({0} : Finset (Fin 32)) ×ˢ ({0} : Finset (Fin 32)) ×ˢ
          (Finset.univ.filter fun o : Fin 32 => (o : ℕ) < 2) ×ˢ ({0} : Finset (Fin 5))).card : ℝ) /
        Fintype.card (Fin 32 × Fin 32 × Fin 32 × Fin 5)) *
      (((172 : ℝ) - 5) / 172) := by
  simp only [Finset.card_product, Finset.card_singleton, Fintype.card_prod, Fintype.card_fin]
  rw [show (Finset.univ.filter fun o : Fin 32 => (o : ℕ) < 2).card = 2 by decide]
  norm_num [tollTerm, baseline, Parameters.nodeCapacity, Parameters.resolution]

/-- **Protocol as the probability of the one successor.** The update is a function
(Conservation, Postulate R), so a state has exactly one successor address. Coordinating it among
the 167 residual addresses without an external pointer succeeds with the uniform probability of
that single address, `2^(−I)` with `I = log₂ 167` the information needed to name it. -/
theorem protocol_persistence {X : Type*} (f : X → Fin 167) (x : X) :
    ({f x} : Finset (Fin 167)).card = 1 ∧ -protocolTerm baseline = mass ({f x} : Finset (Fin 167)) ∧
      mass ({f x} : Finset (Fin 167)) = (2 : ℝ) ^ (-Real.logb 2 167) := by
  refine ⟨Finset.card_singleton _, ?_, ?_⟩
  · simp [mass]; norm_num [protocolTerm, baseline, Parameters.resolution]
  · rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
    simp [mass]

end PMArch.PersistenceEvents
