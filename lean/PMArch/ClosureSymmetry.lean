import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Closure leaves no preferred label

Under Closure nothing outside the substrate can single out a label. If the substrate itself
cannot distinguish the labels of a finite set (every relabeling is a symmetry), then:

* `invariant_set`: any internally defined admissible set of labels is empty or everything;
* `invariant_measure_uniform`: any internally defined probability on the labels is uniform.

These replace two choices in Toll and Margin — "each leg samples the whole node channel set"
and "the prior is uniform" — by one persistence premise: no label is distinguishable without
external information.

Where the substrate's symmetries are known, the premise is checked instead of assumed. On the
32 channel labels the sector-preserving automorphisms of `E₈` act transitively, so invariance
under them alone forces the uniform measure (`ChannelSymmetry.invariant_uniform`); on the `Δ`
clock slots the clock advance does (`ImpedanceTerms.governor_uniform`). The `σ` interaction
directions (three spatial positions and two boundary points, which are of different kinds), the
residual target addresses and Margin's configurations have no such symmetry. For those the
uniform measure follows without symmetry from persistence: it is the unique law that guarantees
the most persistence whichever label is the reference (`PersistenceMaximin.maximin_iff`).
-/

namespace PMArch.ClosureSymmetry

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A set of labels fixed by every relabeling is empty or the whole set. -/
theorem invariant_set (S : Finset α) (h : ∀ σ : Equiv.Perm α, S.map σ.toEmbedding = S) :
    S = ∅ ∨ S = Finset.univ := by
  by_contra hc
  push Not at hc
  obtain ⟨a, ha⟩ := hc.1
  obtain ⟨b, hb⟩ : ∃ b, b ∉ S := by
    by_contra hb; push Not at hb; exact hc.2 (Finset.eq_univ_of_forall hb)
  have := h (Equiv.swap a b)
  have hmem : Equiv.swap a b a ∈ S.map (Equiv.swap a b).toEmbedding :=
    Finset.mem_map_of_mem _ ha
  rw [this, Equiv.swap_apply_left] at hmem
  exact hb hmem

/-- A probability on labels fixed by every relabeling is uniform. -/
theorem invariant_measure_uniform (p : α → ℝ) (h : ∀ σ : Equiv.Perm α, ∀ a, p (σ a) = p a)
    (hsum : ∑ a, p a = 1) (a : α) : p a = 1 / Fintype.card α := by
  have hconst : ∀ b, p b = p a := fun b => by simpa using h (Equiv.swap a b) a
  have hcard : (Fintype.card α : ℝ) * p a = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun b _ => hconst b)]; simp
  have hne : (Fintype.card α : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hcard; exact zero_ne_one hcard
  rw [eq_div_iff hne, mul_comm]; exact hcard

end PMArch.ClosureSymmetry
