import PMArch.Impedance
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Signs and unit weights from the PM cost of persistence

PM defines the operational cost rate as toll × frequency of transitions (`Z ≈ c₀ f`), sums
pillar costs (`Z_net = Σ Zᵢ`) and only then exponentiates for survival (`P = exp(−β S)`).
Read this way, every term of the index is an **expected number of transitions per cycle**:

* `expected_count_linear`: the expected count of transitions from several indicator events is
  the sum of their probabilities — linearity of expectation. Terms therefore add with unit
  weight, and a probability enters as itself (an expected count), not as `−log p`. The single
  weight is the toll `c₀`, the cost of one transition, set to one by Closure (no external unit).
* `removal_subtracts`: Governor (restricts which transitions occur) and Protocol (coordinates
  transitions, replacing uncoordinated ones) are defined by their action on *other* pillars'
  transitions. A transition they remove from the baseline lowers the count by its probability:
  this is the minus sign. The other four pillars provision or spend; their transitions add.
* `survival_factorizes`: with hazard `β · Z_net`, the per-cycle survival factor is the product of
  per-pillar factors `exp(−β Zᵢ)`; the exponential sits outside the sum, which is why the sum
  itself is linear.
-/

noncomputable section
namespace PMArch.NetCost
open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Probability of an event under the uniform measure on a cycle's label space. -/
def prob (E : Finset Ω) : ℝ := E.card / Fintype.card Ω

/-- Expected number of transitions in a cycle, each event contributing one transition of toll
`c₀` when it occurs. -/
def expectedCost (c₀ : ℝ) {k : ℕ} (E : Fin k → Finset Ω) : ℝ :=
  (∑ ω, c₀ * ∑ i, if ω ∈ E i then (1 : ℝ) else 0) / Fintype.card Ω

/-- **Linearity**: costs of independent pillar events add, each with weight `c₀`. -/
theorem expected_count_linear (c₀ : ℝ) {k : ℕ} (E : Fin k → Finset Ω) :
    expectedCost c₀ E = c₀ * ∑ i, prob (E i) := by
  have hcount : ∀ i, (∑ ω, if ω ∈ E i then (1 : ℝ) else 0) = (E i).card := by
    intro i; rw [Finset.sum_boole]; simp
  unfold expectedCost prob
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun i _ => hcount i), Finset.mul_sum, Finset.mul_sum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Removal subtracts.** If a regulating pillar suppresses the transitions `A` out of the
baseline transitions `B`, the realized count drops by exactly the probability of `A`. -/
theorem removal_subtracts (A B : Finset Ω) (h : A ⊆ B) :
    prob (B \ A) = prob B - prob A := by
  unfold prob
  rw [Finset.card_sdiff_of_subset h, Nat.cast_sub (Finset.card_le_card h), sub_div]

/-- **Survival factorizes** over pillars, so the cost inside the exponential is the plain sum. -/
theorem survival_factorizes (β : ℝ) {k : ℕ} (Z : Fin k → ℝ) :
    Real.exp (-β * ∑ i, Z i) = ∏ i, Real.exp (-β * Z i) := by
  rw [Finset.mul_sum, ← Real.exp_sum]

end PMArch.NetCost
