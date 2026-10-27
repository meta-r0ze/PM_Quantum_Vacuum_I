import PMArch.MainResult
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Logic.Function.Iterate

/-! Conditional physical bridges. Dynamics, observations, statistical weights,
and electromagnetic matching are separate inputs; none is inferred from the
word "persistence". These theorems do not construct a quantum field theory. -/
noncomputable section
open scoped BigOperators
namespace PMArch

/-- An autonomous reversible evolution preserves distinguishability at every
specified time. The specified time is essential: periodic states do not encode
how many cycles have elapsed. -/
theorem reversible_history {S : Type*} (U : Equiv.Perm S) (t : ℕ)
    {x y : S} (h : (U^[t]) x = (U^[t]) y) : x = y :=
  U.injective.iterate t h

/-- Observation of the full state is an additional requirement. -/
theorem observed_history {S O : Type*} (U : Equiv.Perm S) (observe : S → O)
    (hobs : Function.Injective observe) (t : ℕ) {x y : S}
    (h : observe ((U^[t]) x) = observe ((U^[t]) y)) : x = y :=
  reversible_history U t (hobs h)

/-- If every candidate has identical observed data, unique reconstruction is
exactly the assertion that at most one candidate exists. -/
theorem constant_observation_iff {S O : Type*} (o : O) :
    Function.Injective (fun _ : S => o) ↔ Subsingleton S := by
  constructor
  · intro h
    exact ⟨fun x y => h rfl⟩
  · intro h x y _
    exact h.elim x y

/-- Reversibility alone does not make a coarse observation informative. -/
theorem reversible_but_unobservable :
    Function.Bijective (Equiv.refl Bool) ∧
    ¬ Function.Injective (fun _ : Bool => ()) := by
  constructor
  · exact (Equiv.refl Bool).bijective
  · intro h
    have hf : (false : Bool) = true := h rfl
    cases hf

/-- Conditional rank selection: rank minimization supplies the upper bound. The
divisibility hypothesis is discharged for even unimodular lattices by
`PMArch.RankEight.minimal_rank_eight_of_lattice`. -/
theorem minimal_rank_eight {n : ℕ} (hn : 0 < n) (hdiv : 8 ∣ n)
    (hminimal : n ≤ 8) : n = 8 := by
  obtain ⟨k, hk⟩ := hdiv
  omega

/-- Nonnegative quadratic cost plus separation of its zero set implies strict
positivity. This lemma does not identify cost with a spacetime metric. -/
theorem positive_cost {S : Type*} [Zero S] (Q : S → ℝ)
    (hnonneg : ∀ x, 0 ≤ Q x) (hzero : ∀ x, Q x = 0 → x = 0)
    {x : S} (hx : x ≠ 0) : 0 < Q x := by
  have hne : Q x ≠ 0 := fun h => hx (hzero x h)
  exact lt_of_le_of_ne (hnonneg x) (Ne.symm hne)

/-- For the supplied orientable-surface Euler formula, maximal Euler
characteristic selects genus zero. Surface classification is not formalized. -/
theorem maximal_euler_iff (g : ℕ) : (2 - 2 * (g : ℤ) = 2) ↔ g = 0 := by
  omega

/-- A speed bound alone gives an upper bound on circumference, not equality. -/
theorem causal_perimeter_bound {r T : ℝ} (h : 2 * r ≤ T) :
    2 * Real.pi * r ≤ Real.pi * T := by
  nlinarith [Real.pi_pos]

/-- Saturation is the extra assumption needed for the capacity term. -/
theorem saturated_perimeter {r T : ℝ} (h : 2 * r = T) :
    2 * Real.pi * r = Real.pi * T := by
  rw [← h]
  ring

/-- Positive factorized weights give additive negative log weight. This is a
conditional identity, not a derivation of statistical independence. -/
theorem factorized_action {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) :
    -Real.log (∏ i, w i) = ∑ i, -Real.log (w i) := by
  rw [Real.log_prod (fun i _ => ne_of_gt (hw i))]
  simp only [Finset.sum_neg_distrib]

/-- The full six-term model can be realized by positive relative weights.
Weights exceeding one are allowed: these are not individual probabilities. -/
def pillarTerms (p : Parameters) : Fin 6 → ℝ :=
  ![capacityTerm p, mapTerm p, protocolTerm p, governorTerm p, tollTerm p, marginTerm p]

theorem pillar_sum (p : Parameters) : (∑ i, pillarTerms p i) = impedance p := by
  simp [pillarTerms, Fin.sum_univ_succ, impedance]
  ring

theorem exponential_weight_action (p : Parameters) :
    -Real.log (∏ i : Fin 6, Real.exp (-pillarTerms p i)) = impedance p := by
  rw [factorized_action _ (fun i => Real.exp_pos _)]
  simp only [Real.log_exp, neg_neg]
  exact pillar_sum p

/-- Counts for an explicit uniform three-leg trial sample space. Selecting
this sample space and event is a modeling choice, not a consequence of triality. -/
abbrev TollSpace := Fin 32 × Fin 32 × Fin 32 × Fin 5 × Fin 172
abbrev ValidToll := Fin 2 × Fin 167

def validPlacement (v : ValidToll) : TollSpace :=
  (0, 0, ⟨v.1.val, by omega⟩, 0, ⟨v.2.val + 5, by omega⟩)

theorem validPlacement_injective : Function.Injective validPlacement := by
  intro a b h
  have h1 := congrArg (fun x : TollSpace => x.2.2.1.val) h
  have h2 := congrArg (fun x : TollSpace => x.2.2.2.2.val) h
  apply Prod.ext
  · apply Fin.ext
    exact h1
  · apply Fin.ext
    dsimp [validPlacement] at h2
    omega

def tollEvent : Finset TollSpace := Finset.univ.image validPlacement

theorem toll_event_card : tollEvent.card = 334 := by
  rw [tollEvent, Finset.card_image_of_injective _ validPlacement_injective]
  simp

/-- Uniform mass of the specified event equals the baseline Toll term. -/
theorem uniform_toll :
    (tollEvent.card : ℝ) / Fintype.card TollSpace = tollTerm baseline := by
  rw [toll_event_card]
  norm_num [TollSpace, tollTerm, baseline, Parameters.nodeCapacity, Parameters.resolution]

abbrev MarginSpace := Fin 31 × Fin 6 × Fin 43 × Fin 43

/-- Uniform mass of a specified single configuration equals the Margin term. -/
theorem uniform_margin :
    (1 : ℝ) / Fintype.card MarginSpace = marginTerm baseline := by
  norm_num [MarginSpace, marginTerm, baseline, Parameters.embeddingLoad,
    Parameters.intrinsicLoad]

/-- In rationalized natural units, the Maxwell coefficient is g⁻².
Matching Zgeo = 4π/g² implies α⁻¹ = Zgeo when α = g²/(4π).
Both the Maxwell normalization and the matching equation are hypotheses. -/
theorem electromagnetic_matching (gSquared Z : ℝ) (_hg : 0 < gSquared)
    (hmatch : 4 * Real.pi / gSquared = Z) :
    (gSquared / (4 * Real.pi))⁻¹ = Z := by
  rw [inv_div]
  exact hmatch

/-- A general matching coefficient is not fixed by positivity. -/
theorem matching_coefficient (gSquared Z C : ℝ) (hg : 0 < gSquared)
    (hZ : 0 < Z) (hmatch : Z = C / gSquared) :
    (gSquared / (4 * Real.pi))⁻¹ = (4 * Real.pi / C) * Z := by
  have hC : C ≠ 0 := by
    intro hc
    rw [hc, zero_div] at hmatch
    linarith
  rw [hmatch, inv_div]
  field_simp

/-- Given the electromagnetic matching postulate, the physical inverse
coupling inherits the already verified numerical enclosure. -/
theorem physical_inverse_coupling_bounds (gSquared : ℝ) (hg : 0 < gSquared)
    (hmatch : 4 * Real.pi / gSquared = geometricIndex) :
    (137.035999212381397211 : ℝ) < (gSquared / (4 * Real.pi))⁻¹ ∧
    (gSquared / (4 * Real.pi))⁻¹ < (137.035999212381397213 : ℝ) := by
  rw [electromagnetic_matching gSquared geometricIndex hg hmatch]
  exact geometricIndex_bounds

/-- The admittance gives a normalized binary distribution, without selecting
which physical event this probability describes. -/
theorem binary_coupling_distribution :
    0 ≤ causalCoupling ∧ 0 ≤ 1 - causalCoupling ∧
    causalCoupling + (1 - causalCoupling) = 1 := by
  obtain ⟨hlo, hhi⟩ := causalCoupling_bounds
  constructor
  · linarith
  constructor <;> linarith

/-- SI resistance identity from the conventional definitions of α, Z₀ and h.
It is not an independent prediction of Hall transport. -/
theorem resistance_identity (e ε hbar c : ℝ)
    (he : e ≠ 0) (hε : ε ≠ 0) (hh : hbar ≠ 0) (hc : c ≠ 0) :
    (2 * Real.pi * hbar) / e^2 =
      (1 / (ε * c)) / 2 * (e^2 / (4 * Real.pi * ε * hbar * c))⁻¹ := by
  field_simp
  ring

/-- Coulomb field at the reduced Compton wavelength equals α times the
conventional Schwinger field scale. This is algebra, not pair-production dynamics. -/
theorem schwinger_scale_identity (e ε hbar c m : ℝ)
    (he : e ≠ 0) (hε : ε ≠ 0) (hh : hbar ≠ 0) (hc : c ≠ 0) (hm : m ≠ 0) :
    e / (4 * Real.pi * ε * (hbar / (m * c))^2) =
      (e^2 / (4 * Real.pi * ε * hbar * c)) * (m^2 * c^3 / (e * hbar)) := by
  field_simp

end PMArch
