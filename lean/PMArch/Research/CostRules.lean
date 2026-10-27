import PMArch.DerivedParameters
import PMArch.ProtocolToll
import PMArch.PhysicalBridge

/-!
# The six terms as outputs of explicit pillar rules

Each term of the index is the value of a stated construction on the forced parameters.
What is proved here is that the constructions produce exactly the six terms; which
construction each pillar must use is the content of the corresponding rule.

| Pillar | Rule | Derived ingredient |
|---|---|---|
| Capacity | perimeter of a round envelope saturating the causal bound `2r ≤ Δ` | — |
| Map | one unit per unit Euler characteristic of the boundary | `χ = 2` (Postulate H) |
| Protocol | credit `−1/Σ y` over the `R_M − σ` residual unit channels in parallel | — |
| Governor | per-slot share of a total credit `χ` spread over the clock cycle | uniformity (Homogeneity) |
| Toll | uniform mass of the transition event in the trial space | — |
| Margin | uniform mass of one configuration in `L × V × Δ × Δ` | `V = σ + 1` (tree) |
-/

noncomputable section
namespace PMArch.CostRules
open ImpedanceTerms

variable (p : Parameters)

/-- **Capacity.** A round envelope whose diameter saturates the causal bound has perimeter
`πΔ`. -/
theorem capacity_rule : 2 * Real.pi * ((p.period : ℝ) / 2) = capacityTerm p := by
  unfold capacityTerm; ring

/-- **Map.** Unit cost per unit Euler characteristic. -/
theorem map_rule : (1 : ℝ) * p.eulerCharacteristic = mapTerm p := by
  unfold mapTerm; ring

/-- **Protocol.** Residual channels as unit admittances in parallel. -/
theorem protocol_rule (h : p.embeddingDimension < p.resolution) :
    ProtocolToll.protocolCredit (fun _ : Fin (p.resolution - p.embeddingDimension) => (1 : ℝ)) =
      protocolTerm p :=
  ProtocolToll.protocol_from_unit_channels p h

/-- **Governor.** A credit totalling `χ`, distributed over the `Δ` clock slots with no
preferred slot, has per-slot value `χ/Δ`: the uniform distribution is forced. -/
theorem governor_rule [NeZero p.period] (f : ZMod p.period → ℝ) (hshift : ∀ i, f (i + 1) = f i)
    (htot : ∑ i, f i = p.eulerCharacteristic) : -f 0 = governorTerm p := by
  rw [governor_uniform f _ hshift htot 0]; rfl

/-- **Toll.** Uniform mass of the specified transition event. -/
theorem toll_rule (hp : p.Admissible) (hχ : p.eulerCharacteristic ≤ p.nodeCapacity) :
    ((ProtocolToll.event hp.2.1 hp.2.2.1 hχ (Nat.le_of_lt hp.2.2.2.1)).card : ℝ) /
      Fintype.card (ProtocolToll.Trial p.nodeCapacity p.embeddingDimension p.resolution) =
      tollTerm p :=
  ProtocolToll.toll_from_sampling p hp hχ

/-- **Margin.** The local interaction volume is the vertex set of a tree with `σ` edges, so it
has `σ + 1` elements, whatever tree it is; the term is the uniform mass of one configuration. -/
theorem margin_rule {V : ℕ} {G : SimpleGraph (Fin V)} [Fintype G.edgeSet] (hG : G.IsTree)
    (hσ : G.edgeFinset.card = p.embeddingDimension) :
    (1 : ℝ) / Fintype.card (Fin p.embeddingLoad × Fin V × Fin p.period × Fin p.period) =
      marginTerm p := by
  have hV : V = p.embeddingDimension + 1 := by simpa using tree_vertices hG _ hσ
  subst hV
  simp [marginTerm, Fintype.card_prod]
  ring

/-- **Assembled index.** The impedance is the sum of the six rule outputs. -/
theorem impedance_from_rules [NeZero p.period] (hp : p.Admissible)
    (hχ : p.eulerCharacteristic ≤ p.nodeCapacity)
    (f : ZMod p.period → ℝ) (hshift : ∀ i, f (i + 1) = f i)
    (htot : ∑ i, f i = p.eulerCharacteristic)
    {V : ℕ} {G : SimpleGraph (Fin V)} [Fintype G.edgeSet] (hG : G.IsTree)
    (hσ : G.edgeFinset.card = p.embeddingDimension) :
    impedance p =
      2 * Real.pi * ((p.period : ℝ) / 2) + 1 * p.eulerCharacteristic +
      ProtocolToll.protocolCredit (fun _ : Fin (p.resolution - p.embeddingDimension) => (1 : ℝ)) +
      -f 0 +
      ((ProtocolToll.event hp.2.1 hp.2.2.1 hχ (Nat.le_of_lt hp.2.2.2.1)).card : ℝ) /
        Fintype.card (ProtocolToll.Trial p.nodeCapacity p.embeddingDimension p.resolution) +
      (1 : ℝ) / Fintype.card (Fin p.embeddingLoad × Fin V × Fin p.period × Fin p.period) := by
  rw [capacity_rule, map_rule, protocol_rule p hp.2.2.2.1, governor_rule p f hshift htot,
    toll_rule p hp hχ, margin_rule p hG hσ]
  rfl

end PMArch.CostRules
