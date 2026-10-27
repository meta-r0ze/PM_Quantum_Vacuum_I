# What the forced substrate provides, compared with the paper's integers

Goal: list what the forced structures (E8, its two D4 sectors, the 43-state clock plane) provide
on their own, then compare with the integers the six-term index uses. Lean: `E8Invariants.lean`,
`Channels.lean`, `DerivedParameters.lean`.

## Intrinsic invariants (computed)

| Structure | Invariant | Value | Lean |
|---|---|---|---|
| E8 | rank | 8 | forced (`Vacuum`) |
| E8 | roots | 240 | `ThetaE8.e8_card_roots` |
| E8 | Coxeter number h = roots/rank | 30 | `E8Invariants.coxeter_numbers` |
| E8 | dim 𝔢8 / rank = h + 1 | 31 | `E8Invariants.margin_reading` |
| E8 | vectors of norm 4 / 6 | 2160 / 6720 | `E8Unique.card_norm_four` (4); numerical (6) |
| E8 | roots at inner product 0 / ±1 / ±2 with a fixed root | 126 / 56+56 / 1+1 | numerical |
| D4 sector | rank | 4 | `Channels.e8_two_d4_sectors` |
| D4 sector | roots, Coxeter number | 24, 6 | `E8Invariants.d4_card_roots` |
| D4 sector | glue classes × minimal vectors | 3 × 8 | `Channels.minimal_class_card` |
| D4 ⊕ D4 in E8 | index | 4 | det = 16 vs 1 |
| Clock plane | discriminant group | ℤ/43 | `ClockPlane.clock_glue`, `DiscriminantGroup` |
| Clock plane | roots of E8 orthogonal to it | 20 (an A4) | numerical; depends on the chosen embedding |

## Comparison with the index's integers

| Paper quantity | Paper's justification | Substrate value | Status |
|---|---|---|---|
| D = 4 | coordinate sector | rank of a D4 sector | forced (`parameters_forced`) |
| Δ = 43 | clock | order of the clock plane's discriminant group | forced |
| ν = 16, N = 32 | two channels per sector | two D4 glue classes × 8 minimal vectors, two sectors | forced |
| χ = 2 | sphere boundary | not a lattice invariant; Postulate H | forced given H |
| σ = 5 | 3 space + 2 boundary dims | not a lattice invariant; Postulates G, H | forced given G, H |
| R_M = 172 | D·Δ | rank(D4) × clock states | bookkeeping product |
| σ + 1 = 6 | star tree with σ edges | also h(D4) = 24/4 | two readings agree |
| L_embed = 31 | ν + σ + χ + 2D (sum of unlike counts) | also h(E8) + 1 = dim 𝔢8 / rank | two readings agree |
| R_M − σ = 167 | residual addresses | no lattice counterpart found | bookkeeping |

## Margin

**L_embed = 31 = dim 𝔢8 / rank.** The substrate's symmetry generators are its 240 root moves plus
8 Cartan directions (the zero weight of the adjoint, one per coordinate). Counting all generators
per coordinate gives 248/8 = 31. The "+1" is not an add-on: it is the coordinate direction itself,
which is part of the geometry. This one rule replaces the paper's sum of unlike counts
(ν + σ + χ + 2D).

**V_local = 6 = σ + 1** stays the local interaction tree (σ edges plus the center;
`ImpedanceTerms.tree_vertices`). It is not a D4 quantity: σ = 5 comes from Postulates G and H.
The coincidence 6 = h(D4) is not used.

A single "Lie rule" for both factors does not reproduce the index, which is why the two factors
keep separate justifications:

| Rule | L | V | Z | vs CODATA 2022 | vs Morel 2020 |
|---|---|---|---|---|---|
| L = dim 𝔢8 / rank, V = σ + 1 (adopted) | 31 | 6 | 137.035999212381 | +1.7σ | +0.6σ |
| Coxeter number for both | 30 | 6 | 137.035999309305 | +6.3σ | +9.4σ |
| dim/rank for both | 31 | 7 | 137.035998796995 | −18.1σ | −37.2σ |

## Toll

Toll = χ(R_M − σ) / (N³ σ R_M) = 334 / (32³ · 5 · 172).

* **Three legs: substrate-derived.** A D4 sector's glue group is (ℤ/2)². A set of distinct nonzero
  glue classes with zero total has exactly three elements (`E8Invariants.neutral_distinct_classes`),
  and a neutral pair is a repeated class, i.e. propagation (`neutral_pair`). This is the
  triality vertex 8_v ⊗ 8_s ⊗ 8_c → 1, obtained from glue arithmetic rather than representation
  theory. In E8 the 240 roots split as 48 sector roots plus three glue cosets of 64 = 8 × 8 roots
  each (numerical): each coset pairs one 8-vector class of sector A with one of sector B.
* **N = 32 per leg: in tension with the triality reading.** If legs are the three distinct classes,
  each leg's natural sample space is that class's minimal vectors in both sectors (16), or all
  minimal glue vectors if the type is unassigned (48). The paper's 32 counts the two
  input/output classes per sector. None of the substrate-native alternatives come close:

| Per-leg sample | Z − CODATA |
|---|---|
| 32 (paper) | +1.7σ |
| 16 (one class, both sectors) | +3952σ |
| 24 (all classes, one sector) | +775σ |
| 48 (all classes, both sectors) | −396σ |

* **σ, R_M, χ(R_M − σ):** bookkeeping on derived integers. No lattice counterpart for the event
  size 334 = 2 · 167 or for σ R_M as a sample-space factor. Two legs: +17498σ; four legs: −545σ.

## Protocol

Protocol = −1/(R_M − σ) = −1/167. R_M = rank(D4) × clock states is substrate-derived; subtracting
σ is not a lattice operation. No E8, D4 or clock invariant equals 167. Neighbouring values move Z by
thousands of σ (1/166: −1716σ; 1/168: +1699σ; 1/172: +8291σ).

## Capacity (`CapacityBarbier.lean`)

The boundary of a convex envelope with support function h has width h(θ) + h(θ + π) and
perimeter ∫₀^{2π} h (Cauchy). Proved:

* `barbier`: every envelope of constant width w has perimeter πw, whatever its shape.
* `perimeter_le`: widths ≤ w give perimeter ≤ πw.
* `capacity_is_max`: under the causal bound (width ≤ Δ: cross and return within one cycle), the
  largest admissible boundary is exactly πΔ, attained by any constant-width envelope.

Roundness and saturation are no longer choices: Capacity is the maximal causally admissible
boundary. Remaining premise: the cost is the boundary measure (interior indistinguishable from
the vacuum), with unit density.

## Shared residual addresses (`TollFilters.lean`)

The embedding occupies σ of the R_M addresses; any injective placement leaves R_M − σ = 167
(`residual_card`). Protocol's channels and Toll's non-aliasing factor are this one set
(`protocol_residual`, `nonaliasing_prob`), so 167 is one quantity used twice, not two choices.
Toll factorizes into independent filters (`toll_as_filters`):
(1/N)·(1/N)·(χ/N)·(1/σ)·((R_M − σ)/R_M).

The third-leg factor 2 is more naturally the number of orientations of a connected orientable
boundary (always 2) than its Euler characteristic; for the sphere the two coincide, so the value
is unchanged. Not formalized (needs manifold orientations).

## Map, Governor

Map = χ with unit weight. Governor = −χ/Δ; uniformity over the cycle is proved
(`ImpedanceTerms.governor_uniform`). The total credit χ is the Gauss–Bonnet total curvature of the
boundary divided by 2π, a classical theorem not formalized here.

## Summary after this pass

| Term | Proved | Still a choice |
|---|---|---|
| Capacity | πΔ is the maximum allowed by causality, for any shape | cost = boundary measure, unit density, maximal allocation |
| Map | χ = 2 (H) | unit weight |
| Protocol | 167 = residual addresses after an injective embedding | embedding occupies σ addresses; credit = −1/(total admittance) |
| Governor | uniform χ/Δ | total credit = χ (Gauss–Bonnet reading), sign |
| Toll | three legs (glue arithmetic); non-aliasing (R_M−σ)/R_M; filter factorization | per-leg sample N = 32 vs triality reading; two legs fixed; 1/σ |
| Margin | 31 = dim 𝔢8/rank; 6 = tree on σ; Δ² as two clock labels | product space, one-quantum singleton |
| All | additivity from factorized weights | ± signs (cost vs controller), unit coefficients |

## Persistence lens on the remaining choices

Only Finiteness, Conservation, Causality, Closure and Economy are used as reasons; no physics.

| Choice | Persistence reason | Status |
|---|---|---|
| Two channel classes per sector (ν = 16) | Causality: a direction needs a source and a sink (≥ 2); Economy: no more than needed (≤ 2). The third glue class carries no flow. | stated; load-bearing (see below) |
| Each Toll leg samples all N = 32 channels | Closure: no external tag can restrict a leg to part of the channel set; the symmetries that preserve the channel structure act transitively on the 32 (expected from W(D4)×W(D4), the class swap and the sector swap; not checked in Lean). `ClosureSymmetry.invariant_set`: an internally defined admissible set is empty or everything. | proved given the symmetry premise |
| Uniform prior (Toll, Margin) | Closure: no internally preferred label. `ClosureSymmetry.invariant_measure_uniform`. | proved given the symmetry premise |
| Three legs | Economy: the least arity that is more than a source→sink transfer (two legs = propagation). | stated, not a theorem |
| Target avoids own embedding | Causality: no self-aliasing. `TollFilters.nonaliasing_prob`. | proved given σ occupied addresses |
| Two legs return to reference, third in 2 orientations | Conservation: identity preserved; the boundary has two orientations. | stated |
| Interaction label 1/σ | — | open |
| Protocol −1/(total admittance) | — | open |
| Signs, unit weights | PM classification: costs vs controllers; Closure: one currency | stated |

Alternatives to N = 32, read through persistence:

* 16 (one sector): needs an external tag saying which sector a leg is in; violates Closure.
* 48 (all three glue classes, both sectors): includes a class that carries no flow; violates
  Economy. It is what pure lattice symmetry gives (triality makes the three classes equivalent),
  so the two-channel choice is exactly where Causality breaks triality.
* The choice is load-bearing beyond Toll: with N = 48 the schedule window is 48 ≤ Δ ≤ 96, whose
  only class-number-one period is 67, not 43.

## Second pass: "what persists?" (`PersistenceEvents.lean`)

| Choice | What persists | Lean |
|---|---|---|
| Three legs | Unlabeled legs (Closure) and reversibility (Conservation): with one-bit legs, every two-leg update is a common relabeling (± exchange) — nothing is coordinated; a symmetric reversible three-leg update exists that is not. Economy: three. | `Arity.two_legs_separable`, `Arity.three_legs_interact` |
| Third leg factor 2 | A connected orientable boundary has exactly two orientations, whatever its genus. | `Orientation.two_orientations` |
| Uniform measure | No internally preferred label (Closure). | `ClosureSymmetry.invariant_measure_uniform` |
| Correction terms | Each is the probability of a persistence event under that measure: Protocol 1/167, Governor 2/43, Toll, Margin. | `PersistenceEvents.corrections_as_probabilities` |

Premises still stated rather than proved: legs carry one bit (channel occupancy); a valid
transition needs one specific interaction direction (1/σ) and returns two legs to their reference
state; Protocol's event is one residual address; the ± signs (costs vs controllers); unit
weights; L_embed read as generators per coordinate.

## Third pass

* **31 is geometry.** 31 = (240 + 8)/8: the 240 nearest-neighbour moves of a site (kissing
  number = roots) plus its 8 coordinate directions, per coordinate (`E8Invariants.margin_reading`).
* **Protocol is information theory.** The update is a function (Postulate R), so a state has one
  successor; coordinating it among the 167 residual addresses without an external pointer
  succeeds with probability 1/167 = 2^(−log₂ 167) (`PersistenceEvents.protocol_persistence`).
* **Toll is the original three filters.** State identity (two legs and the direction return to
  reference), flux orientation (the third leg in either of the two orientations), non-aliasing
  (target off the embedding): Toll = [2/(32³·5)] · (167/172) (`PersistenceEvents.toll_persistence`).
  The 1/σ is part of state identity, not a separate choice.
* **One bit per leg.** A leg's state is occupancy (active or idle slot), the binary already used by
  the schedule; a one-bit distinction is the minimal one. The premise is load-bearing:
  `Arity.three_valued_two_legs_interact` shows three-valued legs would already interact at arity 2.

## Signs, unit weights and Capacity density (`NetCost.lean`, `NetIndex.lean`)

PM prices a pillar as toll × frequency (`Z ≈ c₀ f`), sums the pillars, and only then exponentiates
for survival. Each term of the index is therefore an expected number of transitions per cycle.

* **Unit weights and linear addition.** Expected counts of indicator events add, each with the
  single toll c₀ (`NetCost.expected_count_linear`); Closure sets c₀ = 1. A probability enters as
  an expected count, not as −log p. The exponential sits outside the sum
  (`NetCost.survival_factorizes`).
* **Signs.** Protocol ("coordinates state transitions") and Governor ("restricts which
  transitions the system can undergo") are defined by their action on other transitions; a removed
  transition lowers the count by its probability (`NetCost.removal_subtracts`). The other four
  provision or spend: `NetIndex.signs`. Each of Conservation and Causality has one regulator;
  Finiteness has none. `NetIndex.index_as_net_transitions`: index = provisioned − removed.
* **Capacity density.** The defect's identity is its distinctions from the vacuum; interior and
  vacuum sites carry none (`NetIndex.interior_carries_no_distinction`,
  `vacuum_carries_no_distinction`), so only the boundary costs. At speed one, one unit of boundary
  is one tick, one transition.

## Map and Governor's χ (`Descartes.lean`)

`Descartes.descartes`: for a closed triangulated boundary (triangle angles summing to π, each edge
in two triangles, 3F = 2E), the total angle defect is 2π(V − E + F) = 2πχ, for any triangulation,
shape or size. χ is the number of full 2π turns the boundary makes to close. For the sphere it is
two (`sphere_two_turns`; witness `tetrahedron_turns`). Map's term counts these closures with unit
weight (one transition each); Governor spreads the same total over the cycle. The incidence data is
assumed consistent with a surface; only the counting identity is formalized.

## Only distinctions cost (`Distinctions.lean`)

`Distinctions.only_distinctions_cost`: a maintenance cost that is local (site terms plus
neighbour terms), measured from the vacuum (the vacuum's local terms vanish) and symmetric under
exchanging the two state names (Closure: "vacuum" is not an intrinsic label) equals a single
density times the number of adjacent pairs in different states. Uniform regions, the defect's
interior and the vacuum, cost nothing; the cost is the boundary measure. `area_breaks_relabeling`:
an area cost is local and vacuum-zero but fails the relabeling symmetry, so that symmetry is what
excludes it. The density is the toll: one transition.

## Further premises as theorems (`PersistencePremises.lean`)

* **State identity.** A transition preserves the defect when its internal configuration returns to
  the reference up to the defect's one invisible symmetry, reversal of boundary orientation. The
  valid configurations are the orbit of the reference: exactly two (`state_identity_card`,
  `toll_identity`). This is Toll's 2/(32³·5).
* **Margin's Δ².** At speed one in one spatial direction, the events reachable within one cycle,
  {(t, x) : t < Δ, |x| ≤ t}, number Σ(2t + 1) = Δ² (`causal_cone_card`). Δ² is the causal cone of
  one cycle, not two independent labels.
* **Regulator signs.** Governor restricts (a subset of transitions) and Protocol coordinates (merging
  equivalent attempts); neither can increase the transition count (`restriction_lowers`,
  `merging_lowers`). The minus sign follows from what the definitions do.
* **One bit per leg.** The substrate's local observation of a channel is gap-only, hence binary, and
  both values occur in the forced 43-slot schedule (`leg_state_binary`).

Still premises: identity is configuration up to orientation reversal (the only invisible symmetry);
Governor and Protocol act by restriction and merging (their PM definitions); a leg carries exactly
its local observation; 31 counts each coordinate's "stay" once alongside the 240 moves.

## Final state (`FinalPremises.lean`, `MainTheorem.lean`)

* `Main.persistence_selects`: from the postulates (Geometric, Economical, Sector, Clock, G, H), the
  substrate is E8 with two D4 sectors, Δ = 43, the parameter record is forced, and the index is
  43π + 2 + 334/(32³·5·172) + 1/(31·6·43²) − 1/167 − 2/43 ∈ (137.035999212381397211, …213).
* `Main.postulates_satisfiable`: E8 with the 43-cycle, one time direction and the sphere satisfies
  every postulate.
* `FinalPremises.description_length`: the defect's description (channel content, configuration,
  boundary closures, current and next coordinate) has ν + σ + χ + 2D = 31 labels on the forced
  parameters, equal to the substrate's (240 + 8)/8.
* `FinalPremises.orientation_relabelings`: the only relabelings of the orientation data are the
  identity and the flip.
* `FinalPremises.leg_factorization`: an update insensitive to what the local observation cannot see
  factors through it; with a binary observation, a leg carries one bit.

Remaining readings of PM (stated, not derivable inside Lean): the fields of a defect's description;
orientation as the only discrete boundary data beyond distinctions; Governor and Protocol act by
restriction and merging; under Closure a vertex sees only local observations.

## Status of the last four readings

| Reading | Status |
|---|---|
| Fields of a defect's description | Theorem: `FinalPremises.description_minimal` — a description keeping a subset of independent nontrivial coordinates is injective (Conservation) exactly when it keeps all of them; Economy forbids extras. `defect_description_minimal` applies it to the 31 coordinates, each of which is a forced parameter's coordinate. |
| Orientation as the only boundary data beyond distinctions | Theorem: the distinctions fix the boundary's adjacency; the consistent orientation data on a connected boundary is exactly {s, −s} (`Orientation.two_orientations`), relabeled only by the flip (`orientation_relabelings`). |
| A vertex sees only its local observation | Postulate I itself (gap-only local observations, `ClockPostulates.schedule`); `leg_factorization` gives one bit. |
| Governor restricts, Protocol merges | The PM definitions of the two pillars ("restrict which transitions", "coordinate transitions"): regulators act on existing transitions and create none. Given that, `restriction_lowers` / `merging_lowers` fix the sign. Definitions, not theorems. |
