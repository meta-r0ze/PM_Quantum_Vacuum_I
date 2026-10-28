# PM-1-Arch: Lean formalization

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum I: The E8 Substrate and the
Fine-Structure Constant*.

## Main result

`PMArch.Main.persistence_selects` (`PMArch/MainTheorem.lean`): from the postulates below,

* the substrate lattice is **E8**, containing two orthogonal **D4** sectors;
* the clock period is **Δ = 43**;
* every integer input of the index is forced: D = 4, ν = 16, N = 32, σ = 5, χ = 2;
* the index, read as net transitions per cycle, is

  Z = 43π + 2 + 334/(32³·5·172) + 1/(31·6·43²) − 1/167 − 2/43,
  with 137.035999212381397211 < Z < 137.035999212381397213.

`PMArch.Main.postulates_satisfiable`: E8 with the 43-cycle, one time direction and the sphere
satisfies every postulate, so the set is consistent. Comparison with measured α is separate
(`PMArch.alpha_deviations`) and is not part of the theorem.

## Postulates

| Postulate | PM requirement | Lean | Consequence |
|---|---|---|---|
| Bounded-cost sets are finite | Finiteness | `Vacuum.Geometric.finite` | positive definite (`Translation.posDef_iff_finite_levels`) |
| Every one-bit distinction is readable by the substrate itself | Conservation, Closure | `Vacuum.Geometric.readable` | odd determinant (`SelfReadable.bitReadable_iff_odd`) |
| Glue elements are bits, 2Λ* ⊆ Λ | Map | `Vacuum.Geometric.bitAddressed` | with the above, unimodular |
| A nontrivial exchange law in which zero-pairing operations commute | Protocol, Causality | `Vacuum.Geometric.exchange` | even (`OrthogonalExchange.orthogonal_nontrivial_exchange_forces_even`) |
| Least rank among substrates meeting the above | Economy (PM selection) | `Vacuum.Economical` | rank 8, then E8 (`RankEight.rank_dvd_eight`, `E8Unique.e8_unique`) |
| Two orthogonal irreducible bit-addressed rank-4 root sectors | Postulate B | `Vacuum.SectorPostulates` | D4 (`Sectors.sector_selection`) |
| Clock = a substrate plane; states = its discriminant group; unique geometry; gap-only observations | Closure, Map, Causality | `Vacuum.ClockPostulates` | Δ = 43 (`Vacuum.vacuum_selects`) |
| Volume element squares to −1 | Postulate G | `Derived.SignaturePostulate` | one time direction |
| Boundary of least topological complexity | Economy (Postulate H) | `Derived.BoundaryPostulate` | sphere, χ = 2 |

`Vacuum.geometric_iff`: the first four postulates hold exactly for positive-definite, even,
unimodular, nonzero lattices. `VacuumIndependence` gives, for each postulate, a lattice meeting
every other one but not that one (hyperbolic plane, D4, A2, ℤ, E8 ⊕ E8).

## The six terms

Each term is an expected number of transitions per cycle (`NetCost.expected_count_linear`,
unit toll by Closure). Provisioning pillars add; Protocol and Governor, defined by restricting and
coordinating other transitions, subtract (`NetCost.removal_subtracts`, `NetIndex.signs`).

| Term | Value | Meaning | Main theorems |
|---|---|---|---|
| Capacity | 43π | largest boundary a causal cycle allows, any shape; only distinctions cost | `Capacity.capacity_is_max`, `Capacity.barbier`, `Distinctions.only_distinctions_cost` |
| Map | 2 | full 2π turns of the boundary to close (Gauss–Bonnet) | `Descartes.descartes`, `Derived.boundary_sphere` |
| Protocol | −1/167 | the one successor among the residual addresses | `PersistenceEvents.protocol_persistence`, `TollFilters.residual_card` |
| Governor | −2/43 | the boundary's turns spread uniformly over the cycle | `ImpedanceTerms.governor_uniform` |
| Toll | 334/(32³·5·172) | a transition that preserves identity, orientation and non-aliasing | `PersistenceEvents.toll_persistence`, `PersistencePremises.toll_identity`, `Arity.three_legs_interact`, `Orientation.two_orientations` |
| Margin | 1/(31·6·43²) | one configuration among description × local tree × causal cone | `FinalPremises.description_minimal`, `ImpedanceTerms.tree_vertices`, `PersistencePremises.causal_cone_card` |

Uniform measures come from Closure (`ClosureSymmetry.invariant_measure_uniform`).
`docs/derivation-log.md` records how each choice was replaced by a theorem.

**Not derived inside Lean:** the postulates above, and PM's definitions of the pillars (Governor
restricts transitions, Protocol coordinates them; a vertex sees only local observations, which is
Postulate I).

## Layout

| Path | Contents |
|---|---|
| `PMArch/MainTheorem.lean` | main theorem and satisfiability |
| `PMArch/Vacuum.lean`, `VacuumIndependence.lean` | postulates, E8 and clock selection, independence |
| `PMArch/Lattices`, `RankEight`, `ThetaE8`, `E8Unique`, `Translation*`, `Postulates`, `ClaimBoundary` | lattice classification: theta series, rank divisible by 8, uniqueness of E8 |
| `PMArch/Clock`, `ClockPlane`, `DiscriminantGroup`, `Scheduling`, `Selection`, `ClassNumber`, `ScheduleReconstruction`, `ScheduleReconstructionField` | clock, schedule window (the no-adjacent-idle hypothesis of the older route is discharged from gap-only reconstruction in `ScheduleReconstruction`), class number one |
| `PMArch/SelfReadable`, `Parity`, `OrthogonalExchange`, `Sectors`, `Channels`, `ChannelSymmetry` | unimodularity, evenness, sectors, channels; the uniform channel measure from E8 symmetry |
| `PMArch/DerivedParameters`, `E8Invariants`, `CapacityBarbier`, `CapacityEnvelope`, `CauchyPolygon`, `CircleLength`, `Distinctions`, `Descartes`, `TollFilters`, `ClosureSymmetry`, `PersistenceEvents`, `PersistencePremises`, `FinalPremises`, `NetCost`, `NetIndex`, `Impedance*`, `ProtocolToll` | parameters and the six terms |
| `PMArch/Pillars`, `Comparison`, `PhysicalBridge` | PM failure modes, comparison with measurement, earlier bridge lemmas |
| `PMArch/Research/` | alternative routes, counterexamples and necessity tests (not on the main path) |
| `classification/` | vendored class-number-one proof (Peter W. Murphy, Apache-2.0) |
| `audits/` | scoped axiom audits for the research modules |
| `docs/` | derivation log; `docs/research/` holds earlier investigation notes |

## Build and audit

Lean 4.34.1, mathlib `d13f23b` (pinned in `lake-manifest.json`). With
[elan](https://github.com/leanprover/elan):

```sh
lake exe cache get
./check.sh
```

`check.sh` runs `lake build`, the strict audit (`AuditStrict.lean`: every PMArch declaration may
depend only on `propext`, `Classical.choice`, `Quot.sound`), the readable `Audit.lean`, and the
class-number audit. `audit-negative-tests.sh` checks that the strict audit rejects `sorry` and new
axioms. Last full run (2026-10-27): 1236 declarations passed.

## Credits

The class-number-one classification in `classification/` is Peter W. Murphy's formalization
(https://github.com/DrMurphyIsIn/tenth-discriminant), vendored unmodified; see its NOTICE and
PROVENANCE. Built on mathlib.
