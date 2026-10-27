# PM-1-Arch: conditional architecture and physical bridges

This project checks the finite scheduling argument, the conditional selection of
Δ = 43, the exact six-term geometric index, and conditional physical bridges in the paper. It is a formalization
of a **conditional mathematical core**, not a proof that persistence forces E8
or that the geometric index equals the measured inverse fine-structure constant.

## Build and audit

Lean is pinned to v4.34.1. The vendored class-number proof in `classification/` is a
local Lake package (`ELEM`), built unmodified; mathlib is pinned through its manifest
(commit `d13f23b`), and `lake-manifest.json` pins all dependency commits. With [elan](https://github.com/leanprover/elan) installed:

```sh
cd /path/to/PM-1-Arch/lean
lake exe cache get
./check.sh
```

The first dependency setup requires network access. `check.sh` runs `lake build`
and the exhaustive `AuditStrict.lean`, followed by the human-readable `Audit.lean`.
It then runs the class-number proof's own audit (`classification/Audit.lean`). For a nonstandard installation, set
`PM_ARCH_LAKE_BIN` to the absolute path of `lake` and `ELAN_HOME` to that
installation's directory. `MATHLIB_CACHE_DIR` can relocate mathlib's download cache.
Build products and dependencies under `.lake/` are ignored by Git.

`AuditStrict.lean` checks every public and private PMArch declaration, including
transitive dependencies. It fails for any axiom other than `propext`,
`Classical.choice`, or `Quot.sound`. `audit-negative-tests.sh` verifies rejection
of both an admitted proof and a newly introduced axiom. Its deliberately invalid
test declarations are generated in a temporary directory and never imported by
the project.

The macOS installation uses elan in `~/.elan`; new login shells expose both
`lean` and `lake`. Existing terminals can run `source ~/.elan/env`.

## Verification on 2026-10-27

With Lean 4.34.1 and mathlib `d13f23b`, `lake build` completed (8992 jobs), including the
vendored class-number proof as a local package. The strict audit passed for all 305 PMArch
declarations, whose transitive dependencies now include the full class-number-one proof
through `PMArch/ClassNumber.lean`. The principal-theorem audit and the class-number audit
passed; both negative controls were rejected for the intended reason. All dependencies are
within the standard three-axiom allowlist. Rank divisibility by eight is proved
(`PMArch/RankEight.lean`), and E8 uniqueness is proved (`PMArch/E8Unique.lean`).

## Proven results

| File | Result |
| --- | --- |
| `PMArch/Scheduling.lean` | An injective map from N states into Δ slots implies N ≤ Δ. If every idle slot is followed by an active slot under a permutation, Δ ≤ 2N, where N counts active slots. |
| `PMArch/Selection.lean` | Filtering the explicit discriminant list by 32 ≤ Δ ≤ 64 gives exactly {43}. The schedule and injection hypotheses imply Δ = 43. A concrete single 43-slot cycle has 32 active slots and 11 isolated idle slots. |
| `PMArch/Impedance.lean` | The baseline loads are 32, 172, 23, 31, and 188; the baseline is admissible; the exact six-term expression has the certified interval below; its reciprocal lies strictly between zero and one. |
| `PMArch/PhysicalBridge.lean` | Reconstruction with informative observations; a reversible but unobservable counterexample; conditional rank and boundary selection; perimeter bounds and saturation; additive log weights; explicit Toll and Margin sample spaces; Maxwell matching and SI field/resistance identities. |
| `PMArch/SchedulingComplete.lean` | A single cyclic schedule with N active slots exists if and only if N ≤ Δ ≤ 2N, including the empty case. |
| `PMArch/CliffordSignature.lean` | The four-dimensional volume element squares to the product of the four diagonal signs. The negative scalar occurs exactly for one or three negative signs. |
| `PMArch/RankEight.lean` | Poisson summation for any positive-definite real quadratic form on ℤⁿ (with a real character), by induction on rank via one-dimensional Poisson summation and the Schur complement. A positive-definite even unimodular integral Gram matrix has rank divisible by 8 (`rank_dvd_eight`), hence minimal rank forces rank 8 (`minimal_rank_eight_of_lattice`); the E8 Gram matrix satisfies the hypotheses. |
| `PMArch/ThetaE8.lean` | For a rank-8 positive-definite even unimodular Gram matrix, the theta series is a level-one modular form of weight 4 (holomorphy, boundedness at ∞, invariance under `T` and `S`), hence equals `E₄` (`thetaMF_eq_E₄`); comparing `q`-coefficients gives exactly 240 vectors of norm 2 (`card_roots_eq_240`). Checked on the explicit E8 Gram matrix (`e8_card_roots`). |
| `PMArch/ClockPlane.lean` | The clock as a substrate plane (Closure): the half-norm of any plane in an even lattice is an integral binary form with discriminant −det(Gram), so complex multiplication is forced (`plane_form`). E₈ contains a clock plane with form x² + xy + 11y², D = −43 (`e8_clock_plane`), whose discriminant group (cokernel of the Gram matrix) is ℤ/43 (`clock_glue`, `clock_glue_period`); identifying the clock states with this group is the remaining modeling step. |
| `PMArch/ProtocolToll.lean` | Parallel Ohmic channel addition and effective resistance; unit-admittance Protocol credit, including a normalization counterexample; general Toll event injection, counts, normalized uniform sampling, mass bounds, product factorization, and equality to `tollTerm` under admissibility and χ ≤ N. The physical channel law and selected event remain explicit model inputs. |
| `PMArch/ImpedanceTerms.lean` | Purely mathematical steps inside the System 2 term arguments: a shift-invariant credit on an n-cycle with total χ is uniform χ/n (`governor_uniform`, `governor_baseline`); the sphere uniquely maximizes the Euler characteristic of closed surfaces (`euler_le_two`, `euler_eq_two_iff`); a tree with σ edges has σ+1 vertices (`tree_vertices`) and an acyclic graph whose center touches every vertex is a star (`radius_one_star`); product configuration spaces multiply (`margin_volume`). The choice of what each term counts, its sign and unit weight remain premises. |
| `PMArch/Clock.lean` | Integral clock: positive-definite integral binary forms, Gauss reduction (`exists_reduced`), and clock selection — for 32 ≤ \|D\| ≤ 64 all forms of discriminant D are equivalent iff D = −43 (`clock_unique_iff`), with no class-number classification used. The residue ring O_D/(√D) is ℤ/\|D\| for odd D (`residue_ring`), so the clock period is \|D\| (`clock_period`). Composed with scheduling: `schedule_selects_43_of_clock`, `schedule_impedance_bounds_of_clock`. |
| `PMArch/Sectors.lean` | Sector selection: among the rank-4 simply-laced root lattices, only `D₄` is irreducible with involutive glue `2Λ* ⊆ Λ` (`sector_selection`; completeness of the candidate list is the ADE classification). `ν = 16` for any two distinct 8-dimensional channels (`nu_eq_sixteen`). Relational time: with observations recording only whether an idle run follows each active transition, schedules with idle runs ≤ k are reconstructable iff k ≤ 1 (`obs_injOn_iff`), hence Δ ≤ 2N (`period_le_two_mul`); lengthening a run aliases (`aliasing`). |
| `PMArch/Comparison.lean` | Certified deviations `(Z_geo − α⁻¹_exp)/σ` for the Morel, Fan, Parker and CODATA inputs (`alpha_deviations`; the measured values are external inputs); Postulate R as an exact translation: on a finite state space, never merging states ⇔ bijective update (`never_merge_iff_bijective`). |
| `PMArch/Pillars.lean` | Counterfactual failure modes of the six PM pillars under explicit discrete-time models. With each pillar's mechanism the failure is excluded; without it an explicit trajectory fails: Capacity (`capacity_sustains` / `starvation`, finite lifetime ≤ r₀/d + 1), Margin (`margin_iff`: tolerance ⇔ positive distance to the non-viable set; `fragility`), Map (`map_maintains` / `dissolution`), Protocol (`protocol_coheres` / `decoherence`), Toll (`toll_excludes_zeno` / `zeno_without_toll`), Governor (`governor_bounds` / `runaway`). |
| `PMArch/Translation.lean`, `PMArch/TranslationD.lean` | Exact translations of the lattice postulates into statements about lattice states and their theta series: positive-definite ⇔ every cost level `{Q ≤ c}` contains finitely many lattice vectors (`posDef_iff_finite_levels`); all norms even ⇔ `θ(τ+1) = θ(τ)` (`even_iff_T_invariant`); unimodular ⇔ `θ(s) = s^{-n/2} θ(1/s)` (`unimodular_iff_S_covariant`). |
| `PMArch/Postulates.lean` | Independence: `ℤ`, `A₁`, the hyperbolic plane, and `E8 ⊕ E8` each satisfy all but one of positive-definite, even, unimodular, minimal rank (`evenness_needed`, `unimodularity_needed`, `positivity_needed`, `minimality_needed`). |
| `PMArch/E8Unique.lean` | Uniqueness of E8: 2160 norm-4 vectors from `θ = E₄`; a pigeonhole argument on `L/2L` gives an orthogonal frame of eight norm-4 vectors congruent modulo `2L`; these span `D8`, self-duality and evenness supply a glue vector, and an explicit integral change of basis carries the lattice to the E8 Gram matrix (`e8_unique`). |
| `PMArch/Lattices.lean` | Explicit E8 integral Gram matrix and inverse; evenness, positivity, unimodularity and real duality; a D4 ⊕ D4 embedding and its four glue cosets. |
| `classification/Classification.lean` | Full imaginary-quadratic class-number-one proof (vendored, unmodified), actual field discriminants, and the 32–64 window selecting 43. |
| `PMArch/ClassNumber.lean` | Links the classification to the scheduling argument: the absolute discriminant of a class-number-one imaginary quadratic field lies in the candidate list, so `schedule_selects_43_of_field` and `schedule_impedance_bounds_of_field` replace the candidate-membership hypothesis by an actual number field. |
| `PMArch/MainResult.lean` | Composes the scheduling/candidate hypotheses with the baseline impedance model to obtain the certified interval with the period initially unspecified. |

The main numerical theorem is:

```text
137.035999212381397211 < geometricIndex
geometricIndex < 137.035999212381397213
```

The exact expression is:

```text
43π + 2 - 1/167 - 2/43
    + 334/(32^3 · 5 · 172) + 1/(31 · 6 · 43^2)
```

All divisions occur in the real numbers, and all decimal endpoints are exact
rational literals. The bound follows from mathlib's proved 20-decimal lower and
upper bounds on π, not a floating-point computation. `Parameters.Admissible`
records positivity conditions sufficient to avoid zero denominators and is
proved for the baseline. Lean's total division convention is not used to excuse
an invalid baseline.

## Assumption boundary

1. **Serialization model:** channels are represented by `Fin N` and temporal
   slots by `Fin Δ`; serialization is assumed injective. This does not prove
   that physical causality demands such an encoding.
2. **Idle-slot model:** advancement is a permutation and every idle slot is
   followed by an active slot. The upper bound is valid even for multiple
   cycles, hence also for a single cycle. The concrete witness uses `finRotate`.
   The paper's argument that closure requires isolated idle slots is not proved.
3. **Count identification:** the composed theorem explicitly assumes 32 active
   slots as well as an injective encoding of 32 channels. It does not silently
   identify Hilbert-space dimension, information in bits, and transition count.
4. **Discriminant candidates:** `{3,4,7,8,11,19,43,67,163}` is a finite definition;
   `PMArch/ClassNumber.lean` derives candidate membership from the class-number-one
   classification in `classification/` and the actual field discriminant. The
   physical identification of a period with a field discriminant remains a
   hypothesis (`hΔ`).
5. **Other architectural integers:** dimension 4, sector capacity 16, embedding
   dimension 5, and Euler characteristic 2 are baseline inputs. Their alleged
   necessity from E8, triality, or persistence is not asserted.
6. **Impedance law:** the individual terms, signs, unit coefficients, and
   additivity are definitions of this model. The Additive Impedance Theorem in
   the manuscript has not been formalized as a consequence of geometry.
7. **Physical correspondence:** `causalCoupling` is defined as the reciprocal
   index. The conditional electromagnetic matching implication is now checked, but its
   premise (the microscopic Maxwell coefficient) is not derived. No measurement
   validation or microscopic QED/vacuum model is included.

In particular, the numerical theorem alone verifies an expression, not the
physical reasoning that selects it. `schedule_impedance_bounds` makes the
currently formalized portion of the derivation explicit.

## Mapping to the manuscript

- `paper/4_system0_requirements.tex`: serialization/pigeonhole inequality.
- `paper/5_system1_projection.tex`: relational-time bound, discriminant filter,
  capacity, resolution, and loads.
- `paper/6_system2_impedance.tex`: the six-term finite sum and reciprocal coupling.
- `calculations/constants.py`: numerical counterpart; the Lean expressions use
  exact real arithmetic rather than Python floating-point results.

## Physical derivation extension

`PhysicalBridge.lean` supplies precise conditional statements for the physical
interpretations, including two concrete finite sample spaces and a Maxwell
normalization equation. `paper/*.tex` now states the corresponding postulates,
proofs, and outstanding obligations in the sections where they are used. See
[DERIVATION.md](DERIVATION.md) for the dependency map.

The finite sample spaces are realizations of the stated cost rules, not evidence
that the rules are uniquely selected by the substrate. The exponential-weight
construction likewise proves consistency of the chosen additive action, not its
physical necessity. The SI identities are conditional algebra, not independent
proofs of charge quantization, Hall transport, or pair production.

## Next proof obligations

Autonomous evolution and observation are now explicit. A microscopic physical
model is still needed to select the lattice and class-number constraints. Specific gaps to
resolve include finite description versus discreteness; the extra condition
selecting a sphere over a separating toroidal boundary; the connection between
CM isomorphism classes and histories; and justification of statistical
independence and unit weights in the impedance law. Unimodularity alone does not
supply unit vector norms, and orthogonal vectors have zero inner product.

The explicit E8/D4 construction is supplied, and the lattice selection is now fully
formalized: `rank_dvd_eight` proves that positive-definite even unimodular lattices have rank
divisible by eight, `card_roots_eq_240` and `card_norm_four` read the root and norm-4 counts off
`θ = E₄`, and `e8_unique` (`PMArch/E8Unique.lean`) proves that every such lattice of rank 8 is
integrally equivalent to the explicit E8 Gram matrix. No lattice-classification result is assumed.

The Clifford result is an algebraic signature calculation; it does not select a
physical metric. The scheduling existence theorem does not justify the physical
choice of its scheduling rules. See `classification/PROVENANCE.md` for the
external proof's source revision, author, and license.

## Protocol/Toll review verification (2026-10-27)

After adding `ProtocolToll.lean`, `lake build` completed successfully (9003 jobs).
The strengthened module-aware audit passed for all 671 PMArch declarations,
including private helpers and declarations outside the usual namespace when
they originate in a PMArch module. The three standard logical axioms remain
the only permitted transitive dependencies. Protocol and Toll remain
conditional on their explicitly stated channel and sampling laws.

## Persistence-to-vacuum claim audit

See [CLAIM-AUDIT.md](CLAIM-AUDIT.md) for the exact current claim and missing
implications. `PMArch/ClaimBoundary.lean` composes the finite-cost/state-sum
constraints into E8 selection with explicit global rank minimization, and
composes clock selection with conditional electromagnetic matching. It also
checks operational response and cost-normalization freedom. These results do
not establish that persistence alone forces the vacuum substrate or coupling.

The claim-boundary update built successfully (9004 jobs), and the strict
module-aware audit passed for all 705 PMArch declarations.

## Lattice, symmetry and selection foundations

`PMArch/ConstraintFoundations.lean` constructs integer coordinates and a
positive integral Gram representation from explicit additive-address and cost
constraints. It supplies finite-cost, reversible counterexamples to deriving
the required modular symmetries from conservation alone, and proves
asymptotic rank preference under a common full-coordinate refresh cost model.
See [CONSTRAINT-FOUNDATIONS.md](CONSTRAINT-FOUNDATIONS.md) for the remaining
physical obligations. `AuditFoundations.lean` audits the new module and all its
transitive axiom dependencies.

Verification: full integration build passed (9005 jobs); the foundations
strict transitive axiom audit passed for all 25 added declarations.

## Operational duality investigation

`PMArch/OperationalDuality.lean` characterizes unimodularity by integer and
finite readout completeness, distinguishes fixed-clock encoding from that
requirement, and checks a positive even non-unimodular parent retaining the
actual determinant-43 E8 clock plane. It also checks basis-relabeling
invariance, homogeneous reversible pointwise updates, a lossless two-sector
transform, and an evenness implication from an explicit parity-exchange
operator law. The composed E8 theorem retains the operator/readout/minimum
rank premises. See [OPERATIONAL-DUALITY.md](OPERATIONAL-DUALITY.md).
`AuditOperational.lean` audits the new module and its transitive axiom
dependencies. These are not necessity proofs from closure alone.

Operational-duality verification: complete integration build passed (9006
jobs); the strict module-aware audit passed for all 25 added declarations.

## Intrinsic constraints and fixed-rank alternatives

`PMArch/IntrinsicConstraints.lean` checks intrinsic additive norm parity, its
conservation, an explicit reversible parity-corrected exchange example, and
lossless readout reconstruction/congruence using the image lattice. It also
checks two rank-eight alternatives retaining the determinant-43 clock form,
including an odd unimodular parent with two D4 root sectors and an even
non-unimodular E8 sublattice. The exact failures of the scalar T and S laws
are proved. See [INTRINSIC-CONSTRAINTS.md](INTRINSIC-CONSTRAINTS.md).
`AuditIntrinsic.lean` audits the new module and all transitive axiom
dependencies. These results do not close the persistence-only vacuum claim.

## Orthogonal exchange locality

`PMArch/OrthogonalExchange.lean` formalizes the main theorem from the supplied
independent research note: a nontrivial alternating bi-additive binary exchange
form that vanishes on B-orthogonal pairs forces an integral symmetric B to be
even. The direct proof avoids ideal factorization. An E8 exchange-form witness
and a composed conditional E8 selection theorem are included. Physical
necessity of locality/nontriviality and the operator-to-form bridge remain open.
See [CLAUDE-EXCHANGE-REVIEW.md](CLAUDE-EXCHANGE-REVIEW.md).
`AuditOrthogonal.lean` audits all new declarations and their transitive axiom
dependencies.

Orthogonal-exchange verification: the complete library build passed (9008
jobs), and the strict transitive axiom audit passed for all 19 new
declarations.

## Protocol, Toll and Causality necessity tests

`PMArch/NecessityTests.lean` proves commutation for independent state factors,
constructs finite autonomous reversible protocols with central noncommuting
exchange and positive loop action, and supplies faithful integer-label
operations. It also checks a commuting 43-slot clock, a finite-history
capacity bound and the Clifford algebra consistency issue from Paper II.
These test proposed necessity arguments; they are not quantum-vacuum models.
See [NECESSITY-INVESTIGATION.md](NECESSITY-INVESTIGATION.md).
`AuditNecessity.lean` audits all new declarations and their transitive axiom
dependencies.

Necessity investigation verification: full integration build passed (9009
jobs); strict module-aware transitive axiom audit passed for all 49 new
declarations.
