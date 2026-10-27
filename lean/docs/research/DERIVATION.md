# Physical derivation: dependency map

The paper now presents a conditional model. No physical postulate is installed
as a global Lean axiom, and none is claimed to follow merely from persistence.

| Step | Explicit input | Checked consequence | Manuscript location |
| --- | --- | --- | --- |
| Closure and conservation | Autonomous bijective update, fixed elapsed time, injective observation | Unique reconstruction; counterexample without informative observation | System 0 |
| Positive configuration cost | Nonnegative cost with zero only at the zero state | Strict positivity off zero | System 0 |
| E8 selection | Positive even unimodular lattice classification; minimal nonzero rank | Rank divisibility by 8 (theta series + n-dimensional Poisson summation) and minimal-rank selection of 8 are proved; explicit E8/D4 construction, evenness, positivity, duality, and four glue cosets are checked; uniqueness of the rank-8 lattice (E8) is proved | System 1 |
| Boundary | Connected closed orientable surface and maximal Euler characteristic | Supplied Euler formula forces genus zero; topology classification remains external | System 1 |
| Clock | Clock plane is a rank-2 substrate sublattice (Closure) whose states are its discriminant group Λ_c*/Λ_c (parameter-free finite state set; identification is a modeling step), unique geometry given its discriminant, injective serialization, gap-only observations | Evenness of the substrate forces an integral clock form and hence CM (`PMArch/ClockPlane.lean`); E₈ contains the D = −43 clock plane, whose discriminant group is ℤ/43; Δ = |D| is the size of the residue ring; Gauss reduction proves uniqueness only at D = −43 in [32, 64] (`PMArch/Clock.lean`); the imported classification independently gives the fundamental list (`PMArch/ClassNumber.lean`); idle runs ≤ 1 is derived from gap-only observations (`PMArch/Sectors.lean`); period is 43; cyclic schedule existence is equivalent to N ≤ Δ ≤ 2N | System 1 and CM appendix |
| Capacity | Round planar envelope, causal radial bound, saturation, unit boundary action density | Circumference bound and equality under saturation | System 2 |
| Map | Defect boundary is a closed connected surface; one unit of cost per unit χ | Sphere uniquely maximizes χ = 2 (`PMArch/ImpedanceTerms.lean`) | System 2 |
| Governor | Total feedback credit χ distributed over the Δ-cycle; Homogeneity (no preferred slot) | Per-slot share is exactly χ/Δ (`governor_uniform`) | System 2 |
| Toll | Uniform three-leg product space with the specified event | Event has 334 elements; probability equals the Toll term | System 2 |
| Margin | Uniform 31 × 6 × 43 × 43 label space and a specified singleton; local interaction is a tree on σ = 5 edges localized to radius one | Singleton probability equals Margin; such a tree has σ + 1 = 6 vertices and is the star (`tree_vertices`, `radius_one_star`) | System 2 |
| Additivity | Positive factorized relative weights; exp(-cost) convention | Negative log weight is the sum of signed costs | System 2 |
| Admittance | Coupling defined as reciprocal index | Normalized binary probability distribution | System 2 |
| Electromagnetism | Infrared U(1) theory, charge normalization, Maxwell coefficient g⁻² = Zgeo/(4π) | α⁻¹ = Zgeo and the certified numerical interval | Correspondences |
| SI observables | Conventional definitions of α, Z₀, h, Compton wavelength, Schwinger field scale | Resistance and field identities | Correspondences |

## What is still missing for an unconditional physical derivation

1. A microscopic state space and update/Hamiltonian that realizes the lattice,
   sector and clock assumptions, with a justified observation/encoding scheme.
2. A derivation of the specified sampling events, weights, action density,
   feedback signs, and normalization coefficients from that dynamics.
3. An effective Lorentzian gauge theory with the required chiral charged matter
   and a justified account of mirror modes.
4. A computation of the infrared Maxwell response fixing the coefficient in
   the stated charge convention. For a generic Zgeo = C/g², Lean proves
   α⁻¹ = (4π/C) Zgeo: the number is not predicted until C is fixed.
5. A quantitative observable correction, with uncertainties, before any
   proposed high-order QED discrepancy is attributed to capacity limits.

The equations and numerical prediction are retained. Unsupported necessity
claims were replaced in their original sections, rather than left in the body
with an inconsistent caveat appended elsewhere. In particular, finite
specification does not force a lattice, topology alone does not quantize flux,
class number one does not reconstruct histories, and Euclidean internal
geometry does not imply static mirror states. The abstract, introduction, and
conclusion were aligned with the resulting scope.

## Verification

`./check.sh` builds the main library, audits every PMArch declaration, and
includes the class-number proof, which is built as a local package. The audit accepts
only standard logical foundations; `audit-negative-tests.sh` checks that
admitted proofs and added axioms are rejected. The manuscript is compiled with
LaTeX/BibTeX, and its rendered pages are checked for overflow and broken
references. No existing repository PDF or calculations script is overwritten.

## Exact target-claim audit

[CLAIM-AUDIT.md](CLAIM-AUDIT.md) separates the intended persistence-to-vacuum
theorem from what is presently proved. `PMArch/ClaimBoundary.lean` provides
composed conditional selection theorems and independence checks; it adds no
physical postulates as global axioms.

The follow-up [CONSTRAINT-FOUNDATIONS.md](CONSTRAINT-FOUNDATIONS.md) gives a
conditional construction of the integral positive-definite Gram model, exact
obstructions to deriving the required state-sum symmetries from reversible
cost conservation, and an asymptotic rank-selection mechanism conditional on
a common full-refresh workload. It does not establish the full FCC-to-E8
implication.

[OPERATIONAL-DUALITY.md](OPERATIONAL-DUALITY.md) tests closure, homogeneity,
basis independence and the actual clock-plane requirement against the missing
state-sum symmetries. Readout completeness and a parity-exchange algebra
suffice operationally, but their physical necessity and joint realization
remain unproved. The E8-plus-A1 example preserves the determinant-43 plane
while violating parent unimodularity.

[INTRINSIC-CONSTRAINTS.md](INTRINSIC-CONSTRAINTS.md) strengthens the symmetry
investigation to rank-eight clock-compatible alternatives. It distinguishes
lossless intrinsic readouts from alignment of ambient primitive units, and
intrinsic additive norm parity from externally supplied flags. An alternative
reversible exchange algebra is constructed for the odd rank-one pairing.
The physical selection of the uncorrected law remains open.

[CLAUDE-EXCHANGE-REVIEW.md](CLAUDE-EXCHANGE-REVIEW.md) records the checked
orthogonal-locality route to evenness, which removes the need to assume the
exact pairing exchange sign. The new premises are a binary alternating
bi-additive exchange form, vanishing on metric-orthogonal pairs, and nontrivial
exchange. Their physical necessity and operator realization remain separate
obligations.

[NECESSITY-INVESTIGATION.md](NECESSITY-INVESTIGATION.md) tests the Protocol,
Toll and Causality routes to orthogonal locality and nontrivial exchange.
Independent state factors imply commutation, but metric orthogonality does
not supply that factorization. Positive loop action and causal clocks are
compatible with the counterexamples. The physical operator sector must also
be distinguished from the Clifford generators used in Paper II.
