# Intrinsic readouts, parity and fixed-rank alternatives

This follow-up tests whether the operational premises in the preceding investigation can be obtained from conservation, lack of external controls, and the clock/sector structure. It does not adopt additional physical axioms to force E8.

## Readout reconstruction does not require the whole ambient codomain

For every positive integral Gram matrix A, the state-to-readout map z -> A z is injective. `intrinsicReadout` constructs the canonical equivalence from the integer state space onto the readout image. `intrinsic_readout_reconstructs` proves exact recovery. Both spaces and the map are determined by A; no external dictionary or extra label is supplied.

`natural_readout_congruence` checks the finite-resolution statement:

    x-y is in m Z^n  <=>  A x-A y is in m A Z^n.

This holds even for non-unimodular A. Consequently, the distinction is not merely between infinite exact readouts and finite encodings. Finite distinctions can be carried losslessly when the probe uses the resolution inherited from its own image lattice.

The preceding unimodularity characterization instead required readout completeness in the same ambient integer lattice and primitive units as the states. That is a substantive alignment requirement. It cannot be inferred merely from injectivity or reconstruction. An argument selecting unimodularity must explain why the physical probe and the state labels must share those primitive units, rather than presume that alignment in the definition of completeness.

This is a statement about candidate encodings, not a derivation of the physical measurement space or apparatus.

## Norm parity is intrinsic

For an integral symmetric pairing, define p(z)=B(z,z) mod 2. The quadratic identity

    Q(x+y)=Q(x)+Q(y)+2 B(x,y)

makes p additive. `parity_add` proves this, and `parity_preserved` proves that cost-preserving updates conserve p. It is a function of the existing state, not an independent externally chosen bit. `trivial_parity_iff_even` proves that requiring p to vanish identically is exactly the original evenness condition; it is not a new necessity argument.

The parity-corrected exchange exponent is B(x,y)-p(x)p(y) modulo two. Its diagonal vanishes because k-k^2 is even for every integer k. This removes the diagonal obstruction on odd lattices. `corrected_diagonal_even` checks that fact for every integral Gram matrix.

For the rank-one odd pairing B(x,y)=xy, `odd_lattice_reversible_exchange` supplies a full concrete exchange example: the operations are faithful reversible integer shifts, and xy-x^2 y^2 is always even. The correction is computed from x,y. This demonstrates algebraic consistency of an alternative exchange rule; it does not assert that the physical vacuum uses that rule. A general realization for every lattice or a microscopic quantum dynamics is not claimed.

A correction term also does not automatically imply extra computational overhead. In the rank-one example the complete exchange phase is identically trivial; its implementation can use that simplified rule without computing an additional parity bit at run time. A cost-selection argument would need an explicit implementation and comparison model.

Thus conservation and absence of externally supplied parity do not select the uncorrected exchange rule. The open task is to distinguish that rule from internally parity-corrected rules on independent physical grounds. Global reversibility alone also does not imply invertibility of every projected excitation operator.

## Counterexamples at exactly rank eight

The earlier E8-plus-A1 example increased the rank. The new examples keep the rank equal to eight and retain the determinant-43 clock form.

| Property | E8 | Identity Gram matrix on Z^8 | Stretched E8 sublattice |
| --- | --- | --- | --- |
| Rank | 8 | 8 | 8 |
| Positive definite | Yes | Yes | Yes |
| Even | Yes | No | Yes |
| Unimodular | Yes | Yes | No |
| Contains clock Gram [[2,1],[1,22]] | Yes | Yes | Yes |
| Canonical readout reconstructs its states | Yes | Yes | Yes |
| Required scalar T law | Yes | No | Yes |
| Required scalar S law | Yes | Yes | No |

For the identity Gram matrix, the clock vectors are

    u=(1,1,0,0,0,0,0,0),
    v=(2,-1,4,1,0,0,0,0).

They lie within the first four coordinates and have norms 2,22 and pairing 1. The new `rootBasis` injection and `odd_parent_two_d4_norms` also certify two orthogonal standard D4 root sectors inside this odd parent. These shared root sectors do not require the whole parent to be even.

For the even alternative, let P be diagonal with seven entries equal to one and the last equal to two, and set A'=P^T G_E8 P. It is a rank-eight even positive integral sublattice but is not unimodular. The earlier E8 clock vectors have zero last coordinate, so P fixes them and their clock Gram matrix remains unchanged. `even_parent_fails_S` proves failure of the scalar inversion law; `odd_parent_fails_T` proves failure of the unit theta shift for the odd parent.

The examples have finite bounded-cost levels by the earlier positive-definiteness/finiteness equivalence. They are not asserted to satisfy the explicit evenness or unimodularity postulates they were constructed to violate, nor all requirements of a complete physical vacuum. Their purpose is to test proposed derivations of those postulates. Minimum rank within the already even unimodular class cannot be used to establish membership in that class without a circular argument.

## Consequence for the intended proof

The current conditions leave two separate choices unresolved:

1. Why must physical state labels and readouts share the same primitive ambient lattice, beyond admitting an intrinsic lossless encoding?
2. Why must the operator exchange phase be the uncorrected norm-pairing phase, beyond admitting consistent reversible operations with an intrinsic parity correction?

These are physical selection questions, not missing numerical calculations or missing Lean tactics. The successful E8 classification remains conditional on excluding the explicit alternatives. A microscopic state/update/probe construction could establish new necessary conditions, but it must do so without presupposing E8, its scalar theta symmetries, or the desired fine-structure value.

The six-term cost law, its normalization and electromagnetic matching remain separate open obligations. This follow-up does not claim the persistence-only vacuum theorem has been proved.

## Independent collaboration

`Claude-parity-necessity-task.md` is a self-contained read-only assignment for an independent investigation of the second question. The main Lean work is continuing separately to avoid conflicting edits.

## Verification

The new module compiled successfully (3960 jobs). Its strict module-aware
axiom audit passed for all 52 declarations, including generated helpers and
transitive dependencies. Only propext, Classical.choice and Quot.sound are
allowed. No physical axioms or admitted proofs were introduced.

The complete PMArch integration build also passed (9007 jobs). Existing
manuscript content and experimental inputs were preserved.
