# Operational duality investigation

## Finding

Autonomous closure, homogeneous local updates, ordinary basis independence and the existing clock requirement do not yet force the two scalar theta symmetries. This update identifies stronger operational requirements that would suffice, and tests why the existing conditions do not automatically supply them.

The new results are in `PMArch/OperationalDuality.lean`. They are mathematics about specified models, not a construction of a quantum vacuum or an unconditional calculation of the fine-structure constant.

## Closure and homogeneity

The paper defines closure as a fixed state space and an autonomous update without a time-dependent external control input. A reversible pointwise reflection has this property. The new proofs show it is its own inverse and commutes with every relabeling of sites: its local rule is identical at each site, including under translations. Cost preservation is supplied by the previous reflection theorem.

Thus homogeneity does not remove the earlier odd/non-unimodular counterexamples merely by forbidding a preferred spatial origin for the local rule. These operational models are not asserted to satisfy every condition of a full physical vacuum.

## Basis independence is not scalar modular covariance

`theta_relabel_invariant` proves that a cost-preserving bijection of the integer labels leaves the theta state sum unchanged. No evenness or unimodularity is needed. This covers ordinary relabeling/basis independence once the corresponding cost-preserving coordinate identification is given.

That operation must be distinguished from changing the complex statistical parameter by T or S. The latter produces the special phase and inversion constraints used for E8 selection. An autonomous time update, a basis change in the address lattice, a basis change in the clock plane, and a transformation of a statistical parameter are not automatically the same operation. An identification between them needs a construction and a proof.

## A precise operational route to unimodularity

For an integral Gram matrix A, an integer state z gives the integer readout A z. `integer_readout_iff_unimodular` proves:

    every integer readout is realized by a state <=> det(A) is a unit.

A finite version asks for every residue label b to be realizable modulo q:

    A z + q w = b,    for some integer vectors z,w.

The auxiliary vector w records the congruence; it is not an added physical degree of freedom. `intrinsic_readout_iff_unimodular` proves that completeness even at the intrinsic modulus q=|det A| suffices for unimodularity, assuming positive definiteness. The proof uses the adjugate identity: every det(A) w is already in the image of A. Therefore failure of an exact readout cannot be hidden at that modulus.

`all_finite_readouts_iff_unimodular` proves the equivalent requirement of readout completeness at every positive finite modulus. The underlying cardinality obstruction is now explicit rather than an assertion that Fourier normalization destroys information.

This requirement remains extra. Closure says that the chosen state space and its update are self-contained; it does not say that every abstract integer readout must be representable by a state through the same pairing. A restricted set of readouts can be conserved exactly. Nor does finite capacity imply access to every resolution. Stating readout completeness as a new constraint is a valid conditional specification, but is not yet a derivation of its physical necessity.

The dual lattice is determined by the original lattice and its pairing; a different dual does not, by itself, require an externally supplied structure. For example, the determinant-two scalar readout 2x=b has the unique real solution x=b/2. Requiring that solution to be integral is stronger than requiring it to be internally determined or uniquely reconstructable.

## The fixed clock does not supply that completeness

`determinant_two_fixed_clock` and `two_mod_43_lossless` prove that multiplication by two is fully invertible modulo 43: its inverse is multiplication by 22. Yet it fails to realize the odd readout modulo two. A lossless 43-state encoding therefore does not force unimodularity over the integers.

The stronger embedded-clock test uses the explicit parent lattice

    E8 direct-sum A1.

`clock_parent_positive_even_nonunimodular` checks that it is positive definite and even but not unimodular. `augmented_clock_gram` checks that it retains the exact earlier clock plane with Gram matrix [[2,1],[1,22]], hence determinant 43. The orthogonal extension does not change that plane's form, discriminant or arithmetic clock geometry. This is an obstruction to deriving parent self-duality from the plane's existence. It is not a claim that this parent obeys every other model-selection postulate, such as minimum rank in an already unimodular class.

The paper already uses a nontrivial discriminant group as the clock's internal finite state space. A nontrivial discriminant group therefore cannot be treated as an automatic failure of closure. A separate argument is needed for why the complete vacuum, as opposed to its clock subsystem, must have only one discriminant sector.

## Internal sectors can transform without losing information

`normalized_sector_mix_exists` constructs the two-sector real matrix

    H = (1/sqrt(2)) [[1,1],[1,-1]],

and proves H H=I and H^T H=I. This is a finite lossless algebra certificate. It does not prove a vector-valued theta transformation or construct the physical Hilbert space. Its role is narrower: mixing multiple internal components with a normalization factor does not by itself imply erasure or dependence on an external controller.

## An operator-consistency route to evenness

The new `parity_exchange_forces_even` theorem takes an explicitly specified reversible operator family U_z and a nontrivial phase epsilon. Suppose its exchange rule is

    U_x U_y = phase(B(x,y)) U_y U_x,

where phase(k) is identity for even k and epsilon for odd k. Setting x=y, invertibility forces phase(B(x,x)) to be identity; therefore every norm is even. This is an algebraic consistency result: invertible operations cannot anticommute with themselves.

The unresolved physical step is selecting this exchange-phase rule from the substrate dynamics. Generic conservation of the whole update does not imply that every excitation operator is invertible, or identify its exchange phase with norm parity. A trivial exchange phase is compatible with commuting reversible translations on an odd lattice. The normalization that distinguishes a full phase turn from the proposed half-turn also needs justification. This update does not supply an operator realization or prove that this particular exchange law is necessary for the vacuum.

## Composed conditional theorem

`operational_premises_select_e8` combines the parity-exchange condition and intrinsic readout completeness with the previous finite-cost and minimum-rank constraints. It derives evenness and unimodularity, then the theta symmetries, then E8 up to integral isometry. The two theta laws are not direct hypotheses of this theorem.

This is a more operational statement of what a microscopic theory would need to establish. It does not make the extra premises consequences of PM by renaming them: their physical necessity and joint realization remain open. The earlier asymptotic full-refresh selection model remains conditional, as do the six-term impedance law and electromagnetic matching.

## Next decisive requirement

The remaining necessity argument must establish why all intrinsic readout sectors of the *complete vacuum* must be realizable through the same pairing, and why its reversible operations obey the specified parity exchange law. It must exclude the explicit counterexamples without using E8, the desired decimal, or the desired scalar theta covariance as premises. The current definitions of closure, homogeneity and the clock do not do this.

## Verification

The new module compiled successfully (3959 jobs). Its module-aware strict
axiom audit passed for all 25 declarations, including generated helpers and
transitive axiom dependencies. Only propext, Classical.choice and Quot.sound
are allowed. No physical axioms or admitted proofs were added.

The complete PMArch integration build also passed (9006 jobs). Existing
manuscript content and experimental inputs were not changed in this update.
