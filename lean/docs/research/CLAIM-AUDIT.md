# Paper I: persistence, E8 and the inverse fine-structure constant

## Target and present status

The target is a derivation in substance: independently justified persistence/vacuum constraints should select a substrate and its electromagnetic response without selecting formulas by their agreement with the desired answer.

The current Lean development does not prove that Finiteness, Conservation and Causality, together with the statement that the vacuum persists, imply E8 and the number 137.035999212.... It proves substantial conditional mathematics. The missing premises are mathematical/physical implications, not missing decimal precision or wording.

No new physical postulate has been installed as a global axiom. The new `PMArch/ClaimBoundary.lean` makes the claim boundary executable.

The existing six-pillar failure-mode proofs also use specified dynamical models. They do not turn the PM paper's general completeness conjecture into an unconditional classification of everything that persists. Accepting Finiteness, Conservation and Causality as postulates is distinct from proving their proposed lattice realization is necessary.

## What is proved

1. An integral quadratic lattice has positive-definite cost exactly when every bounded-cost sublevel set is finite (assuming symmetry of its Gram matrix).
2. For this lattice class, evenness is equivalent to the specified theta shift invariance, and unimodularity to the specified weight-corrected theta inversion covariance.
3. A nonzero positive-definite even unimodular integral lattice has rank divisible by eight. E8 realizes rank eight. Minimizing rank within this entire class therefore selects rank eight, and the earlier uniqueness proof selects E8 up to integral isometry.
4. With the stated channel encoding, scheduling and clock arithmetic constraints, the period is 43. Clock existence, schedule realizability and the class-number classification have checked proofs; their physical applicability still has premises.
5. The specified six-term cost law at the baseline has the certified value

       137.035999212381397211 < Zgeo < 137.035999212381397213.

6. If the physical squared coupling satisfies 4 pi / gSquared = Zgeo in the stated charge convention, the inverse coupling inherits exactly those bounds.

The new `state_sum_selects_e8` theorem composes steps 1–3. Unlike an assumed upper bound of eight, its minimality condition quantifies over every nonzero positive even unimodular integral lattice. Rank eight follows by comparison with the existing E8 witness. The theorem explicitly assumes a quadratic integral lattice, the two theta symmetries and rank minimization. It does not relabel those assumptions as consequences of persistence.

The new `clock_and_matching_select_inverse_coupling` theorem composes the schedule selection with the conditional electromagnetic interval. It exposes the electromagnetic matching equation as an argument. The other baseline integers and six-term constitutive expression remain model inputs.

## Missing implications, in order

| Intended step | What is needed | Why the current premise is insufficient |
| --- | --- | --- |
| Persistent vacuum -> lattice | Derive an additive discrete address structure and integral quadratic cost from independently specified vacuum constraints | Finite resources or finite descriptions admit many graphs and state spaces; neither forces a lattice or a quadratic cost |
| Conservation -> theta symmetries | Explain why the vacuum's state enumeration must have the specified T and S transformation laws | Preservation of identity, or even bijective evolution, does not imply modular transformations of a statistical state sum |
| Persistence -> minimum rank | Establish the comparison family, cost functional, weights, selection dynamics and why higher ranks are excluded | Survival bias is conditional on hazard and prior assumptions; persistence does not assert global minimization. Even unimodular lattices also exist above rank eight |
| E8 -> clock/sectors/costs | Derive the physical sector choice, clock interpretation, events, weights, signs, saturation and normalizations | Existence of these objects in E8 does not prove that the vacuum dynamics selects or uses them |
| Geometric index -> electromagnetic response | Compute the normalized infrared electromagnetic response from that same dynamics | Defining a reciprocal index or assuming the Maxwell matching coefficient does not compute the physical coupling |

The rank theorem and E8 uniqueness are already real theorems. Work should concentrate on these missing arrows, rather than repeat their proofs or assert E8 selection is wholly unformalized.

## Checked independence witnesses

Existing `Postulates.lean` supplies lattices distinguishing evenness, positivity, unimodularity and minimality. For example, the rank-one integer lattice is positive and unimodular but odd; E8 plus E8 is positive, even and unimodular but not minimal. Existing `ProtocolToll.lean` shows the chosen admittances and trial arity affect the numerical terms.

The new module adds a nontrivial finite reversible clock with a conserved binary label and a strictly positive tick. Its response coefficient can be any positive real number without altering its update or tick. This is an explicit operational interpretation of finite resources, identity preservation and ordered updates. It is not a complete formalization of every possible meaning of the PM postulates, nor a competing quantum-vacuum construction. It demonstrates precisely why those operational properties, on their own, do not constrain a response coefficient.

It also checks that multiplying a cost by a positive constant preserves every supplied cost symmetry and its zero set. An independent normalization principle or an operational response calculation is therefore needed; symmetry and positivity alone do not fix that scale.

## How to pursue the intended result without hand-picking

First specify the general class of vacuum candidates without mentioning E8, 43, the six-term expression or the target decimal. State the independent vacuum requirements and what each observable means. Then require each selection theorem to rule out alternatives within that class.

If a proposed constraint is chosen because it gives E8 or 137.035999..., that is a model choice until independently justified. Constraints may legitimately be foundational postulates, but the theorem must then be described as conditional on those postulates. Logical assumptions do not cease to be assumptions when written as constraints.

The next useful construction is an explicit local reversible/unitary dynamics with a well-defined state measure and an independently normalized probe response. It could supply the missing physical premises. If several inequivalent constructions satisfy the same requirements but predict different responses, the right result is an underdetermination theorem and a stated additional physical principle—not a forced decimal.

The desired numerical quantity here is the dimensionless inverse fine-structure constant. A geometric dimensionless index and the vacuum's SI impedance in ohms are different observables and require their stated conversion/matching conventions.

## Wording justified now

> We give Lean-verified proofs that the stated lattice and state-sum constraints, together with minimum nonzero rank, select E8 up to integral isometry. Additional explicit clock and constitutive assumptions determine a dimensionless index with certified value 137.035999212.... Its identification with the inverse infrared fine-structure constant is conditional on electromagnetic matching.

The stronger target remains:

> Independently specified persistence and vacuum constraints imply these lattice, state-sum, selection and response premises, so that E8 and the physical inverse fine-structure constant follow without further constitutive choices.

That final implication is not proved by the current development. This audit does not claim to have closed it.

## Verification of this update

The complete PMArch library build passed (9004 jobs). The strict module-aware
axiom audit passed for all 705 PMArch declarations. Only propext,
Classical.choice and Quot.sound are allowed; no physical axioms or admitted
proofs were introduced. Existing manuscript edits were preserved.

The complete `check.sh` run finished with exit status 0, including the printed
axiom dependencies and the separate class-number audit.
