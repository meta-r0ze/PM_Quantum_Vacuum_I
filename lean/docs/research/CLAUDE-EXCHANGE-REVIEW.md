# Review of Claude's exchange-law research note

## Main result

The central orthogonal-locality theorem is sound in its stated binary exchange-form setting. It has now been formalized in `PMArch/OrthogonalExchange.lean`, with a shorter proof that avoids factorization through the image of an integer linear functional.

Let B be an integral symmetric bilinear form, and let C take values in Z/2, be bi-additive and alternating. Assume:

- Orthogonal exchange locality: B(x,y)=0 implies C(x,y)=0.
- Nontrivial exchange: C is not identically zero.

Then every B(x,x) is even. Positivity, unimodularity, minimum rank and a preselected law C=B mod 2 are not hypotheses of this implication.

This improves the conditional route to evenness. It does not derive the two new conditions from PM or construct their physical operator realization.

## Direct proof used in Lean

For a vector v of odd norm, write q=B(v,v) and b=B(v,z), and form

    w = q z - b v.

Then B(v,w)=q B(v,z)-b B(v,v)=0. Orthogonal locality gives C(v,w)=0. Bi-additivity and alternation give

    0 = C(v,w) = q C(v,z) - b C(v,v) = q C(v,z).

An odd integer acts as one on Z/2, so C(v,z)=0 for every z.

Norm parity is additive because B is symmetric. If one odd vector y exists, then for every x either x has odd norm, or x+y has odd norm. The rows C(x,.) and C(y,.) consequently vanish in either case. Thus C=0, contradicting nontriviality. There can be no odd norm.

The public checked statements include `odd_row_zero`, `odd_norm_trivializes_exchange`, and `orthogonal_nontrivial_exchange_forces_even`.

## Nonvacuity and composition

`e8_exchange_form_witness` constructs C=B_E8 mod 2 and checks that it is alternating, orthogonally local and nonzero. This establishes consistency of the abstract exchange-form premises on E8. It is not an operator representation or Hamiltonian.

`orthogonal_exchange_selects_e8` composes the new evenness theorem with the earlier finite-cost, intrinsic-readout completeness and minimum-rank constraints. It selects E8 up to integral isometry without assuming the exact pairing exchange sign at the outset. Readout completeness, rank selection and the physical applicability of the exchange form remain explicit arguments.

The raw group-to-exchange-form bridge is also a premise boundary: the new code starts with a bi-additive alternating Z/2-valued form. Deriving that form from actual operators, their central phases and Weyl composition is not presented as a consequence of PM. In particular, the binary phase codomain must stay explicit. The note's half-turn argument assumes a phase that is a power of the pairing; that conditional argument does not independently establish the most general operator phase structure.

## Qualifications to the rest of the note

### The Pauli example establishes less than a complete vacuum model

The example on C^2 correctly illustrates a nontrivial parity-corrected exchange algebra. But X^2=Z^2=I, so the assigned operator family is periodic in its integer labels: U_(x+2e_i)=U_x. It does not faithfully encode every distinct integer lattice label in those operators.

Unitarity preserves Hilbert norm. It does not, by itself, prove conservation of the integer label cost Q(x)=x_1^2+x_2^2. The lattice-label space, physical state space, update and cost functional need to be connected explicitly before claiming all operational vacuum premises hold. This limits the scope of the example; it does not invalidate its exchange-algebra counterexample.

Likewise, conjugation covariance of the internal operator family and homogeneity of a spatial local update are different statements. A bridge between them needs a specified spatial model.

### Exact equivalence needs a quantifier distinction

The previous `parity_exchange_forces_even` theorem indeed uses the prescribed exchange law only on its diagonal. The desired evenness is encoded in that diagonal assumption, so it is not a necessity proof from generic persistence.

However, evenness is not equivalent to the full prescribed exchange rule for an arbitrary fixed operator family. For example, assigning the identity to every label on E8 does not reproduce its nontrivial pairing exchange phases. An existential equivalence would also need construction of a suitable operator family. This wording should be made precise rather than calling the complete fixed-family hypothesis simply a restatement of evenness.

### The rank-two conclusion concerns a restricted comparison class

The minimum-rank discussion for a parity-corrected nontrivial algebra concerns positivity, unimodularity and that algebraic nontriviality condition. It is not a selection theorem for every constraint in Paper I, including its sector and clock model. The rank-eight alternatives in `IntrinsicConstraints.lean` provide separate, stronger tests of the actual clock and rank requirements.

## What is physically missing now

Orthogonal exchange locality is not the same as ordinary causal separation. The equation B(x,y)=0 is metric orthogonality in a configuration-cost pairing. It need not mean disjoint support or absence of a shared physical update mechanism. For example, (1,1) and (1,-1) have zero Euclidean pairing while both use both coordinate positions. A physical derivation must connect this particular pairing to interaction channels or independent operator factors.

The existing cost-additivity discussion does not supply that connection. Additive costs do not automatically imply independent state factors or commuting operators. Thus the argument "zero pairing means no channel" is an additional physical identification until derived from a state/update/probe model.

A Toll argument also needs care: a zero cross term B(x,y) implies additive quadratic costs, not zero total cost for the four operations in a commutator loop. Those operations can each incur a positive toll. Order dependence with zero cross cost is therefore not automatically a free interaction or a violation of the Toll requirement.

Nontrivial exchange is also independent of generic causality. An autonomous reversible clock can have a positive tick and nontrivial evolution while its update powers commute. Causal ordering alone does not prove a nonzero exchange form in the chosen operator sector.

The theorem therefore provides a useful sufficient constraint package with no E8 value built into its statement. Its physical necessity remains the new research task. Unimodularity/readout alignment, the constitutive impedance law and electromagnetic matching remain separately unresolved.

## Follow-up assignment

`Claude-followup-orthogonal-locality.md` focuses the next independent investigation on the physical meaning of orthogonality and the nontriviality requirement, without duplicating the Lean work.

## Verification

The new module compiled successfully (3961 jobs). The strict module-aware
axiom audit passed for all 19 declarations, including generated helpers and
transitive dependencies. Only propext, Classical.choice and Quot.sound were
permitted; no physical axioms or admitted proofs were introduced.

The complete PMArch integration build also passed (9008 jobs). Existing
manuscript content and experimental inputs were preserved.
