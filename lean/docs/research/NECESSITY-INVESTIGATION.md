# Testing the physical necessity of orthogonal exchange locality

## Result

The proposed arguments from Protocol, Toll and Causality do not establish orthogonal exchange locality or nontrivial exchange by themselves. There is a valid sufficient mechanism for commutation—updates on independent state factors—but linking configuration-metric orthogonality to that factorization is still extra physical content.

This investigation adds explicit reversible operational protocols, a faithful integer-label operator family, a finite-history bound, and a consistency check against the Clifford algebra in Paper II. These are not alternative quantum-vacuum theories or an axiomatization of every PM requirement. They test particular proposed implications without adding a physical postulate chosen to force E8.

## 1. What Protocol can establish

`separate_factors_commute` proves that updates of the form

    (s,t) -> (f(s),t),    (s,t) -> (s,g(t))

commute. This is a genuine route from independent physical state factors to compatible operations.

To use it for the E8 selection theorem, one must additionally establish that B(x,y)=0 gives such a factorization for the relevant physical operators. Orthogonality of a cost pairing is not that factorization. The example (1,1), (1,-1) has zero Euclidean pairing while sharing both coordinate positions.

The stronger interpretation of B as a nonnegative count of shared channels is also unavailable for an arbitrary signed lattice: `nonnegative_cross_pairing_trivial` proves that a bilinear B nonnegative for every x,y must be zero, because B(x,-y)=-B(x,y). This does not disprove orthogonal locality. It rules out that simple nonnegative-channel-count derivation. A signed effective coupling may have other properties, but its connection to operator order must be derived.

## 2. Toll does not imply commuting orthogonal labels

The primitive label directions e1,e2 have the identity Gram pairing:

    B(e1,e2)=0, Q(e1)=Q(e2)=1, Q(e1+e2)=2.

The new finite protocol has three binary state components (a,x,y), and reversible operations

    X(a,x,y) = (a,x+1,y),
    Y(a,x,y) = (a+x,x,y+1),
    E(a,x,y) = (a+1,x,y),

with arithmetic modulo two. Lean checks that E is nontrivial and central relative to X,Y, that X Y = E Y X, and that the commutator loop equals E. All state components are retained, so these are permutations rather than lossy observations.

Each of the four loop operations can be assigned the same positive action/time toll c. `loop_positive_action` gives total action 4c>0. Thus the order-dependent effect is not free even though the two label directions have zero quadratic cross term. Equating zero cross cost with zero total loop action would be incorrect.

The positive bill here is per-operation time/action accounting. The example does not assert irreversible heat expenditure from a finite energy reserve for infinitely many cycles. It also does not identify label cost with a Hamiltonian conserved by each gate.

## 3. The protocol can be autonomous and finite

A four-state internal clock selects the fixed sequence X,Y,X^-1,Y^-1. `controlled` constructs an explicitly reversible autonomous update; its inverse recovers both the previous clock state and the previous data state.

The joint controller/register space has 32 states. `autonomous_period_eight` checks that every state returns after eight updates; `autonomous_nonstatic` checks nontrivial evolution. `all_histories_reconstruct` proves that initial-state distinctions remain recoverable at every specified elapsed time. Applying the same rule pointwise at every spatial site commutes with site relabelings, as checked by `pointwise_protocol_homogeneous`.

This makes the operational scope explicit: finite capacity, internal control, ordered updates and lossless state evolution can coexist with noncommuting operations whose assigned label directions are geometrically orthogonal. The example does not implement the entire E8 paper's sector, clock and quantum-field requirements; it shows that the generic Protocol/Toll argument is insufficient.

## 4. Faithful integer labels are possible too

The earlier Pauli example repeated across integer labels. `integerMove` instead acts on (a,s,t) in Z/2 x Z x Z:

    U_(p,q)(a,s,t) = (a+q s mod 2, p+s, q+t).

Its inverse is explicit. Evaluating at the origin recovers p,q, so `integer_move_faithful` proves that distinct integer labels give distinct operators. `integer_exchange` checks the noncommuting primitive pair, and `integer_phase_nontrivial` checks the central phase operation is not identity.

This is a faithful algebraic operator example on a larger state space, separate from the finite register model. It is not a proof of a full Weyl representation, a Hamiltonian, or conservation of the proposed label energy under every operation. Those were not inferred from invertibility.

## 5. Causality does not force nontrivial exchange

`causal_clock_commuting` gives a nonidentity 43-slot reversible clock whose update powers all commute. One can assign a positive tick duration and per-step action without producing an order-dependent binary exchange form.

A well-defined causal evolution is therefore different from the assertion that some selected pairs of operations have nontrivial exchange. The latter needs a property of the particular vacuum dynamics, not just the existence of clock ticks.

Trying to force exchange through reconstruction of every possible operation history introduces a stronger requirement. `finite_history_capacity` proves that an injective encoding of all n-bit control histories in a state space S requires 2^n <= |S|. `no_unbounded_history_memory` proves that a fixed finite state space cannot retain every such history for unbounded n.

This does not conflict with reversible autonomous evolution. For a fixed update, fixed elapsed time and full state observation, preserving initial distinctions does not require retaining arbitrary external control histories. Demanding all histories as a route to nontrivial exchange would need extra memory or a different observation model.

## 6. A consistency check inside the existing papers

Paper II, `paper/4_cap_map_dirac.tex`, equation `eq:anti_commute`, requires

    Gamma_mu Gamma_nu + Gamma_nu Gamma_mu = 2 eta_mu_nu I.

Distinct orthogonal spatial directions therefore anticommute. `orthogonal_clifford_certificate` checks the corresponding exact two-generator algebra using the integer matrices

    X = [[0,1],[1,0]],    Z = [[1,0],[0,-1]].

Their squares and transpose-products are identity, but XZ=-ZX and XZ!=ZX.

Consequently, a universal rule that all orthogonal vacuum operations commute would conflict with this Clifford operator role. There is no immediate contradiction if lattice exchange operators and spinor direction generators are different operator families with different relevant pairings. That distinction, and the map between them, must be stated and constructed.

In particular, one cannot use Clifford anticommutation to establish nontrivial exchange for the evenness theorem while imposing its orthogonal-locality hypothesis on those same generators. Nontriviality must be established in the correct operator sector.

## What this means for the intended derivation

The evenness criterion in `OrthogonalExchange.lean` remains valid. The present work does not establish its physical necessity. It identifies precisely why the attempted arguments fail:

- Cost orthogonality does not establish separation of physical state factors.
- Zero cross cost does not make a commutator loop cost-free.
- A nontrivial clock does not imply a nontrivial exchange form.
- Reconstructing initial states does not require encoding every control history.
- The existing Clifford algebra cannot be used indiscriminately as the same exchange algebra.

The next substantive construction must specify the physical lattice operators, their update supports, the meaning of B, and their actual commutators. A derivation of factorization for B-orthogonal labels, together with nontrivial exchange in that same sector, would activate the existing Lean evenness theorem. Without that vacuum-specific structure, the tested PM accounting and causal requirements do not supply those premises.

No new physical requirement has been adopted here simply because it would select E8. The persistence-only E8 and inverse-fine-structure claim remains unproved; readout alignment, rank selection, the six-term cost law and electromagnetic matching retain their separate obligations.

## Verification

The new module compiled successfully (3962 jobs). Its strict module-aware
axiom audit passed for all 49 declarations, including generated helpers and
transitive dependencies. Only propext, Classical.choice and Quot.sound were
allowed. No physical axioms or admitted proofs were introduced.

The complete PMArch integration build passed as well (9009 jobs). Existing
manuscript content and experimental inputs were preserved.
