# Lattice class, state-sum symmetries, and rank selection

## Result of this attempt

There is now a constructive conditional route to an integral positive-definite Gram model, and an explicit asymptotic rank-selection mechanism. The required period-one theta symmetry and self-dual inversion symmetry still do not follow from the stated operational persistence conditions. Lean contains counterexamples showing why those implications cannot simply be asserted.

This does not close the full persistence-to-E8 claim. It distinguishes mathematical results from the structural and dynamical requirements still needing independent justification.

## 1. Constructing the lattice representation

`integer_coordinates` proves that a finitely generated, torsion-free additive abelian address group has integer coordinates: it is isomorphic to Z^n for some finite n. The rank is not specified to be eight.

`integer_gram_representation` then proves that an integer-valued symmetric bilinear cost on that address group has an integral symmetric Gram matrix in those coordinates. `finite_budget_gram` proves that finiteness of every quadratic-cost sublevel set forces the real Gram matrix to be positive definite.

This removes an assumed Gram matrix from the start of that conditional construction. It uses general algebraic constraints rather than an E8 matrix or a target decimal. However, the following are still extra structural assumptions:

- Translations compose as an abelian group, rather than a semigroup or a noncommutative group.
- They have finitely many generators and no torsion. Finite generation means finitely many generators, not finitely many addresses.
- Configuration cost comes from an integer-valued symmetric bilinear pairing.
- Every bounded-cost set of configurations is finite.

Generic bounded resources, preserved identity and causal ordering do not imply all these assumptions. A finite model description is not a proof of finite generation. Integer address labels alone do not make an arbitrary real-valued pairing integral. A Gram representation also does not identify its configuration cost with physical excitation energy or construct the physical spacetime embedding.

## 2. State-sum symmetries: explicit obstructions

The required laws are symmetries of a complex statistical generating function. They are not the statement that chronological time evolution is reversible.

The new `natural_theta_period_two` theorem records that integral quadratic lattices already have the period-two theta transformation. The period-one law used in E8 selection is stronger.

Two new counterexample theorems combine earlier independent lattice witnesses with finite-cost and conservation results:

- `finite_conserved_model_without_T`: a positive unimodular rank-one integral lattice has finite cost sublevels and an invertible cost-preserving reflection update, yet fails the period-one theta law. The existing equivalence between evenness and that law proves the failure exactly, without numerically approximating a theta sum.
- `finite_even_conserved_model_without_S`: the rank-one A1 lattice is positive and even, with finite cost sublevels and the same reversible cost-preserving update, yet fails the self-dual inversion law. Evenness supplies the period-one law, but it does not supply self-duality.

Reflection is nontrivial on a specified nonzero vector. Its inverse is itself; its updates conserve the quadratic cost exactly. A positive duration can be assigned to each discrete step without affecting either example. These are operational mathematical counterexamples, not constructed competing quantum vacua.

Consequently, finiteness of bounded-cost sets plus reversible cost conservation cannot force the two E8 state-sum symmetries, even when an integral lattice is already supplied. An additional physical requirement must exclude these examples. Stating Fourier self-duality or phase-period identification directly remains an extra constraint unless its necessity is independently derived.

## 3. Deriving rank preference from operational cost

`minimal_rank_iff_eight` proves the exact minimum-rank characterization within the nonzero positive even unimodular class. The earlier E8 plus E8 example shows why the class alone does not enforce this minimum.

A concrete workload model supplies a possible selection mechanism:

- Every independent coordinate is refreshed at the same flux f.
- Each refresh costs the same positive toll c.
- Compared candidates share those c and f, a failure-hazard coefficient beta>0, and fixed positive prior odds.

The new `refresh_cost_exact` and `refresh_cost_strict` theorems give

    s_n = c f n.

`refresh_survival_ratio` derives the relative survival factor directly from those costs. Including prior odds r, the higher-rank relative weight is

    R_nm(T) = r exp[- beta c f (n-m) T].

For n>m, `higher_rank_odds_tend_to_zero` proves R_nm(T)->0, and `lower_rank_share_tends_to_one` proves that the lower-rank share of the two-candidate surviving ensemble tends to one. `rank_odds_positive` proves that a higher-rank candidate retains positive weight at every finite time when its prior odds are positive.

This derives an asymptotic preference without postulating a rank-eight value. For the even unimodular class, comparison with an available rank-eight candidate favors E8. The formal new limit theorem is pairwise; extending it to a whole ensemble requires an available minimum-rank candidate with positive prior weight and control of the total competing weight. A finite family permits the usual finite-sum argument. An infinite family needs an appropriate summability or uniform bound. This is selection conditional on survival, not guaranteed survival of the selected candidate or a model of transitions between different substrates.

`least_cost_implies_minimal_rank` also proves the deterministic implication from globally least cost to minimum rank when cost is a strictly increasing function of rank alone.

The physical obligation is now precise: justify the full-refresh workload and common comparison conditions. A higher-dimensional model could refresh less often or have different tolls or protection. `higher_rank_not_excluded_by_survival` checks that the exponential survival law can instead favor a higher-rank candidate when it has lower assigned cost. Persistence alone does not supply monotone rank cost.

## What remains before claiming E8 is forced

We need independent vacuum arguments for the additive/integral cost structure, the phase and duality requirements, and the workload/hazard comparison. Merely renaming evenness as phase periodicity, self-duality as Fourier consistency, or rank minimization as lowest cost does not derive these requirements. The new results expose exactly what such arguments must establish and which counterexamples they must exclude.

The six-term impedance law and electromagnetic matching remain separate, unchanged obligations. Nothing in this update selects their numerical normalizations.

## Source and checking

The new source is `PMArch/ConstraintFoundations.lean`. `AuditFoundations.lean` checks every declaration from that module, including generated declarations, and their transitive axiom dependencies; only propext, Classical.choice and Quot.sound are permitted. No physical axioms are introduced.

The new module compiled successfully. Its strict scoped audit passed for all
25 declarations, including generated declarations and transitive dependencies.
The complete earlier 705-declaration audit is recorded in CLAIM-AUDIT.md; this
update uses a focused transitive audit for the added module.

The full PMArch library integration build also passed (9005 jobs). No
existing manuscript content or experimental inputs were changed.
