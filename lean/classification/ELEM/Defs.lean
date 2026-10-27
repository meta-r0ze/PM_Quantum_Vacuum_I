import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# ELEM.Defs: the shared objects of the ELEM development

The source argument is the elementary companion
(twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae), which assembles Green's
derivative determinant (Lemma 5.1 of hexagon 2610.00311v2), van Dijk's auxiliary-prime nonvanishing
(hexagon 2610.00409v1) and Pratt's norm counts. This file fixes, once for every step of the proof:

* the quadratic order `OK c = ℤ[ω]`, `ω² = ω - c`, as Mathlib's `QuadraticAlgebra ℤ (-c) 1`; for a
  discriminant `-q` with `q ≡ 3 (mod 4)` and `c = cq q = (q + 1)/4` this is the ring of integers of
  `ℚ(√-q)`; conjugation is Mathlib's `star` (`star ω = 1 - ω`), the norm is `QuadraticAlgebra.norm`;
* inertness `IsInert c p`: the polynomial `X² - X + c` has no root mod `p`, written in exactly the
  shape of Mathlib's `Field (QuadraticAlgebra K a b)` instance, so that `Fact (IsInert c p)` makes
  `Fp2 c p = 𝔽_p[ω]` a field (with `𝔽_p[ω] ≅ 𝔽_{p²}`);
* the sums over primes `A`, `Iinert`, `Splus` (Lemma 2, (8), (14) of the companion);
* the derivative-determinant matrix `M q R` of the companion's (10) and its square minors.

Nothing here is a hypothesis: these are definitions. The statements that the steps of the proof
prove are in `ELEM.Hypotheses`.
-/

set_option autoImplicit false

open QuadraticAlgebra

namespace ELEM

/-! ## The quadratic order and inertness -/

/-- `c = (q + 1)/4`, the constant term of `X² - X + c`, the minimal polynomial of
`ω = (1 + √-q)/2` for `q ≡ 3 (mod 4)`. -/
def cq (q : ℕ) : ℕ := (q + 1) / 4

/-- The quadratic order `ℤ[ω]` with `ω² = -c + 1·ω`, i.e. `ω² = ω - c`. The element `⟨x, y⟩` is
`x + y ω`; `star ⟨x, y⟩ = ⟨x + y, -y⟩` is `x + y (1 - ω)`. -/
abbrev OK (c : ℕ) : Type := QuadraticAlgebra ℤ (-(c : ℤ)) 1

/-- The same algebra over `ZMod p`: `𝔽_p[ω]`, `ω² = ω - c`. A field when `IsInert c p`. -/
abbrev Fp2 (c p : ℕ) : Type := QuadraticAlgebra (ZMod p) (-(c : ZMod p)) 1

/-- **Inertness.** `X² - X + c` has no root mod `p` (stated as `r² ≠ -c + 1·r`, the shape of the
hypothesis of Mathlib's `Field (QuadraticAlgebra K a b)` instance). For a prime `p` and
`c = cq q`, this says that `p` is inert in `ℚ(√-q)`; `p = 2` is included (inert iff `c` is odd). -/
def IsInert (c p : ℕ) : Prop := ∀ r : ZMod p, r ^ 2 ≠ -(c : ZMod p) + 1 * r

instance instFactField {c p : ℕ} [h : Fact (IsInert c p)] :
    Fact (∀ r : ZMod p, r ^ 2 ≠ -(c : ZMod p) + 1 * r) := h

/-- With `Fact p.Prime` and `Fact (IsInert c p)`, `𝔽_p[ω]` is a field (Mathlib's instance). -/
example {c p : ℕ} [Fact p.Prime] [Fact (IsInert c p)] : Field (Fp2 c p) := inferInstance

/-- **Split** (for the discriminant `-q`, `c = cq q`): `p` is not inert and `p ≠ q`. For prime `q`
the primes that are neither inert nor split are exactly `q` itself (ramified). -/
def IsSplit (q p : ℕ) : Prop := ¬ IsInert (cq q) p ∧ p ≠ q

/-! ## The sums over primes

All three are sums of `log p / p` over primes `p ≤ x`, in Mathlib's `Nat.primesLE x`
(`primesLE x = {p ∈ range (x + 1) | p.Prime}`, the set behind `Chebyshev.theta_eq_sum_primesLE`).
The filters by `IsInert` / `IsSplit` use classical decidability. -/

/-- `A(x) = ∑_{p ≤ x} log p / p` (companion, Lemma 2). -/
noncomputable def A (x : ℕ) : ℝ := ∑ p ∈ Nat.primesLE x, Real.log p / p

open Classical in
/-- `I = ∑_{p ≤ x, p inert} log p / p` (companion, (14)), for `c = cq q`. -/
noncomputable def Iinert (q x : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE x).filter (fun p => IsInert (cq q) p), Real.log p / p

open Classical in
/-- `S₊(X) = ∑_{p ≤ X, p split} log p / p` (companion, (8)), for real `X`. -/
noncomputable def Splus (q : ℕ) (X : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p => IsSplit q p), Real.log p / p

/-- `B = ∑_p log p / p²` (companion, Lemma 2), as a `tsum` over the primes. -/
noncomputable def B : ℝ := ∑' p : Nat.Primes, Real.log (p : ℕ) / ((p : ℕ) : ℝ) ^ 2

/-! ## The derivative-determinant matrix (companion, (10))

Parameters, for the discriminant `-q` and the auxiliary prime `R`:
`S = ⌊R/12⌋`, `J = ⌈R/48⌉`, `N = R S`, `A₀ = ⌈√(R √q)⌉`, `B₀ = ⌈√(R / √q)⌉`.
Rows are `(r, s)`, `0 ≤ r < R`, `0 ≤ s < S`; columns are `(z, k)`, `z = a + b ω` a node with
`|a| ≤ A₀`, `|b| ≤ B₀`, and `0 ≤ k < J`. The entry is `∂_z^k (z^r w^s)` at `(z, z̄)`, i.e.
`(r)_k z^{r-k} z̄^s` with `(r)_k = r (r-1) ⋯ (r-k+1)` the falling factorial (`Nat.descFactorial`,
which is `0` for `k > r`, so the truncated `r - k` is harmless). -/

/-- `S = ⌊R/12⌋`. -/
def Sof (R : ℕ) : ℕ := R / 12

/-- `J = ⌈R/48⌉`. -/
def Jof (R : ℕ) : ℕ := (R + 47) / 48

/-- `A₀ = ⌈√(R √q)⌉`. -/
noncomputable def A0 (q R : ℕ) : ℕ := ⌈Real.sqrt (R * Real.sqrt q)⌉₊

/-- `B₀ = ⌈√(R / √q)⌉`. -/
noncomputable def B0 (q R : ℕ) : ℕ := ⌈Real.sqrt (R / Real.sqrt q)⌉₊

/-- The row index `(r, s)`, `r < R`, `s < S`. `card = R S = N`. -/
abbrev Row (R : ℕ) : Type := Fin R × Fin (Sof R)

/-- The node index `(i, j)`, standing for `a = i - A₀`, `b = j - B₀`. -/
abbrev Node (q R : ℕ) : Type := Fin (2 * A0 q R + 1) × Fin (2 * B0 q R + 1)

/-- The column index `(node, k)`, `k < J`. -/
abbrev Col (q R : ℕ) : Type := Node q R × Fin (Jof R)

/-- The node `z = a + b ω ∈ OK (cq q)` with `a = i - A₀`, `b = j - B₀`. -/
noncomputable def node (q R : ℕ) (n : Node q R) : OK (cq q) :=
  ⟨(n.1 : ℤ) - A0 q R, (n.2 : ℤ) - B0 q R⟩

/-- **The derivative-determinant matrix** `M q R`, an `N × (n J)` matrix over `OK (cq q)`:
`M ((r, s), (z, k)) = (r)_k z^{r-k} z̄^s`. -/
noncomputable def M (q R : ℕ) : Matrix (Row R) (Col q R) (OK (cq q)) :=
  fun rs zk =>
    ((rs.1 : ℕ).descFactorial (zk.2 : ℕ) : OK (cq q)) * node q R zk.1 ^ ((rs.1 : ℕ) - zk.2) *
      star (node q R zk.1) ^ (rs.2 : ℕ)

/-- The square minor `D₀ = det M[·, f]` for a choice `f` of `N` columns (indexed by the rows). -/
noncomputable def minor (q R : ℕ) (f : Row R → Col q R) : OK (cq q) :=
  ((M q R).submatrix id f).det

/-- `Δ = D₀ D̄₀ = N(D₀) ∈ ℤ`, as a real number. -/
noncomputable def Delta (q R : ℕ) (f : Row R → Col q R) : ℝ :=
  ((QuadraticAlgebra.norm (minor q R f) : ℤ) : ℝ)

end ELEM
