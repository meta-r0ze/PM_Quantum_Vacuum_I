import ELEM.Defs
import Mathlib.NumberTheory.Chebyshev

/-!
# ELEM.Hypotheses: the fixed statements each step proves

Each `def … : Prop` below is the exact statement one step of the proof delivers (as `theorem … : ELEM.<Name>`).
`ELEM.Glue` proves the challenge statement from these propositions, taken as explicit arguments, so
every step proves its piece against a fixed target. Equation numbers are those of the elementary
companion (twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae).

| statement        | companion            | proved in |
|------------------|----------------------|-----------|
| `LemmaTwoA`      | Lemma 2, `A(m)`      | `ELEM.Primes.LemmaTwo` |
| `LemmaTwoTheta`  | Lemma 2, `θ(x)`      | `ELEM.Primes.LemmaTwo` |
| `LemmaTwoB`      | Lemma 2, `B`         | `ELEM.Primes.LemmaTwo` |
| `SplitBound`     | (8)                  | `ELEM.Count.SplitBound` |
| `AuxPrime`       | Lemma 3, (9)         | `ELEM.Count.AuxPrime` |
| `Nonvanishing`   | section 4.1          | `ELEM.Nonvanishing.Main` |
| `SizeBound`      | (11), Leibniz form   | `ELEM.Size.Bound` |
| `DivisibilityBound` | (14)              | `ELEM.Divisibility.Main` |
| `Endpoint`       | (15)-(17)            | `ELEM.Endpoint.Comparison` |
| `Sieve`          | section 6            | `ELEM.Sieve.Main` |

`AnalyticSetting q` collects what `ELEM.Glue` derives from `classNumber K = 1` and `q = |disc K| ≥
2^15` (via CN-1's witness lemma): `q` is a prime `≡ 3 (mod 8)`, every prime `p < q/4` is inert, and
every non-inert prime is a value of the norm form `a² + ab + c b²`. The analytic steps may use all of
it, and nothing about the field `K`.
-/

set_option autoImplicit false

open Real

namespace ELEM

/-- **The standing hypotheses of the analytic part**, for `q = |disc K|` and `c = cq q = (q+1)/4`
(companion (1) and section 1). `ELEM.Glue` proves `AnalyticSetting q` from
`classNumber K = 1` and `2^15 ≤ q`. -/
structure AnalyticSetting (q : ℕ) : Prop where
  /-- `q ≥ q₀ = 2^15` -/
  large : 32768 ≤ q
  /-- `q` is prime -/
  prime : q.Prime
  /-- `q ≡ 3 (mod 8)` (so `2` is inert) -/
  mod_eight : q % 8 = 3
  /-- (1): every prime `p < q/4` is inert -/
  inert_of_lt : ∀ p : ℕ, p.Prime → 4 * p < q → IsInert (cq q) p
  /-- `h = 1`: every non-inert prime (split, or `q` itself) is a norm `a² + ab + c b²` -/
  rep : ∀ p : ℕ, p.Prime → ¬ IsInert (cq q) p →
    ∃ a b : ℤ, a ^ 2 + a * b + (cq q : ℤ) * b ^ 2 = p

/-! ## Lemma 2 -/

/-- **Lemma 2, `A(m)`.** `log m - 7/3 < A(m) < log m + 3/2` for integers `m ≥ 2`. -/
def LemmaTwoA : Prop :=
  ∀ m : ℕ, 2 ≤ m → Real.log m - 7 / 3 < A m ∧ A m < Real.log m + 3 / 2

/-- **Lemma 2, `θ(x)`.** `θ(x) < (3/2) x` for `x ≥ 1` (Mathlib's `Chebyshev.theta`). -/
def LemmaTwoTheta : Prop :=
  ∀ x : ℝ, 1 ≤ x → Chebyshev.theta x < 3 / 2 * x

/-- **Lemma 2, `B`.** The series `∑_p log p / p²` converges and `B < 2/3`. (Summability is part of
the statement: a `tsum` of a non-summable family is `0`.) -/
def LemmaTwoB : Prop :=
  Summable (fun p : Nat.Primes => Real.log (p : ℕ) / ((p : ℕ) : ℝ) ^ 2) ∧ B < 2 / 3

/-! ## The split-prime bound and the auxiliary inert prime -/

/-- **(8).** `S₊(X) ≤ (4/(5√q)) (log X)² + 4 (log q + 1)/q` for `X ≥ q/4`. -/
def SplitBound : Prop :=
  ∀ q : ℕ, AnalyticSetting q → ∀ X : ℝ, (q : ℝ) / 4 ≤ X →
    Splus q X ≤ 4 / (5 * √(q : ℝ)) * Real.log X ^ 2 + 4 * (Real.log q + 1) / q

/-- **Lemma 3.** There is an inert prime `R` with `q⁴ < R ≤ q⁵`. -/
def AuxPrime : Prop :=
  ∀ q : ℕ, AnalyticSetting q → ∃ R : ℕ, R.Prime ∧ IsInert (cq q) R ∧ q ^ 4 < R ∧ R ≤ q ^ 5

/-! ## The derivative determinant

All three take the same premises: the analytic setting for `q` and an inert prime `R` with
`q⁴ < R ≤ q⁵` (the output of `AuxPrime`). -/

/-- **Section 4.1 (van Dijk's auxiliary-prime nonvanishing).** Some `N × N` minor of `M q R` is
nonzero. -/
def Nonvanishing : Prop :=
  ∀ q R : ℕ, AnalyticSetting q → R.Prime → IsInert (cq q) R → q ^ 4 < R → R ≤ q ^ 5 →
    ∃ f : Row R → Col q R, minor q R f ≠ 0

/-- **(11), in the Leibniz form.** For every nonzero `N × N` minor `D₀`,
`log Δ / (R² S) ≤ (9/16) log R + (25/96) log q + (25/24) log 2 + 6 (log R)/R`, `Δ = N(D₀)`.
(The companion's Hadamard step gives `4 (log R)/R`; `Matrix.det_le`'s `N!` costs a further
`(log N)/R ≤ 2 (log R)/R`.) -/
def SizeBound : Prop :=
  ∀ q R : ℕ, AnalyticSetting q → R.Prime → IsInert (cq q) R → q ^ 4 < R → R ≤ q ^ 5 →
    ∀ f : Row R → Col q R, minor q R f ≠ 0 →
      Real.log (Delta q R f) / ((R : ℝ) ^ 2 * Sof R) ≤
        9 / 16 * Real.log R + 25 / 96 * Real.log q + 25 / 24 * Real.log 2 + 6 * Real.log R / R

/-- **(14) (Green's Frobenius divisibility, summed over the inert primes `p ≤ R`).** For every
nonzero `N × N` minor, `log Δ / (R² S) ≥ I - I/(2S) - 79/18`, `I = Iinert q R`. -/
def DivisibilityBound : Prop :=
  ∀ q R : ℕ, AnalyticSetting q → R.Prime → IsInert (cq q) R → q ^ 4 < R → R ≤ q ^ 5 →
    ∀ f : Row R → Col q R, minor q R f ≠ 0 →
      Iinert q R - Iinert q R / (2 * Sof R) - 79 / 18 ≤
        Real.log (Delta q R f) / ((R : ℝ) ^ 2 * Sof R)

/-! ## The endpoint comparison (pure real arithmetic) -/

/-- **(15)-(17).** The real-number contradiction. Variables: `q`, the auxiliary prime `R`,
`S = ⌊R/12⌋`, `A = A(R)`, `I = Iinert`, `Sp = S₊(R)`, `Y = log Δ / (R² S)`. The hypotheses are, in
order: `q ≥ 2^15`; `q⁴ < R ≤ q⁵`; `S ≥ R/13 > 0`; `Sp ≥ 0`; the decomposition
`A = I + S₊ + (log q)/q` (only `q` ramifies); Lemma 2 at `R`; (8) at `X = R`; `SizeBound`;
`DivisibilityBound`. -/
def Endpoint : Prop :=
  ∀ q R S A I Sp Y : ℝ, 32768 ≤ q → q ^ 4 < R → R ≤ q ^ 5 → R / 13 ≤ S → 0 < S → 0 ≤ Sp →
    A = I + Sp + Real.log q / q →
    Real.log R - 7 / 3 < A → A < Real.log R + 3 / 2 →
    Sp ≤ 4 / (5 * √q) * Real.log R ^ 2 + 4 * (Real.log q + 1) / q →
    Y ≤ 9 / 16 * Real.log R + 25 / 96 * Real.log q + 25 / 24 * Real.log 2 + 6 * Real.log R / R →
    I - I / (2 * S) - 79 / 18 ≤ Y →
    False

/-! ## The residue sieve -/

/-- **The residue sieve (companion section 6).** Every `q = 8k + 3` with `8 < q < 2^15`
is one of `11, 19, 43, 67, 163`, or has a prime `p ∈ {3, …, 31}` with `4p < q` and a root `y < p` of
`y² - y + (q+1)/4 ≡ 0 (mod p)` (written `y² + (p-1) y + (q+1)/4` to avoid truncated subtraction).
Decidable; `ELEM.Sieve.sieve` proves it by `decide +kernel` in chunks. -/
def Sieve : Prop :=
  ∀ k < 4096, 8 < 8 * k + 3 →
    8 * k + 3 ∈ ({11, 19, 43, 67, 163} : Finset ℕ) ∨
      ∃ p ∈ ([3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ), 4 * p < 8 * k + 3 ∧
        ∃ y < p, (y ^ 2 + (p - 1) * y + (8 * k + 3 + 1) / 4) % p = 0

end ELEM
