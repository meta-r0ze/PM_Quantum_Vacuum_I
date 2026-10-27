import ELEM.Glue
import ELEM.Primes.LemmaTwo
import ELEM.Count
import ELEM.Nonvanishing.Main
import ELEM.Size.Bound
import ELEM.Divisibility.Main
import ELEM.Endpoint
import ELEM.Sieve.Main

/-!
# ELEM.Main: the class number one theorem, with no L-function, no zeta function and no zero-free
theorem in its closure

The Comparator solution for the challenge `CN1Challenges.ClassNumberOne` (md5 c162eee6). The
statement below is the challenge's, byte for byte (docstring included); only the proof differs.
It is `ELEM.classNumber_eq_one_iff_of_hyps` (ELEM.Glue) applied to the eight proved
theorems of the steps: `lemmaTwoA` (Lemma 2), `splitBound` ((8)) and `auxPrime` (Lemma 3),
`nonvanishing` (van Dijk), `sizeBound` ((11), Leibniz form), `divisibilityBound` ((14)),
`endpoint` ((15)-(17)) and `sieve` (the residue sieve below 2^15).

The argument is the elementary companion of twinheterodox/tenth-discriminant
(companions/elementary/proof.tex, commit 64694aae), building on Green and van Dijk; this module
formalizes it in our own words and code.
-/

open NumberField

namespace CN1

/-- **Class number one for imaginary quadratic fields.** Let `K` be a number field of degree two
over `ℚ` containing a square root of `-m`, where `m` is a squarefree natural number (so `m ≥ 1`
and `K ≅ ℚ(√-m)`). Then the class number of `K` is one if and only if
`m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}`. The set is written out so that the statement's constant
closure is Mathlib's alone (Comparator compares every constant the statement uses). -/
theorem classNumber_eq_one_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ) :=
  ELEM.classNumber_eq_one_iff_of_hyps ELEM.Primes.lemmaTwoA ELEM.Count.splitBound
    ELEM.Count.auxPrime ELEM.nonvanishing ELEM.Size.sizeBound ELEM.divisibilityBound ELEM.Endpoint.endpoint
    ELEM.Sieve.sieve K hK m hm hsq

end CN1
